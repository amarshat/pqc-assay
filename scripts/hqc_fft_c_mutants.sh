#!/usr/bin/env bash
# Source-level mutants of the additive-FFT reference C (a measurement, out of band; it never gates the
# build). Each mutant is a one-line change to a copy of one file of target/hqc-fft/gf264_ref (target/ is
# never edited), compiled with the rest as make hqc-fft compiles it (decode_64 repaired), and the
# unchanged hqc-1 script that proves the mutated routine is run against it. Caught: saw exits non-zero.
# A run that reaches LIMIT seconds (default 1800) is "no result", not caught. A run that exits non-zero
# without a failed proof outside a `fails` block (a crash, a kill) is "died", not caught: the verdict
# reads the log, not only the exit code.
# Usage: scripts/hqc_fft_c_mutants.sh [mutant-name]   (needs AVX_CLANG's llvm-link, see Makefile)
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"; export PATH="$ROOT/.tools/bin:$PATH"
WHICH="${1:-all}"; LIMIT="${LIMIT:-1800}"; MEMLIMIT_GB="${MEMLIMIT_GB:-36}"
AVX_CLANG="${AVX_CLANG:-/opt/homebrew/opt/llvm@22/bin/clang}"; LLVM="$(dirname "$AVX_CLANG")"
SRC=target/hqc-fft/gf264_ref; FILES=$(sed -n 's/^FFT_C *:= //p' Makefile)
M="$ROOT/build/hqc-fft/cmut"; [ "$WHICH" = all ] && rm -rf "$M"; mkdir -p "$M"
make -s build/hqc-fft/src/dencoder.c >/dev/null
printf '%-16s %-14s %-9s %-7s %s\n' mutant file verdict seconds "last failure reported by saw"

run_mutant() {  # name file sed-expression script [sed-expression on the proof script]
  local name=$1 file=$2 expr=$3 script=$4 sexpr="${5:-}" d="$M/${1//\//_}" objs="" f s
  [ "$WHICH" = all ] || [ "$WHICH" = "$name" ] || [ "${name%/*}" = "$WHICH" ] || return 0
  mkdir -p "$d/src" "$d/build/hqc-fft" "$d/proof/hqc-fft"
  s=$SRC/$file; [ "$file" = dencoder.c ] && s=build/hqc-fft/src/dencoder.c
  sed -e "$expr" "$s" > "$d/src/$file"
  if [ -z "$expr" ]; then :   # a /ctl row: the C unchanged
  elif cmp -s "$s" "$d/src/$file"; then printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" ERROR - "mutation did not apply"; return; fi
  [ -z "$expr" ] || [ "$(diff "$s" "$d/src/$file" | grep -c '^<')" = 1 ] || { printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" ERROR - "mutation touched more than one line"; return; }
  for f in $FILES; do
    s=$SRC/$f.c; [ $f = dencoder ] && s=build/hqc-fft/src/dencoder.c; [ "$f.c" = "$file" ] && s=$d/src/$file
    "$AVX_CLANG" -O0 -std=c11 -I $SRC -c -emit-llvm -o "$d/build/hqc-fft/$f.bc" "$s" || return; objs="$objs $d/build/hqc-fft/$f.bc"
  done
  "$LLVM/llvm-link" -o "$d/build/hqc-fft/fft_ref.bc" $objs || return
  cp proof/hqc-fft/*.saw "$d/proof/hqc-fft/"
  if [ -n "$sexpr" ]; then sed -i.orig -e "$sexpr" "$d/proof/hqc-fft/$script.saw"
    cmp -s "$d/proof/hqc-fft/$script.saw" "$d/proof/hqc-fft/$script.saw.orig" && { printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" ERROR - "script edit did not apply"; return; }; fi
  local start pid timed_out=0 mem_out=0 peak=0 r; start=$(date +%s)
  (cd "$d" && exec env CRYPTOLPATH="$ROOT/model/cryptol/hqc:$ROOT/model/cryptol/hqc-fft" saw "proof/hqc-fft/$script.saw" > saw.log 2>&1) &
  pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    if [ $(( $(date +%s) - start )) -ge "$LIMIT" ]; then timed_out=1; pkill -KILL -P "$pid" 2>/dev/null; kill -KILL "$pid" 2>/dev/null; break; fi
    r=$(ps -o rss= -p "$pid" 2>/dev/null | tr -d ' '); [ -n "$r" ] && [ "$r" -gt "$peak" ] && peak=$r
    if [ "${r:-0}" -gt $((MEMLIMIT_GB * 1048576)) ]; then mem_out=1; pkill -KILL -P "$pid" 2>/dev/null; kill -KILL "$pid" 2>/dev/null; break; fi
    sleep 2
  done
  wait "$pid" 2>/dev/null; local rc=$? secs=$(( $(date +%s) - start )) why last_ant last_trace
  # an anticipated failure prints its header and then "Stack trace:"; a real failure prints a stack trace
  # with no header in front of it
  last_ant=$(grep -an '== Anticipated failure message ==' "$d/saw.log" | tail -1 | cut -d: -f1); last_ant=${last_ant:-0}
  last_trace=$(grep -an '^Stack trace:' "$d/saw.log" | tail -1 | cut -d: -f1); last_trace=${last_trace:-0}
  why=$(grep -aE 'Subgoal failed|Symbolic execution failed|error:' "$d/saw.log" | tail -1 | cut -c1-90)
  if [ $timed_out = 1 ]; then printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" "no result" "$secs" "limit $LIMIT s"
  elif [ $mem_out = 1 ]; then printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" "no result" "$secs" "memory limit $MEMLIMIT_GB GB"
  elif [ $rc -ne 0 ] && [ "$last_trace" -gt $((last_ant + 1)) ]; then printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" caught "$secs" "$why"
  elif [ $rc -ne 0 ]; then printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" died "$secs" "exit $rc with no failed proof in the log: $(tail -1 "$d/saw.log" | cut -c1-50)"
  elif [ -z "$expr" ]; then printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" "passes" "$secs" "control: saw exited 0 on the unchanged C"
  else printf '%-16s %-14s %-9s %-7s %s\n' "$name" "$file" MISSED "$secs" "saw exited 0 on a wrong program"; fi
}

# twiddle selection in the forward network: table entry k^1 instead of k. (A first choice, j<<2 for
# j<<1 in the Cantor offset, was accepted by saw: at the hqc-1 sizes step_size = num, so j is always 0
# and the mutant was the same program.)
run_mutant fft-twiddle btfy.c '59s/cantor_to_gf264_2x\[k\]^extra_a_j/cantor_to_gf264_2x[k^1]^extra_a_j/' ref_2
# basis conversion: layer 6 of the unrolled bc_256_16384 drops one quotient word from one remainder
# word. (A first choice, a shift in the generic cvt, was accepted by saw: cvt runs only for n_256 other
# than 64, 128 and 256, which no HQC length reaches in the forward direction, so that mutant was dead
# code and the program unchanged on every input the proofs cover.)
run_mutant fft-bc-layer bc_256_ref.c '133s/= q1^p1;/= q1;/' ref_4
# linear map indexing: row j^1 of the matrix instead of row j
run_mutant fft-linmap dencoder.c 's/&mat\[j\];/\&mat[j^1];/' ref_3
# Karatsuba cross terms of polymul_280U64_mul: one of the two products dropped
run_mutant fft-crossterm polymul_hqclen_ref.c '274s/tmp0\[j\] ^ tmp1\[j\]/tmp0[j]/' fft_1

# The rme-proved routines build a canonical form, which on a false goal ran out of memory (bc-layer,
# linmap, 2026-10-27), and z3 gave no result on the twiddle mutant in 1800 s. As for the HQC leaf
# (scripts/hqc_c_mutants.sh), each is run again with only the mutated routine's tactic swapped
# (row suffix /abc or /yices), so that a refutation, if there is one, is on record.
run_mutant fft-bc-layer/abc bc_256_ref.c '133s/= q1^p1;/= q1;/' ref_4 '/^b2 <- llvm_verify m "bc_256"/s/ rme;$/ abc;/'
run_mutant fft-linmap/abc dencoder.c 's/&mat\[j\];/\&mat[j^1];/' ref_3 '/^lin <- llvm_verify m "linear_map_x8"/s/ rme;$/ abc;/'
run_mutant fft-twiddle/yices btfy.c '59s/cantor_to_gf264_2x\[k\]^extra_a_j/cantor_to_gf264_2x[k^1]^extra_a_j/' ref_2 '/^bt <- llvm_verify m "btfy_64"/s/(w4_unint_z3 \["gf264"\]);$/(w4_unint_yices ["gf264"]);/'
# A false goal can be refuted on one input: the /concrete row fixes btfy_64's input to [1 .. 512] and
# interprets gf264, so the goal is a closed evaluation, and drops the rest of the script; /ctl runs the
# same script on the unchanged C and must pass, which shows the concrete script itself is sound.
CONCRETE_BT='/^bt <- llvm_verify m "btfy_64"/,$c\
bt <- llvm_verify m "btfy_64" bfs false (do { p <- llvm_alloc (w 512); llvm_points_to p (llvm_term {{ [1 .. 512] : [512][64] }}); llvm_execute_func [p, llvm_term {{ 9 : [32] }}, llvm_term {{ 1 << 41 : [64] }}]; llvm_points_to p (llvm_term {{ btfy9 (1 << 41) ([1 .. 512] : [512][64]) }}); }) (w4_unint_z3 []);'
run_mutant fft-twiddle/concrete btfy.c '59s/cantor_to_gf264_2x\[k\]^extra_a_j/cantor_to_gf264_2x[k^1]^extra_a_j/' ref_2 "$CONCRETE_BT"
run_mutant fft-twiddle/ctl btfy.c '' ref_2 "$CONCRETE_BT"
