#!/usr/bin/env bash
# Source-level mutants of the HQC C under proof: does the unchanged SAW script reject a wrong program?
#
# The gated mutants (make hqc, make hqc-avx) perturb the specification and must fail; they show the
# equality is checked. This script perturbs the C instead: each mutant is a one-line change to a copy
# of the vendored file (target/ is never edited), compiled exactly as the gated run compiles it, and
# the unchanged proof script for hqc-1 is run against it. A mutant counts as caught when saw exits
# non-zero. A measurement, out of band (make hqc-c-mutants); it never gates the build.
#
# Each run has a time limit (LIMIT, default 1200 s); a run that hits it is "no result", not caught.
# The leaf of karatsuba_1.saw is proved with rme, which builds a canonical form: it proves fast but
# gave no refutation of a wrong leaf in 1200 s (2026-10-24). The gated leaf mutant therefore uses abc,
# and the leaf C mutant here is run twice: with the unchanged script, and with the one leaf tactic
# swapped to abc (row suffix /abc), so that the refutation itself is on record.
#
# A mutant that z3 cannot refute symbolically can still be refuted on one concrete input: a universal
# claim fails as soon as one instance fails. Rows with the suffix /concrete replace the two fresh
# inputs of the obligation by fixed values in the proof script (and interpret the leaf, so that the
# whole goal evaluates); a matching /ctl row runs the same script against the unmodified C and must
# pass, which shows the concrete script itself is not broken. An empty sed expression means "no C
# change" and is only for /ctl rows.
#
# Usage: scripts/hqc_c_mutants.sh [ref|avx|all|<mutant-name>]   (default all; avx needs AVX_CLANG, see Makefile)
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"; export PATH="$ROOT/.tools/bin:$PATH"
WHICH="${1:-all}"; LIMIT="${LIMIT:-1200}"
AVX_CLANG="${AVX_CLANG:-/opt/homebrew/opt/llvm@22/bin/clang}"
M="$ROOT/build/hqc/cmut"; case "$WHICH" in ref|avx|all) rm -rf "$M";; esac; mkdir -p "$M"
printf '%-22s %-9s %-7s %s\n' mutant verdict seconds "last failure reported by saw"

run_mutant() {  # name  kind(ref|avx)  sed-expression  [sed-expression on the proof script]
  local name=$1 kind=$2 expr=$3 sexpr="${4:-}" d="$M/${1//\//_}" src dst bc script
  case "$WHICH" in ref|avx|all) ;; *) [ "$WHICH" = "$name" ] || [ "${name%/*}" = "$WHICH" ] || return 0;; esac
  mkdir -p "$d/proof/hqc" "$d/build/hqc"
  if [ "$kind" = ref ]; then src=target/hqc/gf2x.c; script=karatsuba_1.saw; else src=target/hqc/avx2/hqc-1/gf2x.c; script=avx_1.saw; fi
  dst="$d/gf2x.c"
  if [ -z "$expr" ]; then cp "$src" "$dst"; else
    sed -e "$expr" "$src" > "$dst"
    if cmp -s "$src" "$dst"; then printf '%-22s %-9s %-7s %s\n' "$name" ERROR - "mutation did not apply"; return; fi
    [ "$(diff "$src" "$dst" | grep -c '^<')" -le 1 ] || { printf '%-22s %-9s %-7s %s\n' "$name" ERROR - "mutation touched more than one line"; return; }
  fi
  if [ "$kind" = ref ]; then
    clang -c -emit-llvm -O0 -g -I target/hqc/hqc-1 -I target/hqc -o "$d/build/hqc/gf2x_1.bc" "$dst" || return
  else
    "$AVX_CLANG" --target=x86_64-apple-darwin -isysroot "$(xcrun --show-sdk-path)" -D_FORTIFY_SOURCE=0 -O0 -mavx -mavx2 -mbmi -mpclmul \
      -I target/hqc/avx2/hqc-1 -I target/hqc/hqc-1 -I target/hqc/avx2 -I target/hqc -c -emit-llvm -o "$d/build/hqc/avx_1.raw.bc" "$dst" 2>/dev/null || return
    python3 scripts/hqc_avx_ir.py "$(dirname "$AVX_CLANG")/" "$d/build/hqc/avx_1.raw.bc" "$d/build/hqc/avx_1.bc" --slack > /dev/null || return
  fi
  if [ -n "$sexpr" ]; then sed -e "$sexpr" "proof/hqc/$script" > "$d/proof/hqc/$script"
    cmp -s "proof/hqc/$script" "$d/proof/hqc/$script" && { printf '%-22s %-9s %-7s %s\n' "$name" ERROR - "script edit did not apply"; return; }
  else cp "proof/hqc/$script" "$d/proof/hqc/"; fi
  local start pid timed_out=0; start=$(date +%s)
  (cd "$d" && exec env CRYPTOLPATH="$ROOT/model/cryptol/hqc" saw "proof/hqc/$script" > saw.log 2>&1) &
  pid=$!
  while kill -0 "$pid" 2>/dev/null; do
    if [ $(( $(date +%s) - start )) -ge "$LIMIT" ]; then
      timed_out=1; pkill -KILL -P "$pid" 2>/dev/null; kill -KILL "$pid" 2>/dev/null; break   # this saw and its solvers only
    fi
    sleep 2
  done
  wait "$pid" 2>/dev/null; local rc=$?
  local secs=$(( $(date +%s) - start ))
  # The last failure line: the earlier ones belong to the script's own gated mutants, which must fail.
  local why; why=$(grep -E 'Subgoal failed: [a-z_0-9]+|Symbolic execution failed|error: in [a-zA-Z]' "$d/saw.log" | tail -1 | cut -c1-70)
  if [ $timed_out -eq 1 ]; then printf '%-22s %-9s %-7s %s\n' "$name" no-result "$secs" "killed at the limit; last line: $(tail -1 "$d/saw.log" | cut -c1-50)"
  elif [ -z "$expr" ]; then  # control row: unmodified C, the edited script must pass
    if [ $rc -eq 0 ]; then printf '%-22s %-9s %-7s %s\n' "$name" ctl-pass "$secs" "saw exit 0 on the unmodified C"
    else printf '%-22s %-9s %-7s %s\n' "$name" ctl-FAIL "$secs" "${why:-exit $rc}"; fi
  elif [ $rc -ne 0 ]; then printf '%-22s %-9s %-7s %s\n' "$name" caught "$secs" "${why:-exit $rc}"
  else printf '%-22s %-9s %-7s %s\n' "$name" MISSED "$secs" "saw exit 0"; fi
}

if [ "$WHICH" != avx ]; then
  run_mutant ref-schoolbook-carry ref '/r\[base + j + 1\] \^= (b\[j\] >> inv) \& mask;/d'
  run_mutant ref-schoolbook-carry/abc ref '/r\[base + j + 1\] \^= (b\[j\] >> inv) \& mask;/d' 's/false sb_8_spec rme;/false sb_8_spec abc;/'
  run_mutant ref-karatsuba-mid    ref 's/uint64_t mid = zmid\[i\] \^ z0i \^ z2i;/uint64_t mid = zmid[i] ^ z2i;/'
  run_mutant ref-child-overlap    ref 's/uint64_t \*child_buffer = tmp_buffer + 8 \* n;/uint64_t *child_buffer = tmp_buffer + 7 * n;/'
  run_mutant ref-reduce-shift     ref 's/a\[i + VEC_N_SIZE_64 - 1\] >> (PARAM_N \& 0x3F);/a[i + VEC_N_SIZE_64 - 1] >> ((PARAM_N - 1) \& 0x3F);/'
  run_mutant ref-reduce-mask      ref '/o\[VEC_N_SIZE_64 - 1\] \&= BITMASK(PARAM_N, 64);/d'
fi
if [ "$WHICH" != ref ]; then
  run_mutant avx-prefix-xor       avx 's/B\[i\] = B\[i - 1\] \^ A\[i\];/B[i] = A[i];/'
  # toom_3_mult with both inputs fixed (a_i = i*0x9E3779B97F4A7C15 + 0x0123456789ABCDEF, b_i likewise with
  # other constants) and km96 interpreted: the obligation becomes a closed term. The script stops after
  # toom_3_mult (a concrete-input tt could not serve as the vect_mul override).
  CONCRETE='s#a <- llvm_fresh_var "a" (w 282);#let a = {{ [ i * 0x9E3779B97F4A7C15 + 0x0123456789ABCDEF | i <- [0..281] ] : [282][64] }};#; s#b <- llvm_fresh_var "b" (w 282);#let b = {{ [ i * 0xC2B2AE3D27D4EB4F + 0xFEDCBA9876543210 | i <- [0..281] ] : [282][64] }};#; s#tm1 a b }})) (w4_unint_z3 \["km96"\])#tm1 a b }})) (w4_unint_z3 [])#; /^\/\/ vect_mul:/,$d'
  run_mutant avx-prefix-xor/concrete avx 's/B\[i\] = B\[i - 1\] \^ A\[i\];/B[i] = A[i];/' "$CONCRETE"
  run_mutant avx-prefix-xor/ctl   avx '' "$CONCRETE"
  run_mutant avx-karat1-dd2       avx 's/__m128i DD1 = _mm_xor_si128(_mm_xor_si128(DD0, DD2), _mm_clmulepi64_si128(AAlpAAh, BBlpBBh, 0));/__m128i DD1 = _mm_xor_si128(DD0, _mm_clmulepi64_si128(AAlpAAh, BBlpBBh, 0));/'
  run_mutant avx-karat1-dd2/abc   avx 's/__m128i DD1 = _mm_xor_si128(_mm_xor_si128(DD0, DD2), _mm_clmulepi64_si128(AAlpAAh, BBlpBBh, 0));/__m128i DD1 = _mm_xor_si128(DD0, _mm_clmulepi64_si128(AAlpAAh, BBlpBBh, 0));/' 's/{{ km4 a b }})) rme;/{{ km4 a b }})) abc;/'
fi
