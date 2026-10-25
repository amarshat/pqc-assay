#!/usr/bin/env bash
# Which SAW backends can prove HQC's bit-sliced schoolbook_mul equal to the Karatsuba model?
#
# One obligation, several backends, a fixed wall-clock limit each. The obligation is the leaf proof
# of proof/hqc/karatsuba_<p>.saw (schoolbook_mul(s) == km<s>) at one leaf size. A run that finishes
# reports the backend's verdict; a run that hits the limit reports TIMEOUT; a run that errors reports
# ERROR with the first error line. This is a measurement, not a gate: it is out of band (make
# hqc-solvers) and never fails the build.
#
# Usage: scripts/hqc_solver_study.sh [param=1] [size=8] [limit_seconds=600] [true|false|cmut]
#   false runs the same backends on the WRONG obligation (bit 0 of the result flipped), which a
#   backend should refute: a canonical-form backend proves a true equality fast but may not refute.
#   cmut keeps the true specification and runs it against a copy of gf2x.c with one schoolbook term
#   dropped (the ref-schoolbook-carry mutant of scripts/hqc_c_mutants.sh), which is also false.
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
P="${1:-1}"; S="${2:-8}"; LIMIT="${3:-600}"; KIND="${4:-true}"
MUT=""; [ "$KIND" = false ] && MUT=" ^ ([1] # zero)"
export PATH="$ROOT/.tools/bin:$PATH"
BC="build/hqc/gf2x_$P.bc"
[ -f "$BC" ] || { echo "!! $BC missing: run make hqc first" >&2; exit 1; }
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
if [ "$KIND" = cmut ]; then   # the one-line source mutant, compiled as make hqc compiles gf2x.c
  sed -e '/r\[base + j + 1\] \^= (b\[j\] >> inv) \& mask;/d' target/hqc/gf2x.c > "$TMP/gf2x.c"
  cmp -s target/hqc/gf2x.c "$TMP/gf2x.c" && { echo "!! mutation did not apply" >&2; exit 1; }
  clang -c -emit-llvm -O0 -g -I "target/hqc/hqc-$P" -I target/hqc -o "$TMP/gf2x_mut.bc" "$TMP/gf2x.c" || exit 1
  BC="$TMP/gf2x_mut.bc"; BCDESC="the schoolbook-carry source mutant"
else BCDESC="the vendored C"; fi

echo ">> machine: $(uname -m) $(sw_vers -productVersion 2>/dev/null || uname -r); saw $(saw --version 2>/dev/null | head -1)"
echo ">> obligation: hqc-$P schoolbook_mul($S) == km$S$MUT on $BCDESC ($KIND); limit ${LIMIT}s per backend"
printf '%-10s %-10s %s\n' backend result seconds
for tac in rme abc z3 yices cvc5 bitwuzla; do
  cat > "$TMP/s.saw" <<SAW
import "GF2X.cry";
import "KM$P.cry";
m <- llvm_load_module "$BC";
let spec = do {
  rp <- llvm_alloc (llvm_array $((2*S)) (llvm_int 64));
  ap <- llvm_alloc_readonly (llvm_array $S (llvm_int 64));
  bp <- llvm_alloc_readonly (llvm_array $S (llvm_int 64));
  a <- llvm_fresh_var "a" (llvm_array $S (llvm_int 64));
  b <- llvm_fresh_var "b" (llvm_array $S (llvm_int 64));
  llvm_points_to ap (llvm_term a);
  llvm_points_to bp (llvm_term b);
  llvm_execute_func [rp, ap, bp, llvm_term {{ $S : [64] }}];
  llvm_points_to rp (llvm_term {{ km$S a b$MUT }});
};
llvm_verify m "schoolbook_mul" [] false spec $tac;
print "PROVED";
SAW
  start=$(date +%s)
  CRYPTOLPATH="$ROOT/model/cryptol/hqc" saw "$TMP/s.saw" > "$TMP/out" 2>&1 &
  pid=$!; timed_out=0
  while kill -0 "$pid" 2>/dev/null; do
    if [ $(( $(date +%s) - start )) -ge "$LIMIT" ]; then
      timed_out=1
      pkill -KILL -P "$pid" 2>/dev/null   # this run's solver children only
      kill -KILL "$pid" 2>/dev/null
      break
    fi
    sleep 2
  done
  wait "$pid" 2>/dev/null
  secs=$(( $(date +%s) - start ))
  if [ $timed_out -eq 1 ]; then res=TIMEOUT
  elif grep -q '^PROVED' "$TMP/out"; then res=proved
  elif grep -q 'Proof failed\|Subgoal failed' "$TMP/out"; then res=refuted
  else res="ERROR: $(grep -m1 -iE 'error|fail|exception' "$TMP/out" | cut -c1-80)"; fi
  printf '%-10s %-10s %s\n' "$tac" "$res" "$secs"
done
