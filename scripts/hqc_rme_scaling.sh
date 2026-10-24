#!/usr/bin/env bash
# How SAW's rme backend scales on HQC's bit-sliced leaf: schoolbook_mul(s) == km<s> (the Karatsuba
# model) as s grows, one size per run, rme only. A measurement, not a gate (make hqc-rme-scaling).
#
# Usage: scripts/hqc_rme_scaling.sh [param=1] [sizes="8 9 17 18 34 35"] [limit_seconds=1200]
# The sizes must be ones the parameter set's recursion reaches (KM<p>.cry defines km<s> for them).
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
P="${1:-1}"; SIZES="${2:-8 9 17 18 34 35}"; LIMIT="${3:-1200}"
export PATH="$ROOT/.tools/bin:$PATH"
BC="build/hqc/gf2x_$P.bc"
[ -f "$BC" ] || { echo "!! $BC missing: run make hqc first" >&2; exit 1; }
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
echo ">> machine: $(uname -m) $(sw_vers -productVersion 2>/dev/null || uname -r); saw $(saw --version 2>/dev/null | head -1)"
echo ">> obligation: hqc-$P schoolbook_mul(s) == km<s>, rme, limit ${LIMIT}s per size"
printf '%-6s %-10s %s\n' words result seconds
for S in $SIZES; do
  cat > "$TMP/s.saw" <<SAW
import "GF2X.cry";
import "KM$P.cry";
m <- llvm_load_module "$ROOT/$BC";
let spec = do {
  rp <- llvm_alloc (llvm_array $((2*S)) (llvm_int 64));
  ap <- llvm_alloc_readonly (llvm_array $S (llvm_int 64));
  bp <- llvm_alloc_readonly (llvm_array $S (llvm_int 64));
  a <- llvm_fresh_var "a" (llvm_array $S (llvm_int 64));
  b <- llvm_fresh_var "b" (llvm_array $S (llvm_int 64));
  llvm_points_to ap (llvm_term a);
  llvm_points_to bp (llvm_term b);
  llvm_execute_func [rp, ap, bp, llvm_term {{ $S : [64] }}];
  llvm_points_to rp (llvm_term {{ km$S a b }});
};
llvm_verify m "schoolbook_mul" [] false spec rme;
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
  else res="ERROR: $(grep -m1 -iE 'error|fail|exception' "$TMP/out" | cut -c1-80)"; fi
  printf '%-6s %-10s %s\n' "$S" "$res" "$secs"
done
