#!/usr/bin/env bash
# Property 3's obligation holds only under a tactic that keeps the two signature verifiers
# uninterpreted. This runs the same obligations under the default z3 and requires all three to verify,
# including the two injected mutants, which is the failure the paper reports. If a future SAW or
# Cryptol stops unfolding the placeholders, this script fails and the paper's claim needs revisiting.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"
command -v saw >/dev/null 2>&1 || export PATH="$REPO/.tools/bin:$PATH"
CLANG="${CLANG:-clang}"
mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/hybrid.c" -o "$HERE/build/hybrid.bc"
cd "$HERE/proof"
OUT="$(saw hybrid_plain_z3.saw)"
echo "$OUT"
n="$(printf '%s\n' "$OUT" | grep -c 'Proof succeeded' || true)"
if [ "$n" -ne 3 ]; then
  echo "FAIL: expected 3 'Proof succeeded' under plain z3 (honest + both mutants); got $n"
  exit 1
fi
echo "OK: under plain z3 the obligation and both injected mutants all verify, so the result depends"
echo "    entirely on w4_unint_z3 keeping vE and vM uninterpreted."
