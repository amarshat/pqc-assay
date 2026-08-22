#!/usr/bin/env bash
# GSMA SGP.29 v1.1 EID validation: an EXTERNAL standard's rules, verified end to end.
#   1. cryptol + z3: the bridge lemmas and the clause-directed vectors.
#   2. clang + SAW: the C reference equals the Cryptol transcription, and three mutants are rejected.
# Exits non-zero on any failure.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

if ! command -v cryptol >/dev/null 2>&1 || ! command -v saw >/dev/null 2>&1; then
  export PATH="$REPO/.tools/bin:$PATH"
fi
command -v cryptol >/dev/null 2>&1 || { echo "FAIL: cryptol not found"; exit 2; }
command -v saw     >/dev/null 2>&1 || { echo "FAIL: saw not found"; exit 2; }
CLANG="${CLANG:-clang}"
command -v "$CLANG" >/dev/null 2>&1 || { echo "FAIL: clang not found (set CLANG=...)"; exit 2; }

echo "== $(basename "$0") on $(uname -srm), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || echo 'unknown CPU')"
echo "== toolchain: $(saw --version | head -1 | sed 's/^/saw /'); $(cryptol --version | head -1); $(${CLANG} --version | head -1)"

# 1. Model level: the bridge lemmas, the accumulator invariant, the wide-width counterexample, and one
#    clause-directed vector per rule.
cd "$HERE/model"
OUT="$(cryptol -b /dev/stdin <<'CRY' 2>&1
:l EID.cry
:set prover=z3
:prove step_reduce_early
:prove fold_acc_bounded
:sat step_wide_is_false
:prove kav_good
:prove kav_badcheck
:prove kav_e118
:prove kav_nondigit
:prove e118_checksum_is_valid
CRY
)"
echo "$OUT"
QED="$(printf '%s\n' "$OUT" | grep -c 'Q.E.D.' || true)"
SAT="$(printf '%s\n' "$OUT" | grep -c 'Satisfiable' || true)"
CEX="$(printf '%s\n' "$OUT" | grep -c 'Counterexample' || true)"
if [ "$QED" -ne 7 ] || [ "$SAT" -ne 1 ] || [ "$CEX" -ne 0 ]; then
  echo "FAIL: expected 7 Q.E.D. + 1 Satisfiable (the fixed-width counterexample); got QED=$QED SAT=$SAT CEX=$CEX"
  exit 1
fi
echo "OK: bridge lemmas, accumulator invariant, fixed-width counterexample, and 5 clause-directed vectors"

# 2. C reference == the transcription of the standard.
mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/eid.c" -o "$HERE/build/eid.bc"
cd "$HERE/proof"
SOUT="$(saw eid.saw)"
echo "$SOUT"
SOK="$(printf '%s\n' "$SOUT" | grep -c '^VERIFIED:' || true)"
SMUT="$(printf '%s\n' "$SOUT" | grep -c '^MUTATION CAUGHT:' || true)"
if [ "$SOK" -ne 1 ] || [ "$SMUT" -ne 3 ]; then
  echo "FAIL: expected 1 VERIFIED + 3 MUTATION CAUGHT; got VERIFIED=$SOK MUTATION=$SMUT"
  exit 1
fi
echo "OK: C reference == SGP.29 transcription, all three mutants rejected"
