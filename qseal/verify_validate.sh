#!/usr/bin/env bash
# Q-SEAL request validation (section 16 property 7: a malformed request fails before signing). Two
# checks:
#   1. cryptol + z3: the model QSEAL_Validate.cry proves malformed_never_signs / signed_is_validated,
#      exhibits a valid request (:sat), and shows a no-suite-check gate accepts an unsupported suite.
#   2. clang + SAW: the C reference qseal/ref/validate.c equals the model (valid, create_checked), and
#      the no-suite-check variant is rejected by the validate-then-sign spec.
# Exits non-zero on any failure.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

if ! command -v cryptol >/dev/null 2>&1 || ! command -v saw >/dev/null 2>&1; then
  export PATH="$REPO/.tools/bin:$PATH"
fi
command -v cryptol >/dev/null 2>&1 || { echo "FAIL: cryptol not found (expected on PATH or in .tools/bin)"; exit 2; }
command -v saw     >/dev/null 2>&1 || { echo "FAIL: saw not found (expected on PATH or in .tools/bin)"; exit 2; }
CLANG="${CLANG:-clang}"
command -v "$CLANG" >/dev/null 2>&1 || { echo "FAIL: clang not found (set CLANG=...)"; exit 2; }

# 1. Model-level properties.
cd "$HERE/model"
OUT="$(cryptol -b /dev/stdin <<'EOF' 2>&1
:l QSEAL_Validate.cry
:set prover=z3
:prove malformed_never_signs
:prove signed_is_validated
:sat valid
:sat bug_signs_malformed
:sat bug_signs_observed
EOF
)"
echo "$OUT"

QED="$(printf '%s\n' "$OUT" | grep -c 'Q.E.D.' || true)"
SAT="$(printf '%s\n' "$OUT" | grep -c 'Satisfiable' || true)"
UNSAT="$(printf '%s\n' "$OUT" | grep -c 'Unsatisfiable' || true)"
CEX="$(printf '%s\n' "$OUT" | grep -c 'Counterexample' || true)"
if [ "$QED" -ne 2 ] || [ "$SAT" -ne 3 ] || [ "$UNSAT" -ne 0 ] || [ "$CEX" -ne 0 ]; then
  echo "FAIL: model check expected 2 Q.E.D. + 3 Satisfiable (a valid request, the no-suite-check bug, the allow-observed bug) + 0 Unsatisfiable/Counterexample; got QED=$QED SAT=$SAT UNSAT=$UNSAT CEX=$CEX"
  exit 1
fi
echo "OK: model validation properties (2/2 Q.E.D.), a valid request exists (SAT), and the no-suite-check + allow-observed gates are over-permissive (SAT)"

# 2. C reference == model (build tbs_v1.c + assertion.c + validate.c as one TU).
mkdir -p "$HERE/build"
cat "$HERE/ref/tbs_v1.c" "$HERE/ref/assertion.c" "$HERE/ref/validate.c" > "$HERE/build/_validate_combined.c"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/build/_validate_combined.c" -o "$HERE/build/validate.bc"
cd "$HERE/proof"
saw validate.saw
