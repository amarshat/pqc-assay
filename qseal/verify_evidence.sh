#!/usr/bin/env bash
# Q-SEAL evidence-fragment reassembly (section 16 property 6: reassembly produces exactly the original
# evidence bytes or fails closed). Two checks:
#   1. cryptol + z3: the model QSEAL_Evidence.cry proves reassemble_round_trip and fail-closed on a
#      dropped or mis-sized fragment, and shows a no-completeness reassembler corrupts (:sat).
#   2. clang + SAW: the C reference qseal/ref/evidence.c equals the model, and the no-completeness
#      variant is rejected by the reassemble spec.
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
:l QSEAL_Evidence.cry
:set prover=z3
:prove reassemble_round_trip
:prove dropped_fragment_rejected
:prove wrong_total_rejected
:sat bug_corrupts
EOF
)"
echo "$OUT" | grep -vE '^\s+(0x|\[0x|0,|\[0,)' | head -30

QED="$(printf '%s\n' "$OUT" | grep -c 'Q.E.D.' || true)"
SAT="$(printf '%s\n' "$OUT" | grep -c 'Satisfiable' || true)"
UNSAT="$(printf '%s\n' "$OUT" | grep -c 'Unsatisfiable' || true)"
CEX="$(printf '%s\n' "$OUT" | grep -c 'Counterexample' || true)"
if [ "$QED" -ne 3 ] || [ "$SAT" -ne 1 ] || [ "$UNSAT" -ne 0 ] || [ "$CEX" -ne 0 ]; then
  echo "FAIL: model check expected 3 Q.E.D. + 1 Satisfiable (the corrupting bug) + 0 Unsatisfiable/Counterexample; got QED=$QED SAT=$SAT UNSAT=$UNSAT CEX=$CEX"
  exit 1
fi
echo "OK: model reassembly properties (3/3 Q.E.D.) and the no-completeness reassembler corrupts (SAT)"

# 2. C reference == model.
mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/evidence.c" -o "$HERE/build/evidence.bc"
cd "$HERE/proof"
saw evidence.saw
