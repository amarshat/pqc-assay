#!/usr/bin/env bash
# Q-SEAL single-use challenge store (section 16 property 4: a consumed request_id cannot be accepted
# twice). Two checks:
#   1. cryptol + z3: the model QSEAL_Nonce.cry proves no_replay / consumed_never_accepts /
#      consume_marks_seen, and the no-consume bug is demonstrably replayable (:sat Satisfiable).
#   2. clang + SAW: the C reference qseal/ref/nonce.c equals the model (acceptBit, nextStore), and the
#      no-consume variant is rejected by that spec.
# Exits non-zero on any failure.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

if ! command -v cryptol >/dev/null 2>&1 || ! command -v saw >/dev/null 2>&1; then
  export PATH="$REPO/.tools/bin:$PATH"
fi
command -v cryptol >/dev/null 2>&1 || { echo "FAIL: cryptol not found (expected on PATH or in .tools/bin)"; exit 2; }
command -v saw >/dev/null 2>&1 || { echo "FAIL: saw not found (expected on PATH or in .tools/bin)"; exit 2; }
CLANG="${CLANG:-clang}"
command -v "$CLANG" >/dev/null 2>&1 || { echo "FAIL: clang not found (set CLANG=...)"; exit 2; }

# 1. Model-level properties.
cd "$HERE/model"
OUT="$(cryptol -b /dev/stdin <<'EOF' 2>&1
:l QSEAL_Nonce.cry
:set prover=z3
:prove no_replay
:prove consumed_never_accepts
:prove consume_marks_seen
:sat replay_possible_bug
EOF
)"
echo "$OUT"

QED="$(printf '%s\n' "$OUT" | grep -c 'Q.E.D.' || true)"
SAT="$(printf '%s\n' "$OUT" | grep -c 'Satisfiable' || true)"
UNSAT="$(printf '%s\n' "$OUT" | grep -c 'Unsatisfiable' || true)"
CEX="$(printf '%s\n' "$OUT" | grep -c 'Counterexample' || true)"
if [ "$QED" -ne 3 ] || [ "$SAT" -ne 1 ] || [ "$UNSAT" -ne 0 ] || [ "$CEX" -ne 0 ]; then
  echo "FAIL: model check expected 3 Q.E.D. + 1 Satisfiable (the replay bug) + 0 Unsatisfiable/Counterexample; got QED=$QED SAT=$SAT UNSAT=$UNSAT CEX=$CEX"
  exit 1
fi
echo "OK: model single-use properties (3/3 Q.E.D.) and the no-consume bug is replayable (SAT)"

# 2. C reference == model.
mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/nonce.c" -o "$HERE/build/nonce.bc"
cd "$HERE/proof"
saw nonce.saw
