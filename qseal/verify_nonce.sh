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

# Timings from these scripts are only meaningful with the machine and toolchain named, so print them.
echo "== $(basename "$0") on $(uname -srm), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || (grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2- | sed 's/^ //') || echo 'unknown CPU')"
echo "== toolchain: $(if command -v saw >/dev/null 2>&1; then saw --version | head -1 | sed 's/^/saw /'; else echo 'saw n/a'; fi); $(if command -v cryptol >/dev/null 2>&1; then cryptol --version | head -1; else echo 'cryptol n/a'; fi); $(if command -v proverif >/dev/null 2>&1; then proverif -help 2>&1 | head -1 | cut -d, -f1; else echo 'proverif n/a'; fi); $(${CLANG:-clang} --version | head -1)"

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

# 2. The expiring store (nonce_exp.c): windowed single use plus the availability property the
#    append-only store does not have.
cd "$HERE/model"
EOUT="$(cryptol -b /dev/stdin <<'EOF' 2>&1
:l QSEAL_NonceExp.cry
:set prover=z3
:prove no_replay_in_window
:prove consume_marks_live
:prove expiry_restores_room
:prove expired_never_accepted
:prove accept_reachable
EOF
)"
echo "$EOUT"
EQED="$(printf '%s\n' "$EOUT" | grep -c 'Q.E.D.' || true)"
ECEX="$(printf '%s\n' "$EOUT" | grep -c 'Counterexample' || true)"
if [ "$EQED" -ne 5 ] || [ "$ECEX" -ne 0 ]; then
  echo "FAIL: expiring-store model expected 5 Q.E.D.; got QED=$EQED CEX=$ECEX"
  exit 1
fi
echo "OK: expiring-store model (5/5 Q.E.D.: windowed single use, marks live, expiry restores room, expired never accepted, accept reachable)"

# 3. C reference == model.
mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/nonce.c" -o "$HERE/build/nonce.bc"
cd "$HERE/proof"
saw nonce.saw

# 4. The expiring store's C reference == its model, and the evict-live variant is rejected.
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/nonce_exp.c" -o "$HERE/build/nonce_exp.bc"
cd "$HERE/proof"
EXPOUT="$(saw nonce_exp.saw)"
echo "$EXPOUT"
EOK="$(printf '%s\n' "$EXPOUT" | grep -c '^VERIFIED:' || true)"
EMUT="$(printf '%s\n' "$EXPOUT" | grep -c '^MUTATION CAUGHT:' || true)"
if [ "$EOK" -ne 1 ] || [ "$EMUT" -ne 1 ]; then
  echo "FAIL: expiring store expected 1 VERIFIED + 1 MUTATION CAUGHT; got VERIFIED=$EOK MUTATION=$EMUT"
  exit 1
fi
echo "OK: expiring store C == model, evict-live mutant rejected"
