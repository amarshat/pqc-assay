#!/usr/bin/env bash
# Q-SEAL CREATE_ASSERTION verification (section 16 property 2):
#  (1) cryptol/z3: the model `create` binds the validated challenge and the applet controls its own
#      identity fields (binds_challenge, applet_controls_identity).
#  (2) SAW: the C reference qseal_create_assertion equals the Cryptol `create`.
# Exits non-zero on any failure.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

command -v saw     >/dev/null 2>&1 || export PATH="$REPO/.tools/bin:$PATH"
command -v saw     >/dev/null 2>&1 || { echo "FAIL: saw not found";     exit 2; }
command -v cryptol >/dev/null 2>&1 || { echo "FAIL: cryptol not found"; exit 2; }
CLANG="${CLANG:-clang}"
command -v "$CLANG" >/dev/null 2>&1 || { echo "FAIL: clang not found (set CLANG=...)"; exit 2; }

# (1) model-level binding properties
cd "$HERE/model"
OUT="$(cryptol -b /dev/stdin <<'EOF' 2>&1
:l QSEAL_Assertion.cry
:set prover=z3
:prove binds_challenge
:prove applet_controls_identity
EOF
)"
echo "$OUT"
QED="$(printf '%s\n' "$OUT" | grep -c 'Q.E.D.' || true)"
CEX="$(printf '%s\n' "$OUT" | grep -c 'Counterexample' || true)"
[ "$QED" -eq 2 ] && [ "$CEX" -eq 0 ] || { echo "FAIL: binding properties (QED=$QED CEX=$CEX)"; exit 1; }

# (2) C reference == model (build assertion.c + tbs_v1.c as one TU; no llvm-link in the toolchain)
mkdir -p "$HERE/build"
cat "$HERE/ref/tbs_v1.c" "$HERE/ref/assertion.c" > "$HERE/build/_assertion_combined.c"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/build/_assertion_combined.c" -o "$HERE/build/assertion.bc"
cd "$HERE/proof"
saw assertion.saw
