#!/usr/bin/env bash
# Mechanized lift gate for the escape-2 (Route Y) Barrett bridge:
# verify that the committed Isabelle model `spec/isabelle/tier2/barrett/Barrett_Lift.thy` is
# byte-for-byte what `cryptol-to-isabelle` produces from the Cryptol Barrett model
# `implementations/rustcrypto-ml-dsa/proof/ntt/barrett_bridge.cry` — the SAME .cry SAW uses to
# reason about the deployed `barrett_reduce`. So the object Route Y (Barrett_Bridge.thy) proves
# `== x mod q` is exactly the lift of the checked Cryptol model, not a hand-transcription trusted
# by eyeball.
#
# The ONLY permitted difference is the theory name: the generator emits `theory "barrett_bridge"`,
# but the committed file is `theory Barrett_Lift` (renamed to dodge the macOS case-insensitive-FS
# collision with `Barrett_Bridge.thy`). This script normalizes that one line, then requires an
# exact diff on everything else (the Cryptol-semantics definitions).
#
# Needs only the SAW bundle (cryptol-to-isabelle) on PATH — NOT a full Isabelle build.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
export PATH="$ROOT/.tools/bin:$PATH"

CRY="implementations/rustcrypto-ml-dsa/proof/ntt/barrett_bridge.cry"
COMMITTED="spec/isabelle/tier2/barrett/Barrett_Lift.thy"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

echo ">> regenerating Isabelle Barrett model from $CRY"
cryptol-to-isabelle -s "$CRY" -d "$TMP" --all-modules >/dev/null

GEN="$TMP/barrett_bridge.thy"
# Normalize only the theory-name line (the sole sanctioned edit on the committed copy).
sed '1s/^theory "barrett_bridge"$/theory Barrett_Lift/' "$GEN" > "$TMP/normalized.thy"

if diff -u "$COMMITTED" "$TMP/normalized.thy"; then
  echo ">> barrett lift-check OK: Barrett_Lift.thy == cryptol-to-isabelle($CRY) (modulo theory name)"
else
  echo "!! barrett lift-check FAILED: the committed Barrett_Lift.thy is OUT OF SYNC with the Cryptol model." >&2
  echo "!! Route Y is only sound if the lifted model it proves about matches the .cry SAW checks. Regenerate with:" >&2
  echo "!!   cryptol-to-isabelle -s $CRY -d <dir> --all-modules   (then keep the 'theory Barrett_Lift' rename)" >&2
  exit 1
fi
