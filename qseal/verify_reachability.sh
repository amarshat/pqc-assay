#!/usr/bin/env bash
# Q-SEAL section 16 property 5: PROFILE_ACTION_OBSERVED (assertion type 0x04) cannot be reached through a
# host-exposed APDU path. Checked in ProVerif (symbolic model), because this is a reachability property
# over the command surface, not a fixed-format identity.
#   1. property5.pv (guarded host path): ProVerif proves the correspondence "an OBSERVED assertion is
#      signed only after the trusted internal callback" is TRUE.
#   2. property5_mutant.pv (host guard dropped): ProVerif FALSIFIES the same query, i.e. it finds a trace
#      where the host obtains an OBSERVED assertion with no internal callback.
# Exits 0 only if the good model proves the query and the mutant refutes it.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

# Prefer a pinned proverif, then the repo toolchain dir, then an opam switch.
if ! command -v proverif >/dev/null 2>&1; then
  export PATH="$REPO/.tools/bin:$HOME/.opam/proverif/bin:$PATH"
fi
command -v proverif >/dev/null 2>&1 || { echo "FAIL: proverif not found (expected on PATH, in .tools/bin, or the opam 'proverif' switch)"; exit 2; }

PV="$HERE/proof/proverif"

echo ">> ProVerif: property5.pv (guarded host path) -- expect the query TRUE"
GOOD="$(proverif "$PV/property5.pv" 2>&1)"
echo "$GOOD" | grep -E '^RESULT'

echo ">> ProVerif: property5_mutant.pv (host guard dropped) -- expect the query FALSE"
MUT="$(proverif "$PV/property5_mutant.pv" 2>&1)"
echo "$MUT" | grep -E '^RESULT'

good_true="$(printf '%s\n' "$GOOD"  | grep -cE '^RESULT .* is true\.'  || true)"
good_false="$(printf '%s\n' "$GOOD" | grep -cE '^RESULT .* is false\.' || true)"
mut_true="$(printf '%s\n' "$MUT"    | grep -cE '^RESULT .* is true\.'  || true)"
mut_false="$(printf '%s\n' "$MUT"   | grep -cE '^RESULT .* is false\.' || true)"

if [ "$good_true" = "1" ] && [ "$good_false" = "0" ] && [ "$mut_false" = "1" ] && [ "$mut_true" = "0" ]; then
  echo "OK: OBSERVED is reachable only via the internal callback (query true); the host-path mutant is refuted (query false)."
  exit 0
fi
echo "FAIL: expected good=true/mutant=false; got good_true=$good_true good_false=$good_false mut_true=$mut_true mut_false=$mut_false"
exit 1
