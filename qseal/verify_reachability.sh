#!/usr/bin/env bash
# Q-SEAL section 16 property 5: PROFILE_ACTION_OBSERVED (assertion type 0x04) cannot be reached through a
# host-exposed APDU path. Checked in ProVerif (symbolic model), because this is a reachability property
# over the command surface, not a fixed-format identity.
#   1. property5.pv (guarded host path): ProVerif proves the correspondence "an OBSERVED assertion is
#      signed only after the trusted internal callback" is TRUE.
#   2. property5_reachable.pv (same model, reachability query only): SignedObserved must be REACHABLE.
#      Without this the positive result in (1) proves nothing, which is exactly how the previous version
#      of this model came to be vacuous (docs/ASSUMPTIONS.md OF-3): nothing wrote to the private callback
#      channel, so the event in the query antecedent could never occur.
#   3. property5_mutant.pv (host guard dropped): ProVerif FALSIFIES the correspondence, i.e. it finds a
#      trace where the host obtains an OBSERVED assertion with no internal callback.
# Exits 0 only if all three hold.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

# Prefer a pinned proverif, then the repo toolchain dir, then an opam switch.
if ! command -v proverif >/dev/null 2>&1; then
  export PATH="$REPO/.tools/bin:$HOME/.opam/proverif/bin:$PATH"
fi
command -v proverif >/dev/null 2>&1 || { echo "FAIL: proverif not found (expected on PATH, in .tools/bin, or the opam 'proverif' switch)"; exit 2; }

PV="$HERE/proof/proverif"

echo ">> ProVerif: property5.pv (guarded host path) -- expect the correspondence TRUE"
GOOD="$(proverif "$PV/property5.pv" 2>&1)"
echo "$GOOD" | grep -E '^RESULT'

echo ">> ProVerif: property5_reachable.pv (non-vacuity) -- expect the observed-action event REACHABLE"
REACH="$(proverif "$PV/property5_reachable.pv" 2>&1)"
echo "$REACH" | grep -E '^RESULT'

echo ">> ProVerif: property5_mutant.pv (host guard dropped) -- expect the correspondence FALSE"
MUT="$(proverif "$PV/property5_mutant.pv" 2>&1)"
echo "$MUT" | grep -E '^RESULT'

good_true="$(printf '%s\n' "$GOOD"  | grep -cE '^RESULT .* is true\.'  || true)"
good_false="$(printf '%s\n' "$GOOD" | grep -cE '^RESULT .* is false\.' || true)"
mut_true="$(printf '%s\n' "$MUT"    | grep -cE '^RESULT .* is true\.'  || true)"
mut_false="$(printf '%s\n' "$MUT"   | grep -cE '^RESULT .* is false\.' || true)"

# ProVerif proves the NEGATION of a reachability query, so an event that can occur is reported as
# "RESULT not event(...) is false." That false is the witness we want; a true here means the honest
# path is dead and the correspondence above is vacuous.
reach_live="$(printf '%s\n' "$REACH" | grep -cE '^RESULT not event\(SignedObserved.*is false\.' || true)"
reach_dead="$(printf '%s\n' "$REACH" | grep -cE '^RESULT not event\(SignedObserved.*is true\.'  || true)"

if [ "$reach_live" -lt 1 ] || [ "$reach_dead" -ne 0 ]; then
  echo "FAIL (VACUITY): the observed-action event is not reachable in the model, so the correspondence in property5.pv holds trivially. See docs/ASSUMPTIONS.md OF-3."
  exit 1
fi

# ProVerif may print an extra parenthetical "(even event ... is false.)" line when an injective query
# fails, so require at-least-one false for the mutant rather than exactly one.
if [ "$good_true" -ge 1 ] && [ "$good_false" -eq 0 ] && [ "$mut_false" -ge 1 ] && [ "$mut_true" -eq 0 ]; then
  echo "OK: the observed-action event is reachable (non-vacuous), the injective correspondence holds, and the host-path mutant is refuted."
  exit 0
fi
echo "FAIL: expected good=true/mutant=false; got good_true=$good_true good_false=$good_false mut_true=$mut_true mut_false=$mut_false"
exit 1
