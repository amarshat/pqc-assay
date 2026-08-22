#!/usr/bin/env bash
# Q-SEAL section 16 property 5: PROFILE_ACTION_OBSERVED (assertion type 0x04) must not be obtainable
# through a host-exposed APDU path. A safety property over the command surface, checked in ProVerif
# (Dolev-Yao). Four queries, five runs, every cell gated:
#
#   Q1  every observed-action assertion follows an internal event with the same data
#   Q2  every observed-typed signature the ATTACKER holds follows such an event
#   Q3  the attacker cannot obtain an assertion over content of its own choosing
#   SK  the signing key never leaks
#
#   property5.pv                     Q1 true,  Q2 true,  Q3 true,  SK true
#   property5_reachable.pv  GENERATED  the observed-action event must be REACHABLE, else the positives
#                                      above hold vacuously (docs/ASSUMPTIONS.md OF-3)
#   property5_ablation.pv   GENERATED  the spec 8.4 guard deleted and NOTHING else: Q2 and Q3 must be
#                                      false, or the result does not depend on the guard it is about
#   property5_mutant_databind.pv     builder signs handset subject:     Q1 true, Q2 false
#   property5_mutant_hostdata.pv     card attests host-supplied fields: Q1 true, Q2 true, Q3 false
#
# The two generated files are derived from property5.pv at run time by proof/proverif/gen_variants.py,
# so neither can drift from the model. Both existed as checked-in copies once, and a review showed that
# a copy certifies the copy: deleting the honest emitter from the model alone left the witness reporting
# reachability the model no longer had, with this gate green.
# Exits 0 only if every cell matches.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

# Prefer a pinned proverif, then the repo toolchain dir, then an opam switch.
if ! command -v proverif >/dev/null 2>&1; then
  export PATH="$REPO/.tools/bin:$HOME/.opam/pv/bin:$HOME/.opam/proverif/bin:$PATH"
fi
command -v proverif >/dev/null 2>&1 || { echo "FAIL: proverif not found (expected on PATH, in .tools/bin, or an opam switch). scripts/setup.sh builds it."; exit 2; }

# Timings from these scripts are only meaningful with the machine and toolchain named, so print them.
echo "== $(basename "$0") on $(uname -srm), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || (grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2- | sed 's/^ //') || echo 'unknown CPU')"
echo "== toolchain: $(if command -v saw >/dev/null 2>&1; then saw --version | head -1 | sed 's/^/saw /'; else echo 'saw n/a'; fi); $(if command -v cryptol >/dev/null 2>&1; then cryptol --version | head -1; else echo 'cryptol n/a'; fi); $(if command -v proverif >/dev/null 2>&1; then proverif -help 2>&1 | head -1 | cut -d, -f1; else echo 'proverif n/a'; fi); $(${CLANG:-clang} --version | head -1)"

PV="$HERE/proof/proverif"
GEN="$HERE/build/pv"

python3 "$PV/gen_variants.py" "$PV/property5.pv" "$GEN"

q1='^RESULT event\(SignedObserved'
q2='^RESULT attacker\(sign\(tbs\(OBSERVED'
q3='^RESULT not attacker\(sign\(tbs\(OBSERVED'
sk='^RESULT not attacker\(sk'
wit='^RESULT not event\(SignedObserved'

fail=0
say_fail() { echo "FAIL: $*"; fail=1; }
count() { printf '%s\n' "$2" | grep -cE "$1" || true; }
expect() {  # expect <label> <output> <pattern> <true|false> <what>
  [ "$(count "$3.*is $4\." "$2")" -ge 1 ] || say_fail "$1: $5 is not $4"
}

echo ">> property5.pv: expect Q1 true, Q2 true, Q3 true, key secret"
GOOD="$(proverif "$PV/property5.pv" 2>&1)"; printf '%s\n' "$GOOD" | grep -E '^RESULT' || true
expect property5 "$GOOD" "$q1" true "Q1 (event correspondence)"
expect property5 "$GOOD" "$q2" true "Q2 (attacker-held signature)"
expect property5 "$GOOD" "$q3" true "Q3 (no attacker-chosen content)"
expect property5 "$GOOD" "$sk" true "signing-key secrecy"

echo ">> property5_reachable.pv (generated): expect the observed-action event REACHABLE"
REACH="$(proverif "$GEN/property5_reachable.pv" 2>&1)"; printf '%s\n' "$REACH" | grep -E '^RESULT' || true
[ "$(count "$wit.*is false\." "$REACH")" -ge 1 ] || say_fail "(VACUITY) the observed-action event is not reachable, so property5.pv proves nothing. See docs/ASSUMPTIONS.md OF-3."

echo ">> property5_ablation.pv (generated, spec 8.4 guard deleted): expect Q2 false, Q3 false"
ABL="$(proverif "$GEN/property5_ablation.pv" 2>&1)"; printf '%s\n' "$ABL" | grep -E '^RESULT' || true
expect ablation "$ABL" "$q2" false "Q2 with the guard removed (the result does not depend on the guard)"
expect ablation "$ABL" "$q3" false "Q3 with the guard removed (the result does not depend on the guard)"

echo ">> property5_mutant_databind.pv (builder signs handset subject): expect Q1 true, Q2 false"
MUTB="$(proverif "$PV/property5_mutant_databind.pv" 2>&1)"; printf '%s\n' "$MUTB" | grep -E '^RESULT' || true
expect databind "$MUTB" "$q1" true  "Q1 (it should stay true; that is the point)"
expect databind "$MUTB" "$q2" false "Q2"

echo ">> property5_mutant_hostdata.pv (card attests host-supplied fields): expect Q1 true, Q2 true, Q3 false"
MUTH="$(proverif "$PV/property5_mutant_hostdata.pv" 2>&1)"; printf '%s\n' "$MUTH" | grep -E '^RESULT' || true
expect hostdata "$MUTH" "$q1" true  "Q1 (it should stay true; that is the point)"
expect hostdata "$MUTH" "$q2" true  "Q2 (it should stay true; that is the point)"
expect hostdata "$MUTH" "$q3" false "Q3"

[ "$fail" -eq 0 ] || exit 1
echo "OK: event reachable; all four queries hold; deleting the spec 8.4 guard breaks Q2 and Q3; both content mutants caught by the query added for each."
