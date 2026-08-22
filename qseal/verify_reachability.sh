#!/usr/bin/env bash
# Q-SEAL section 16 property 5: PROFILE_ACTION_OBSERVED (assertion type 0x04) must not be obtainable
# through a host-exposed APDU path. A safety property over the command surface, checked in ProVerif
# (Dolev-Yao). Four queries, five runs, and the whole matrix is gated:
#
#   Q1  every observed-action assertion follows an internal event with the same data
#   Q2  every observed-typed signature the ATTACKER holds follows such an event
#   Q3  the attacker cannot obtain an assertion over content of its own choosing
#   SK  the signing key never leaks
#
#   property5.pv                    Q1 true,  Q2 true,  Q3 true,  SK true
#   property5_reachable.pv          the observed-action event must be REACHABLE, else everything above
#                                   holds vacuously (docs/ASSUMPTIONS.md OF-3)
#   property5_mutant.pv             host guard dropped:            Q1 false, Q2 false, Q3 false
#   property5_mutant_databind.pv    builder signs handset subject: Q1 TRUE,  Q2 false, Q3 true
#   property5_mutant_hostdata.pv    card attests host-supplied fields: Q1 TRUE, Q2 TRUE, Q3 false
#
# The last two rows are why Q2 and Q3 exist: each mutant is invisible to the queries above it. The
# hostdata case is a real defect that survived a rebuild of this model and was caught in review.
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

q1='^RESULT event\(SignedObserved'
q2='^RESULT attacker\(sign\(tbsObserved'
q3='^RESULT not attacker\(sign\(tbsObserved'
sk='^RESULT not attacker\(sk'
wit='^RESULT not event\(SignedObserved'

fail=0
say_fail() { echo "FAIL: $*"; fail=1; }
run()   { proverif "$PV/$1.pv" 2>&1; }
count() { printf '%s\n' "$2" | grep -cE "$1" || true; }
# expect <label> <output> <pattern> <true|false> <description>
expect() {
  local out="$2" pat="$3" want="$4"
  [ "$(count "$pat.*is $want\." "$out")" -ge 1 ] || say_fail "$1: $5 is not $want"
}

echo ">> property5.pv: expect Q1 true, Q2 true, Q3 true, key secret"
GOOD="$(run property5)"; printf '%s\n' "$GOOD" | grep -E '^RESULT' || true
expect property5 "$GOOD" "$q1" true  "Q1 (event correspondence)"
expect property5 "$GOOD" "$q2" true  "Q2 (attacker-held signature)"
expect property5 "$GOOD" "$q3" true  "Q3 (no attacker-chosen content)"
expect property5 "$GOOD" "$sk" true  "signing-key secrecy"

echo ">> property5_reachable.pv: expect the observed-action event REACHABLE"
REACH="$(run property5_reachable)"; printf '%s\n' "$REACH" | grep -E '^RESULT' || true
# ProVerif proves the negation of a reachability query, so "is false" means a trace emitting it exists.
[ "$(count "$wit.*is false\." "$REACH")" -ge 1 ] || say_fail "(VACUITY) the observed-action event is not reachable, so property5.pv proves nothing. See docs/ASSUMPTIONS.md OF-3."

echo ">> property5_mutant.pv (host guard dropped): expect Q1 false, Q2 false, Q3 false"
MUT="$(run property5_mutant)"; printf '%s\n' "$MUT" | grep -E '^RESULT' || true
expect host-guard-mutant "$MUT" "$q1" false "Q1"
expect host-guard-mutant "$MUT" "$q2" false "Q2"
expect host-guard-mutant "$MUT" "$q3" false "Q3"

echo ">> property5_mutant_databind.pv (builder signs handset subject): expect Q1 true, Q2 false"
MUTB="$(run property5_mutant_databind)"; printf '%s\n' "$MUTB" | grep -E '^RESULT' || true
expect databind-mutant "$MUTB" "$q1" true  "Q1 (it should stay true; that is the point)"
expect databind-mutant "$MUTB" "$q2" false "Q2"

echo ">> property5_mutant_hostdata.pv (card attests host-supplied fields): expect Q1 true, Q2 true, Q3 false"
MUTH="$(run property5_mutant_hostdata)"; printf '%s\n' "$MUTH" | grep -E '^RESULT' || true
expect hostdata-mutant "$MUTH" "$q1" true  "Q1 (it should stay true; that is the point)"
expect hostdata-mutant "$MUTH" "$q2" true  "Q2 (it should stay true; that is the point)"
expect hostdata-mutant "$MUTH" "$q3" false "Q3"

[ "$fail" -eq 0 ] || exit 1
echo "OK: event reachable; all four queries hold; each of the three mutants is caught, and the last two only by the query added for it."
