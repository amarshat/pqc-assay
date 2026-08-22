#!/usr/bin/env bash
# Q-SEAL section 16 property 5: PROFILE_ACTION_OBSERVED (assertion type 0x04) must not be obtainable
# through a host-exposed APDU path. A safety property over the command surface, so it is checked in
# ProVerif (Dolev-Yao) rather than in the SAW/Cryptol pipeline. Four runs, all gated:
#   1. property5.pv                   three queries, all TRUE:
#                                       Q1 every observed assertion follows an internal event
#                                       Q2 every observed signature the attacker holds follows one
#                                       SK the signing key never leaks
#   2. property5_reachable.pv         the observed-action event must be REACHABLE. Without this the
#                                     positive results above prove nothing, which is how an earlier
#                                     version of this model came to be vacuous (ASSUMPTIONS.md OF-3).
#   3. property5_mutant.pv            host guard dropped: Q1 and Q2 must both be FALSE.
#   4. property5_mutant_databind.pv   builder signs handset-supplied data: Q1 stays TRUE and Q2 must be
#                                     FALSE. That asymmetry is why Q2 exists.
# Exits 0 only if all four match.
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

q1='^RESULT event\(SignedObserved'         # correspondence over applet events
q2='^RESULT attacker\(sign\(tbsObserved'   # correspondence over what the attacker holds
sk='^RESULT not attacker\(sk'              # signing-key secrecy
wit='^RESULT not event\(SignedObserved'    # reachability witness

fail=0
say_fail() { echo "FAIL: $*"; fail=1; }
run()   { proverif "$PV/$1.pv" 2>&1; }
count() { printf '%s\n' "$2" | grep -cE "$1" || true; }

echo ">> property5.pv: expect Q1 true, Q2 true, key secret"
GOOD="$(run property5)"; printf '%s\n' "$GOOD" | grep -E '^RESULT' || true
[ "$(count "$q1.*is true\." "$GOOD")" -eq 1 ] || say_fail "property5.pv Q1 (event correspondence) is not true"
[ "$(count "$q2.*is true\." "$GOOD")" -eq 1 ] || say_fail "property5.pv Q2 (attacker-held signature) is not true"
[ "$(count "$sk.*is true\." "$GOOD")" -eq 1 ] || say_fail "property5.pv signing key is not secret"

echo ">> property5_reachable.pv: expect the observed-action event REACHABLE"
REACH="$(run property5_reachable)"; printf '%s\n' "$REACH" | grep -E '^RESULT' || true
# ProVerif proves the negation of a reachability query, so "is false" here means a trace emitting the
# event exists. A "true" means the honest path is dead and property5.pv proves nothing.
[ "$(count "$wit.*is false\." "$REACH")" -ge 1 ] || say_fail "(VACUITY) the observed-action event is not reachable, so property5.pv proves nothing. See docs/ASSUMPTIONS.md OF-3."

echo ">> property5_mutant.pv (host guard dropped): expect Q1 false, Q2 false"
MUT="$(run property5_mutant)"; printf '%s\n' "$MUT" | grep -E '^RESULT' || true
[ "$(count "$q1.*is false\." "$MUT")" -eq 1 ] || say_fail "the host-guard mutant is not caught by Q1"
[ "$(count "$q2.*is false\." "$MUT")" -eq 1 ] || say_fail "the host-guard mutant is not caught by Q2"

echo ">> property5_mutant_databind.pv (builder signs handset data): expect Q1 true, Q2 false"
MUTB="$(run property5_mutant_databind)"; printf '%s\n' "$MUTB" | grep -E '^RESULT' || true
[ "$(count "$q1.*is true\." "$MUTB")" -eq 1 ]  || say_fail "the data-binding mutant unexpectedly breaks Q1"
[ "$(count "$q2.*is false\." "$MUTB")" -eq 1 ] || say_fail "the data-binding mutant is not caught by Q2"

[ "$fail" -eq 0 ] || exit 1
echo "OK: observed-action event reachable; both correspondences hold; the host-guard mutant breaks both, the data-binding mutant breaks the attacker-side one."
