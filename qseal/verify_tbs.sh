#!/usr/bin/env bash
# Machine-check the Q-SEAL TBS-V1 and TBS-V2 transcript bijectivity/injectivity properties
# (cryptol + z3), including V2's pair-commitment signedness and its omission witness.
# Exits 0 only if all eight properties are Q.E.D. and none produced a counterexample.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

# Prefer the pinned toolchain if cryptol is not already on PATH.
if ! command -v cryptol >/dev/null 2>&1; then
  export PATH="$REPO/.tools/bin:$PATH"
fi
command -v cryptol >/dev/null 2>&1 || { echo "FAIL: cryptol not found (expected on PATH or in .tools/bin)"; exit 2; }

# Timings from these scripts are only meaningful with the machine and toolchain named, so print them.
echo "== $(basename "$0") on $(uname -srm), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || (grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2- | sed 's/^ //') || echo 'unknown CPU')"
echo "== toolchain: $(if command -v saw >/dev/null 2>&1; then saw --version | head -1 | sed 's/^/saw /'; else echo 'saw n/a'; fi); $(if command -v cryptol >/dev/null 2>&1; then cryptol --version | head -1; else echo 'cryptol n/a'; fi); $(if command -v proverif >/dev/null 2>&1; then proverif -help 2>&1 | head -1 | cut -d, -f1; else echo 'proverif n/a'; fi); $(${CLANG:-clang} --version | head -1)"

cd "$HERE/model"
OUT="$(cryptol -b /dev/stdin <<'EOF' 2>&1
:l QSEAL_TBS.cry
:set prover=z3
:prove roundtrip_parse_serialize
:prove roundtrip_serialize_parse
:prove serialize_injective
:l QSEAL_TBS_V2.cry
:set prover=z3
:prove roundtrip2_parse_serialize
:prove roundtrip2_serialize_parse
:prove serialize2_injective
:prove commitment_is_signed
:prove omitting_commitment_breaks_binding
EOF
)"

echo "$OUT"

QED="$(printf '%s\n' "$OUT" | grep -c 'Q.E.D.' || true)"
CEX="$(printf '%s\n' "$OUT" | grep -c 'Counterexample' || true)"

if [ "$QED" -eq 8 ] && [ "$CEX" -eq 0 ]; then
  echo "OK: TBS-V1 (3/3) + TBS-V2 incl. pair-commitment signedness (5/5), 8/8 Q.E.D."
  exit 0
fi
echo "FAIL: expected 8 Q.E.D. and 0 counterexamples; got QED=$QED CEX=$CEX"
exit 1
