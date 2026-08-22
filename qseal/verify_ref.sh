#!/usr/bin/env bash
# Build the C reference TBS-V1 and TBS-V2 (de)serializers to LLVM bitcode and prove each equals its
# Cryptol model (QSEAL_TBS.cry / QSEAL_TBS_V2.cry, themselves proven bijective/injective) with SAW.
# Exits non-zero on failure.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

command -v saw >/dev/null 2>&1 || export PATH="$REPO/.tools/bin:$PATH"
command -v saw >/dev/null 2>&1 || { echo "FAIL: saw not found (expected on PATH or in .tools/bin)"; exit 2; }
CLANG="${CLANG:-clang}"
command -v "$CLANG" >/dev/null 2>&1 || { echo "FAIL: clang not found (set CLANG=...)"; exit 2; }

# Timings from these scripts are only meaningful with the machine and toolchain named, so print them.
echo "== $(basename "$0") on $(uname -srm), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || (grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2- | sed 's/^ //') || echo 'unknown CPU')"
echo "== toolchain: $(if command -v saw >/dev/null 2>&1; then saw --version | head -1 | sed 's/^/saw /'; else echo 'saw n/a'; fi); $(if command -v cryptol >/dev/null 2>&1; then cryptol --version | head -1; else echo 'cryptol n/a'; fi); $(if command -v proverif >/dev/null 2>&1; then proverif -help 2>&1 | head -1 | cut -d, -f1; else echo 'proverif n/a'; fi); $(${CLANG:-clang} --version | head -1)"

mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/tbs_v1.c" -o "$HERE/build/tbs_v1.bc"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/tbs_v2.c" -o "$HERE/build/tbs_v2.bc"

cd "$HERE/proof"

# Count the outcomes rather than trusting the exit status: six obligations must discharge (serialize,
# parse-accept and parse-reject for each of V1 and V2) and all six injected mutants must be rejected.
OUT="$(saw tbs_v1.saw; saw tbs_v2.saw)"
echo "$OUT"
OK="$(printf '%s\n' "$OUT" | grep -c '^VERIFIED:' || true)"
MUT="$(printf '%s\n' "$OUT" | grep -c '^MUTATION CAUGHT:' || true)"
if [ "$OK" -ne 6 ] || [ "$MUT" -ne 6 ]; then
  echo "FAIL: expected 6 VERIFIED + 6 MUTATION CAUGHT; got VERIFIED=$OK MUTATION=$MUT"
  exit 1
fi
echo "OK: 6 obligations discharged, 6 injected mutants rejected"
