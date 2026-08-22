#!/usr/bin/env bash
# Q-SEAL HYB-1 hybrid acceptance (section 16 property 3): with the ECDSA/ML-DSA verifiers uninterpreted,
# SAW proves qseal_hybrid_accept requires BOTH signatures over the same transcript, and the downgrade
# variant (accept on either) is rejected by the same spec. Exits non-zero on failure.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

command -v saw >/dev/null 2>&1 || export PATH="$REPO/.tools/bin:$PATH"
command -v saw >/dev/null 2>&1 || { echo "FAIL: saw not found"; exit 2; }
CLANG="${CLANG:-clang}"
command -v "$CLANG" >/dev/null 2>&1 || { echo "FAIL: clang not found (set CLANG=...)"; exit 2; }

# Timings from these scripts are only meaningful with the machine and toolchain named, so print them.
echo "== $(basename "$0") on $(uname -srm), $(sysctl -n machdep.cpu.brand_string 2>/dev/null || (grep -m1 'model name' /proc/cpuinfo 2>/dev/null | cut -d: -f2- | sed 's/^ //') || echo 'unknown CPU')"
echo "== toolchain: $(if command -v saw >/dev/null 2>&1; then saw --version | head -1 | sed 's/^/saw /'; else echo 'saw n/a'; fi); $(if command -v cryptol >/dev/null 2>&1; then cryptol --version | head -1; else echo 'cryptol n/a'; fi); $(if command -v proverif >/dev/null 2>&1; then proverif -help 2>&1 | head -1 | cut -d, -f1; else echo 'proverif n/a'; fi); $(${CLANG:-clang} --version | head -1)"

mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/hybrid.c" -o "$HERE/build/hybrid.bc"

cd "$HERE/proof"
saw hybrid.saw
