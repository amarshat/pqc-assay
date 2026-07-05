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

mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/hybrid.c" -o "$HERE/build/hybrid.bc"

cd "$HERE/proof"
saw hybrid.saw
