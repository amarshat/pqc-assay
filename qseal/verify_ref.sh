#!/usr/bin/env bash
# Build the C reference TBS-V1 (de)serializer to LLVM bitcode and prove it equals the Cryptol model
# (qseal/model/QSEAL_TBS.cry, itself proven bijective/injective) with SAW. Exits non-zero on failure.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$HERE/.." && pwd)"

command -v saw >/dev/null 2>&1 || export PATH="$REPO/.tools/bin:$PATH"
command -v saw >/dev/null 2>&1 || { echo "FAIL: saw not found (expected on PATH or in .tools/bin)"; exit 2; }
CLANG="${CLANG:-clang}"
command -v "$CLANG" >/dev/null 2>&1 || { echo "FAIL: clang not found (set CLANG=...)"; exit 2; }

mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/tbs_v1.c" -o "$HERE/build/tbs_v1.bc"

cd "$HERE/proof"
saw tbs_v1.saw
