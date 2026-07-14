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

mkdir -p "$HERE/build"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/tbs_v1.c" -o "$HERE/build/tbs_v1.bc"
"$CLANG" -c -emit-llvm -O0 -g -I "$HERE/ref" "$HERE/ref/tbs_v2.c" -o "$HERE/build/tbs_v2.bc"

cd "$HERE/proof"
saw tbs_v1.saw
saw tbs_v2.saw
