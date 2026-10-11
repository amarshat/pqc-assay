#!/usr/bin/env bash
# Check that the default and -fwrapv builds of the vendored C differ only in overflow flags.
#
# mldsa_ntt.saw proves functional equality on the -fwrapv bitcode; poly_nsw.saw proves on the
# default bitcode that no `nsw` operation overflows. Those two combine only if the builds are
# otherwise the same program. This compiles both to textual IR with the flags build_bitcode.sh
# uses, strips `nsw` and `inbounds` from both, and fails if anything else differs. It compiles fresh
# IR rather than disassembling build/*.bc (there is no llvm-dis in the toolchain), so it relies on
# clang being deterministic for the same flags.
# Usage: ./scripts/check_wrapv_diff.sh <target_dir>
set -euo pipefail

TARGET_DIR="${1:?need target dir}"
CLANG="${CLANG:-clang}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

printf '#include "reduce.c"\n#include "ntt.c"\n' > "$TMP/c.c"
if [ -f "$TARGET_DIR/poly.c" ]; then printf '#include "poly.c"\n' >> "$TMP/c.c"; fi
if [ -f "$TARGET_DIR/polyvec.c" ]; then printf '#include "polyvec.c"\n' >> "$TMP/c.c"; fi

"$CLANG" -S -emit-llvm -O0 -g -I "$TARGET_DIR" "$TMP/c.c" -o "$TMP/default.ll"
"$CLANG" -S -emit-llvm -O0 -g -fwrapv -I "$TARGET_DIR" "$TMP/c.c" -o "$TMP/wrapv.ll"

n_nsw=$(grep -c ' nsw' "$TMP/default.ll" || true)
strip() { sed -E 's/ nsw//g; s/getelementptr inbounds/getelementptr/g' "$1"; }
if ! diff <(strip "$TMP/default.ll") <(strip "$TMP/wrapv.ll") > "$TMP/diff.txt"; then
  echo "FAIL: default and -fwrapv IR differ beyond nsw/inbounds:"
  head -40 "$TMP/diff.txt"
  exit 1
fi
[ "$n_nsw" -gt 0 ] || { echo "FAIL: default IR has no nsw flags; the check is not testing anything"; exit 1; }
echo "OK: default and -fwrapv IR identical up to nsw/inbounds ($n_nsw nsw operations in the default build)"
