#!/bin/sh
# Preprocess the vendored PQClean C (target/pqclean, unchanged) for AutoCorres2's C-parser:
#   clang -E -P: comments dropped, line markers dropped; <stdint.h>/<stddef.h> come from the
#   typedef-only shim/ so the C-parser never reads the macOS SDK headers.
# Why not let AutoCorres2 run cpp itself: it calls `cpp -CC`, which keeps comments inside macro
# expansions. params.h has `#define QINV 58728449 // q^(-1) mod 2^32`, so the `//` lands mid-
# statement and swallows the rest of it. /usr/bin/cpp on macOS has the same effect (traditional
# mode), hence clang -E.
# Usage: gen.sh <clang> <name>...   writes pp_<name>.c next to this script
set -eu
here="$(cd "$(dirname "$0")" && pwd)"
clang="$1"; shift
for f in "$@"; do
  "$clang" -E -P -I "$here/shim" -I "$here/../../target/pqclean" \
    "$here/../../target/pqclean/$f.c" > "$here/pp_$f.c"
done
