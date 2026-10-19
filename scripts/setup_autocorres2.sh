#!/usr/bin/env bash
# Prerequisite for `make ac2` (the second C semantics: AutoCorres2 on the vendored PQClean C).
#
# AutoCorres2 (in the pinned AFP, afp-2026-06-05) calls clang to compute record layouts, at a
# hard-coded default path /usr/bin/clang (c-parser/isar_install.ML, config clang_path). Its own
# session installs a test file using C23 [[attributes]], which Apple clang 14 rejects. We do not
# edit the pinned AFP. Instead:
#   - .tools/afp-ac2/ mirrors the AFP thys directory with symlinks, except AutoCorres2, which is a
#     copy whose only change is the default clang_path (checked below with diff);
#   - .tools/isa-ac2-home/ is a separate Isabelle user home (USER_HOME) whose ROOTS lists the
#     mirror, the SAW Cryptol component and spec/isabelle, so the main ~/.isabelle setup and its
#     heaps are untouched.
# Then the AutoCorres2 heap is built there (about 30 min).
#
# AC2_CLANG: a clang >= 15. Default: Homebrew llvm@22.
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
TOOLS_DIR="$ROOT_DIR/.tools"
ISABELLE="$TOOLS_DIR/bin/isabelle"
AC2_CLANG="${AC2_CLANG:-/opt/homebrew/opt/llvm@22/bin/clang}"

"$AC2_CLANG" --version | head -1
AFP_DIR="$(find "$TOOLS_DIR" -maxdepth 1 -type d -name 'afp-2*' | head -1)"
[[ -d "$AFP_DIR/thys/AutoCorres2" ]] || { echo "AFP with AutoCorres2 not found; run scripts/setup_isabelle_cryptol.sh"; exit 1; }
SAW_ISA_COMPONENT="$(find "$TOOLS_DIR" -maxdepth 3 -type d -path '*saw-*/lib/isabelle' | head -1)"

MIRROR="$TOOLS_DIR/afp-ac2"
rm -rf "$MIRROR"; mkdir -p "$MIRROR"
for d in "$AFP_DIR"/thys/*; do
  b="$(basename "$d")"
  [[ "$b" == AutoCorres2 ]] && continue
  ln -s "$d" "$MIRROR/$b"
done
cp -R "$AFP_DIR/thys/AutoCorres2" "$MIRROR/AutoCorres2"
sed -i.bak "s#(K \"/usr/bin/clang\")#(K \"$AC2_CLANG\")#" "$MIRROR/AutoCorres2/c-parser/isar_install.ML"
rm "$MIRROR/AutoCorres2/c-parser/isar_install.ML.bak"
echo ">> the only change to the AFP copy:"
diff -r "$AFP_DIR/thys/AutoCorres2" "$MIRROR/AutoCorres2" || true

HOME_DIR="$TOOLS_DIR/isa-ac2-home/.isabelle/Isabelle2025-2"
mkdir -p "$HOME_DIR"
printf '%s\n' "$MIRROR" "$SAW_ISA_COMPONENT" "$ROOT_DIR/spec/isabelle" > "$HOME_DIR/ROOTS"

echo ">> building the AutoCorres2 heap under USER_HOME=$TOOLS_DIR/isa-ac2-home (about 30 min)"
USER_HOME="$TOOLS_DIR/isa-ac2-home" "$ISABELLE" build -o timeout_scale="${ISABELLE_TIMEOUT_SCALE:-10}" -b AutoCorres2
echo ">> DONE: make ac2 can run."
