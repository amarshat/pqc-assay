#!/usr/bin/env bash
# Install & PIN the toolchain. Reproducibility is the product, so pin exact versions.
#
# Verified working on: macOS 26.3.1 (Darwin 25.x), Apple Silicon (arm64), 2026-06-01.
# Re-running is idempotent: it skips a tool if the pinned version is already extracted.
#
# After running, these must succeed (checkpoint 1 of docs/ROADMAP.md):
#   "$TOOLS_DIR"/bin/saw --version
#   "$TOOLS_DIR"/bin/isabelle version
set -euo pipefail

cd "$(dirname "$0")/.."
ROOT="$(pwd)"
TOOLS_DIR="${TOOLS_DIR:-$ROOT/.tools}"          # gitignored; see /.tools/ in .gitignore
BIN_DIR="$TOOLS_DIR/bin"
DL_DIR="$TOOLS_DIR/downloads"
mkdir -p "$BIN_DIR" "$DL_DIR"

# ---------------------------------------------------------------------------
# PINNED VERSIONS  (mirror any change here into docs/ASSUMPTIONS.md)
# ---------------------------------------------------------------------------
SAW_VERSION="1.5.1"                              # first release shipping cryptol-to-isabelle
SAW_ASSET="saw-${SAW_VERSION}-macos-15-ARM64-with-solvers.tar.gz"
SAW_URL="https://github.com/GaloisInc/saw-script/releases/download/v${SAW_VERSION}/${SAW_ASSET}"

ISABELLE_VERSION="2025-2"                        # Isabelle2025-2 (Jan 2026)
ISA_ASSET="Isabelle${ISABELLE_VERSION}_macos.tar.gz"
ISA_URL="https://isabelle.in.tum.de/dist/${ISA_ASSET}"

# Bitwuzla: the abstraction-refinement SMT solver that discharges wide-domain Barrett reduction
# where eager bit-blasters (z3/cvc5/yices/abc, all bundled with SAW) stall. SAW calls it via the
# w4_unint_bitwuzla backend. Not in the SAW tarball, so pinned separately.
BITWUZLA_VERSION="0.9.1"
BITWUZLA_ASSET="Bitwuzla-macOS-arm64-static.zip"
BITWUZLA_URL="https://github.com/bitwuzla/bitwuzla/releases/download/${BITWUZLA_VERSION}/${BITWUZLA_ASSET}"

# ProVerif: symbolic protocol verifier for the Q-SEAL reachability property (section 16 property 5).
# Built from source (CLI only), because the opam package pulls a GTK2 GUI dependency we do not need.
# Needs an OCaml toolchain; skip with SKIP_PROVERIF=1 (the SAW/Cryptol/Isabelle legs do not need it).
PROVERIF_VERSION="2.05"
PROVERIF_URL="https://bblanche.gitlabpages.inria.fr/proverif/proverif${PROVERIF_VERSION}.tar.gz"
PROVERIF_SHA256="4871f53c32ab4a04669a060c4886ba5d9080496963fb980a9a62d2c429ceabc4"

# clang: we deliberately use the system Apple clang (recorded in ASSUMPTIONS.md), NOT a vendored one.
EXPECTED_CLANG="Apple clang version 17.0.0 (clang-1700.0.13.5)"

# ---------------------------------------------------------------------------
fetch() {  # fetch <url> <dest-file>
  local url="$1" dest="$2"
  if [[ -f "$dest" ]]; then echo ">> cached: $dest"; return; fi
  echo ">> downloading $url"
  # Robust against flaky mirrors (large Isabelle/AFP tarballs): retry all transient errors and
  # resume partial transfers (-C -) rather than restarting the whole download on a reset.
  curl -fL --retry 8 --retry-all-errors --retry-delay 5 --connect-timeout 30 \
       -C - -o "$dest.partial" "$url"
  mv "$dest.partial" "$dest"
}

link() {   # symlink <target> into BIN_DIR
  local target="$1" name="$2"
  ln -sf "$target" "$BIN_DIR/$name"
}

# --- SAW + Cryptol + cryptol-to-isabelle (Galois) ---------------------------
SAW_HOME="$TOOLS_DIR/saw-${SAW_VERSION}"
if [[ ! -x "$SAW_HOME/bin/saw" ]]; then
  fetch "$SAW_URL" "$DL_DIR/$SAW_ASSET"
  echo ">> extracting SAW ${SAW_VERSION}"
  rm -rf "$SAW_HOME" && mkdir -p "$SAW_HOME"
  tar -xzf "$DL_DIR/$SAW_ASSET" -C "$SAW_HOME" --strip-components=1
fi
for b in saw cryptol cryptol-to-isabelle abc z3 yices yices-smt2 cvc4 cvc5; do
  [[ -e "$SAW_HOME/bin/$b" ]] && link "$SAW_HOME/bin/$b" "$b"
done

# macOS arm64 gotchas, both of which cause a silent "Killed: 9" on exec:
#   (1) downloaded files carry com.apple.quarantine; an ad-hoc-signed (non-notarized)
#       binary that is quarantined is SIGKILLed by Gatekeeper. Strip it.
#   (2) every arm64 binary must carry at least an ad-hoc signature. Galois tarballs are
#       signed ad-hoc already, but re-sign defensively in case extraction altered them.
xattr -dr com.apple.quarantine "$SAW_HOME" 2>/dev/null || true
if command -v codesign >/dev/null; then
  find "$SAW_HOME/bin" -type f -exec sh -c 'file "$1" | grep -q Mach-O' _ {} \; \
    -exec codesign --force --sign - {} \; 2>/dev/null || true
fi

# --- Bitwuzla (pinned separately; not in the SAW tarball) -------------------
BITWUZLA_HOME="$TOOLS_DIR/bitwuzla-${BITWUZLA_VERSION}"
if [[ ! -x "$BITWUZLA_HOME/bin/bitwuzla" ]]; then
  fetch "$BITWUZLA_URL" "$DL_DIR/$BITWUZLA_ASSET"
  echo ">> extracting bitwuzla ${BITWUZLA_VERSION}"
  rm -rf "$BITWUZLA_HOME" && mkdir -p "$BITWUZLA_HOME"
  unzip -o -q "$DL_DIR/$BITWUZLA_ASSET" -d "$BITWUZLA_HOME"
  # the zip nests a Bitwuzla-*-static/bin/bitwuzla; flatten to $BITWUZLA_HOME/bin/bitwuzla
  found="$(find "$BITWUZLA_HOME" -type f -name bitwuzla | head -1)"
  mkdir -p "$BITWUZLA_HOME/bin"; [[ "$found" != "$BITWUZLA_HOME/bin/bitwuzla" ]] && cp "$found" "$BITWUZLA_HOME/bin/bitwuzla"
fi
link "$BITWUZLA_HOME/bin/bitwuzla" "bitwuzla"
xattr -dr com.apple.quarantine "$BITWUZLA_HOME" 2>/dev/null || true
if command -v codesign >/dev/null; then
  codesign --force --sign - "$BITWUZLA_HOME/bin/bitwuzla" 2>/dev/null || true
fi

# --- ProVerif (Q-SEAL reachability leg; optional, needs OCaml) ---------------
# Set SKIP_PROVERIF=1 to skip. Otherwise build from source IF an OCaml toolchain is on PATH; the opam
# package's GTK2 GUI dependency is not needed, so we build the CLI directly.
if [[ -z "${SKIP_PROVERIF:-}" ]]; then
  PROVERIF_HOME="$TOOLS_DIR/proverif-${PROVERIF_VERSION}"
  if [[ ! -x "$BIN_DIR/proverif" ]]; then
    if command -v ocamlfind >/dev/null 2>&1; then
      fetch "$PROVERIF_URL" "$DL_DIR/proverif${PROVERIF_VERSION}.tar.gz"
      got="$(shasum -a 256 "$DL_DIR/proverif${PROVERIF_VERSION}.tar.gz" | awk '{print $1}')"
      if [[ "$got" != "$PROVERIF_SHA256" ]]; then
        echo "!! proverif tarball sha256 mismatch: got $got, expected $PROVERIF_SHA256" >&2
        exit 1
      fi
      echo ">> building proverif ${PROVERIF_VERSION} from source (CLI only, no GTK)"
      rm -rf "$PROVERIF_HOME" && mkdir -p "$PROVERIF_HOME"
      tar -xzf "$DL_DIR/proverif${PROVERIF_VERSION}.tar.gz" -C "$PROVERIF_HOME" --strip-components=1
      # ./build exits 2 when the lablgtk GUI leg fails, which is expected here: we do not install GTK2
      # and do not use proverif_interact. The CLI binary is still produced, so judge on the binary.
      ( cd "$PROVERIF_HOME" && ./build ) || echo ">> proverif ./build returned non-zero (expected: GUI leg)"
      if [[ ! -x "$PROVERIF_HOME/proverif" ]]; then
        echo "!! proverif CLI was not produced by ./build" >&2
        exit 1
      fi
      link "$PROVERIF_HOME/proverif" "proverif"
      "$PROVERIF_HOME/proverif" -help | head -1
    else
      echo ">> SKIP: proverif needs an OCaml toolchain (ocamlfind not found). Install opam + ocaml"
      echo "         4.14.1 then re-run, or set SKIP_PROVERIF=1. See qseal/proof/proverif/README.md."
    fi
  fi
else
  echo ">> SKIP_PROVERIF set — skipping proverif (Q-SEAL reachability leg)"
fi

# --- Isabelle ---------------------------------------------------------------
# Set SKIP_ISABELLE=1 to skip the (large, ~1.6GB) Isabelle download — e.g. CI that only runs
# `make saw` does not need it.
if [[ -z "${SKIP_ISABELLE:-}" ]]; then
  ISA_HOME="$TOOLS_DIR/Isabelle${ISABELLE_VERSION}"
  if [[ ! -x "$ISA_HOME/bin/isabelle" ]] && [[ -z "$(find "$ISA_HOME" -name isabelle -path '*/bin/*' 2>/dev/null | head -1)" ]]; then
    fetch "$ISA_URL" "$DL_DIR/$ISA_ASSET"
    echo ">> extracting Isabelle ${ISABELLE_VERSION}"
    rm -rf "$ISA_HOME" && mkdir -p "$ISA_HOME"
    # macOS tarball unpacks to an .app bundle; --strip-components flattens it to ISA_HOME.
    tar -xzf "$DL_DIR/$ISA_ASSET" -C "$ISA_HOME" --strip-components=1
  fi
  xattr -dr com.apple.quarantine "$ISA_HOME" 2>/dev/null || true
  # The CLI launcher lives at <app>/bin/isabelle (or Contents/Resources/.../bin/isabelle).
  ISA_BIN="$(find "$ISA_HOME" -type f -name isabelle -path '*/bin/*' | head -1 || true)"
  [[ -n "$ISA_BIN" ]] && link "$ISA_BIN" "isabelle"
else
  echo ">> SKIP_ISABELLE set — skipping Isabelle install"
fi

# --- clang (system) ---------------------------------------------------------
if ! clang --version | grep -qF "$EXPECTED_CLANG"; then
  echo "!! WARNING: system clang != pinned '$EXPECTED_CLANG' — record the delta in ASSUMPTIONS.md" >&2
fi

# ---------------------------------------------------------------------------
echo
echo ">> toolchain installed under $TOOLS_DIR"
echo ">> add to PATH for this shell:   export PATH=\"$BIN_DIR:\$PATH\""
echo ">> verifying versions:"
"$BIN_DIR/saw" --version || { echo "!! saw failed to run" >&2; exit 1; }
if [[ -z "${SKIP_ISABELLE:-}" ]]; then
  "$BIN_DIR/isabelle" version || { echo "!! isabelle failed to run" >&2; exit 1; }
fi
clang --version | head -1
echo ">> setup complete."
