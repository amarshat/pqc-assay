#!/usr/bin/env bash
# Composition-soundness gate for EVERY cryptol-to-isabelle lift in the tree.
#
# The chain C == Cryptol (SAW) composed with model == spec (Isabelle) is only sound if the Isabelle
# theory the proofs reason about really is the lift of the Cryptol model SAW checked the C against.
# scripts/lift_check.sh enforced that for MLDSA_NTT and lift_check_barrett.sh for the Barrett lift,
# which left two lifts ungated: the ML-KEM model and the FIPS-204 reference transcription. Both were
# in sync when this script was written, so the gap was latent rather than live, but "currently in
# sync" is not a check.
#
# Adding a lift without adding it here is itself an error: the manifest is compared against every
# theory in the tree that cryptol-to-isabelle could have produced.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
export PATH="$ROOT/.tools/bin:$PATH"

# committed_theory <TAB> cryptol_source <TAB> generated_name (optional, when the commit renames it)
# Barrett_Lift is the one rename: cryptol-to-isabelle emits barrett_bridge.thy, and the committed
# copy is renamed to dodge a clash on macOS's case-insensitive filesystem. The theory-name line is
# the only sanctioned edit, and it is normalized before comparing.
MANIFEST="
spec/isabelle/MLDSA_NTT.thy	model/cryptol/MLDSA_NTT.cry
spec/isabelle/kem/MLKEM_NTT.thy	model/cryptol/MLKEM_NTT.cry
spec/isabelle/tier2/fips204_ntt_lift.thy	implementations/rustcrypto-ml-dsa/proof/ntt/fips204_ntt_lift.cry
spec/isabelle/tier2/barrett/Barrett_Lift.thy	implementations/rustcrypto-ml-dsa/proof/ntt/barrett_bridge.cry	barrett_bridge.thy
"

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
rc=0

while IFS=$'\t' read -r thy cry genname; do
  [ -z "$thy" ] && continue
  if [ ! -f "$thy" ]; then echo "!! manifest names a missing theory: $thy" >&2; rc=1; continue; fi
  if [ ! -f "$cry" ]; then echo "!! manifest names a missing Cryptol source: $cry" >&2; rc=1; continue; fi
  d="$TMP/$(basename "$thy" .thy)"; mkdir -p "$d"
  if ! cryptol-to-isabelle -s "$cry" -d "$d" --all-modules >/dev/null 2>&1; then
    echo "!! cryptol-to-isabelle failed on $cry" >&2; rc=1; continue
  fi
  gen="$d/${genname:-$(basename "$thy")}"
  if [ ! -f "$gen" ]; then echo "!! $cry did not produce $(basename "$thy")" >&2; rc=1; continue; fi
  if [ -n "${genname:-}" ]; then
    # normalize the one sanctioned edit: the theory-name line
    want="$(basename "$thy" .thy)"; have="$(basename "$genname" .thy)"
    sed "1s/^theory \"$have\"$/theory $want/" "$gen" > "$gen.norm" && gen="$gen.norm"
  fi
  if diff -q "$thy" "$gen" >/dev/null; then
    printf '  %-46s == lift(%s)\n' "$thy" "$cry"
  else
    echo "!! OUT OF SYNC: $thy != cryptol-to-isabelle($cry)" >&2
    diff -u "$thy" "$gen" | head -20 >&2
    rc=1
  fi
done <<< "$MANIFEST"

# Any lifted theory not in the manifest is an ungated lift.
listed="$(awk -F'\t' 'NF{print $1}' <<< "$MANIFEST" | sort)"
found="$(grep -rl 'cryptol_definition' spec/isabelle --include='*.thy' 2>/dev/null | sort || true)"
missing="$(comm -13 <(echo "$listed") <(echo "$found") || true)"
if [ -n "$missing" ]; then
  echo "!! these theories contain cryptol_definition but are not in the manifest, so they are ungated:" >&2
  echo "$missing" | sed 's/^/     /' >&2
  rc=1
fi

[ "$rc" -eq 0 ] && echo ">> lift-check-all OK: every lifted theory matches its Cryptol source"
exit $rc
