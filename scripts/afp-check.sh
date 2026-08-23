#!/usr/bin/env bash
# Mechanical check of an AFP entry against the rules on https://isa-afp.org/submission/.
#
# The judgment-call rules (Isar style over apply scripts, comments on slow steps, whether the abstract
# and citations are adequate) are not checkable here; ~/.claude/agents/afp-referee covers those. What
# this does is make the countable rules countable, so nothing on the list is left to memory.
#
# Usage: scripts/afp-check.sh [entry-dir]   (default afp/MLDSA_Reduce)
set -uo pipefail

ENTRY="${1:-afp/MLDSA_Reduce}"
NAME="$(basename "$ENTRY")"
REPO="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO"
fail=0
ok()  { printf '  ok    %s\n' "$*"; }
bad() { printf '  FAIL  %s\n' "$*"; fail=1; }

echo "== AFP rule check: $NAME =="

# --- structure -------------------------------------------------------------------------------------
[ -f "$ENTRY/ROOT" ] || bad "no ROOT file"
grep -q '^chapter AFP' "$ENTRY/ROOT" && ok "ROOT declares chapter AFP" \
  || bad "ROOT must start with 'chapter AFP'"

if grep -qE "^session +\"?$NAME\"? " "$ENTRY/ROOT"; then
  ok "session is named after the entry folder ($NAME)"
else
  bad "the session must be named after the entry folder ($NAME)"
fi

nsess=$(grep -c '^session ' "$ENTRY/ROOT")
[ "$nsess" -eq 1 ] && ok "exactly one session" || echo "  note  $nsess sessions; AFP expects one named after the entry"

# timeout must be present and divisible by 300
to=$(grep -oE 'timeout *= *[0-9]+' "$ENTRY/ROOT" | grep -oE '[0-9]+' | head -1)
if [ -z "$to" ]; then
  bad "no timeout in ROOT options; AFP requires one"
elif [ $((to % 300)) -ne 0 ]; then
  bad "timeout $to is not divisible by 300"
else
  ok "timeout $to is divisible by 300"
fi

# --- prohibited commands ---------------------------------------------------------------------------
for cmd in sorry back sledgehammer smt_oracle; do
  n=$(grep -rhoE "\\b$cmd\\b" "$ENTRY"/*.thy 2>/dev/null | wc -l | tr -d ' ')
  [ "$n" -eq 0 ] && ok "no $cmd" || bad "$n use(s) of $cmd"
done

# nitpick / quickcheck / nunchaku need an expect parameter
for cmd in nitpick quickcheck nunchaku; do
  while IFS= read -r line; do
    [ -z "$line" ] && continue
    printf '%s' "$line" | grep -q 'expect' || bad "$cmd without an expect parameter: $line"
  done < <(grep -rhE "^[[:space:]]*$cmd" "$ENTRY"/*.thy 2>/dev/null)
done
ok "nitpick/quickcheck/nunchaku either absent or carry expect"

# --- style rules that can be counted ---------------------------------------------------------------
# attributes such as [simp] belong on named lemmas only
if grep -rnE '^[[:space:]]*(lemma|theorem|corollary)[[:space:]]*\[' "$ENTRY"/*.thy >/dev/null 2>&1; then
  grep -rnE '^[[:space:]]*(lemma|theorem|corollary)[[:space:]]*\[' "$ENTRY"/*.thy | sed 's/^/        /'
  bad "unnamed lemma carrying attributes; only named lemmas may carry [simp] and friends"
else
  ok "no unnamed lemma carries attributes"
fi

# Isabelle-generated names must not appear in instantiations
gen=$(grep -rnE '\b(of|where)\b[^"]*\b[a-z][a-z]\b' "$ENTRY"/*.thy 2>/dev/null \
      | grep -oE '\b(xa|xb|ya|yb|za|zb|aa|ab|ba|bb)\b' | sort -u | tr '\n' ' ')
[ -z "$gen" ] && ok "no Isabelle-generated names (xa, ya, ...) in instantiations" \
  || bad "generated names used in instantiations: $gen"

# apply-style usage, reported rather than gated: AFP prefers structured Isar
ap=$(grep -rhcE '^[[:space:]]*apply' "$ENTRY"/*.thy 2>/dev/null | paste -sd+ - | bc)
isar=$(grep -rhcE '^[[:space:]]*(proof|next|qed|have|show|obtain)\b' "$ENTRY"/*.thy 2>/dev/null | paste -sd+ - | bc)
echo "  note  $ap apply step(s) against $isar structured step(s); AFP prefers Isar"

# --- citations and metadata ------------------------------------------------------------------------
if [ -f "$ENTRY/document/root.tex" ]; then
  c=$(grep -c '\\cite{' "$ENTRY/document/root.tex")
  [ "$c" -ge 1 ] && ok "$c citation(s) in root.tex" || bad "no \\cite in root.tex; AFP requires sources to be cited"
  grep -q '\\bibliography' "$ENTRY/document/root.tex" && [ -f "$ENTRY/document/root.bib" ] \
    && ok "bibliography present" || bad "root.tex has no bibliography or root.bib is missing"
else
  bad "no document/root.tex"
fi

meta="$(dirname "$ENTRY")/$NAME.toml"
if [ -f "$meta" ]; then
  for field in title date topics abstract license; do
    grep -q "^$field" "$meta" && ok "metadata has $field" || bad "metadata is missing $field"
  done
  lic=$(grep -oE '^license *= *"[a-z]+"' "$meta" | grep -oE '"[a-z]+"' | tr -d '"')
  if [ "$lic" = "lgpl" ]; then
    for f in "$ENTRY"/*.thy; do
      grep -q 'License: LGPL' "$f" || bad "LGPL entry: $f lacks the 'License: LGPL' header"
    done
  else
    ok "license is $lic (no per-file header required)"
  fi
else
  bad "no metadata file at $meta"
fi

# --- the build, with AFP's own options ---------------------------------------------------------------
if command -v isabelle >/dev/null 2>&1; then
  AFP_THYS=$(find "$REPO/.tools" -maxdepth 2 -type d -name thys -path '*afp*' | head -1)
  echo "  ..    building with AFP's options (this is the one that matters)"
  if isabelle build -v -o browser_info -o "document=pdf" \
       -o "document_variants=document:outline=/proof,/ML" \
       -d "$ENTRY" ${AFP_THYS:+-d "$AFP_THYS"} -c "$NAME" > /tmp/afp_check_build.log 2>&1; then
    ok "isabelle build exits 0 with AFP's build options, document included"
  else
    bad "isabelle build FAILED with AFP's options; see /tmp/afp_check_build.log"
    tail -5 /tmp/afp_check_build.log | sed 's/^/        /'
  fi
else
  bad "isabelle not on PATH; the build check is the one that matters and it did not run"
fi

echo
[ "$fail" -eq 0 ] && echo "afp-check OK" || echo "afp-check FAILED"
exit "$fail"
