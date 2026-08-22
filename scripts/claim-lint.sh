#!/usr/bin/env bash
# Mechanical version of the standing pre-submission review checklist (kept outside this repo). These
# are the defect
# classes that got past this project's own reviews and had to be found by hand: a proof with no
# non-vacuity guard, a symbolic model whose events cannot fire, a comment citing a path that does not
# exist. Cheap enough to run every time.
# Exits non-zero if any check fails.
set -uo pipefail

REPO="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO"
fail=0
note() { printf '%s\n' "$*"; }
bad()  { printf 'FAIL: %s\n' "$*"; fail=1; }

note "== 1. every SAW obligation has a mutant paired to the SAME spec =="
# Counting `fails` guards per FILE is not enough: a file can hold three guards that all target one spec
# while another spec in the same file carries none. Pair them by spec name, and ignore comment lines,
# which an earlier version of this check counted as obligations.
for f in qseal/proof/*.saw cve-anchor/proof/*.saw; do
  [ -e "$f" ] || continue
  while read -r spec nobl nguard; do
    [ -z "$spec" ] && continue
    printf '  %-24s %-22s obligations=%s mutants=%s\n' "$(basename "$f")" "$spec" "$nobl" "$nguard"
    [ "$nobl" -eq 0 ] && continue
    [ "$nguard" -ge 1 ] || bad "$f: $spec has $nobl obligation(s) and no 'fails (llvm_verify ... $spec ...)' paired to it"
  done <<EOF
$(awk '
  /^[[:space:]]*\/\// { next }
  /llvm_verify/ {
    spec = ""
    n = split($0, toks, /[^A-Za-z0-9_]/)
    for (i = 1; i <= n; i++) if (toks[i] ~ /_spec$/) spec = toks[i]
    if (spec == "") next
    if ($0 ~ /fails[[:space:]]*\(/) guards[spec]++; else obl[spec]++
    seen[spec] = 1
  }
  END { for (s in seen) printf "%s %d %d\n", s, obl[s] + 0, guards[s] + 0 }
' "$f")
EOF
done

note "== 2. every ProVerif model has a reachability witness =="
for f in qseal/proof/proverif/*.pv; do
  case "$(basename "$f")" in *_reachable.pv|*_mutant*.pv) continue;; esac
  base="${f%.pv}"
  if [ -f "${base}_reachable.pv" ]; then
    printf '  %-28s witness present\n' "$(basename "$f")"
  else
    bad "$f has no $(basename "${base}")_reachable.pv witness; a query whose antecedent cannot fire holds vacuously (OF-3)"
  fi
done
for f in qseal/proof/proverif/*.pv; do
  # a private channel that is never written makes every process guarded on it dead
  for ch in $(grep -oE 'free [a-zA-Z_][a-zA-Z0-9_]*: channel \[private\]' "$f" | awk '{print $2}' | tr -d ':'); do
    if grep -q "in($ch," "$f" && ! grep -q "out($ch," "$f"; then
      bad "$f: private channel '$ch' is read but never written, so the reading process is dead code (OF-3)"
    fi
  done
done
grep -q 'VACUITY' qseal/verify_reachability.sh || bad "qseal/verify_reachability.sh has no vacuity gate"

note "== 3. every assumed spec is justified in docs/ASSUMPTIONS.md =="
assumed=0
# Strict for this artifact (qseal + the CVE anchor). The Rust ML-DSA proofs under implementations/ are
# a separate piece of work with its own assumption record, so they are listed, not gated.
for f in $(git ls-files 'qseal/*.saw' 'cve-anchor/*.saw'); do
  for fn in $(grep -oE '(llvm|mir)_unsafe_assume_spec[[:space:]]+[A-Za-z0-9_]+[[:space:]]+"[^"]+"' "$f" \
              | sed 's/.*"\(.*\)"/\1/'); do
    assumed=$((assumed+1))
    short="${fn##*::}"
    if grep -qF "$fn" docs/ASSUMPTIONS.md || grep -qF "$short" docs/ASSUMPTIONS.md; then
      printf '  %-34s justified (%s)\n' "$short" "$(basename "$f")"
    else
      bad "$f assumes '$fn' with no justification in docs/ASSUMPTIONS.md"
    fi
  done
done
note "  $assumed assumed spec(s) in the Q-SEAL artifact"
for f in $(git ls-files 'implementations/*.saw'); do
  grep -oE '(llvm|mir)_unsafe_assume_spec[[:space:]]+[A-Za-z0-9_]+[[:space:]]+"[^"]+"' "$f" \
    | sed "s|.*\"\(.*\)\"|  (not gated here) ${f##*/}: \1|"
done

note "== 4. every mutation figure in the docs agrees =="
# The mutation count was stated four different ways across the tree once. Collect every "N of M ...
# mutants" claim and fail if they disagree, so a re-measurement cannot update one file and leave three.
figs="$(git ls-files '*.md' | xargs grep -ohE '[0-9]+ of [0-9]+ (such |systematic )?[a-z/-]*mutants' 2>/dev/null \
        | grep -oE '[0-9]+ of [0-9]+' | sort -u)"
nfig="$(printf '%s\n' "$figs" | grep -c . || true)"
if [ "$nfig" -gt 1 ]; then
  bad "mutation figures disagree across the docs: $(printf '%s' "$figs" | tr '\n' ' ')"
else
  note "  all mutation figures agree: ${figs:-none stated}"
fi

note "== 5. paths cited in comments exist =="
missing=0
for f in $(git ls-files '*.c' '*.h' '*.cry' '*.saw' '*.pv'); do
  for cited in $(grep -ohE '(\.\./)*\b(qseal|target|implementations|docs|spec|proof|model|ref|cve-anchor|scripts)/[A-Za-z0-9_./-]+\.(c|h|cry|saw|pv|md|rs|thy|py|sh)' "$f" 2>/dev/null | sort -u); do
    found=0
    # resolve against the repo root, the citing file's directory, and each ancestor up to the root
    dir="$(dirname "$f")"
    while : ; do
      if [ -e "$dir/$cited" ]; then found=1; break; fi
      [ "$dir" = "." ] && break
      dir="$(dirname "$dir")"
    done
    if [ "$found" -eq 0 ]; then
      bad "$f cites '$cited', which does not resolve from the repo root or any ancestor of the file"
      missing=$((missing+1))
    fi
  done
done
[ "$missing" -eq 0 ] && note "  all cited paths resolve"

note "== 6. SAW preconditions that assume attacker-controlled shape (review each) =="
grep -rn 'llvm_precond' --include='*.saw' qseal | sed 's/^/  /' || note "  none"
note "  (each of these narrows the verified domain: check the rejecting direction is verified too)"

if [ "$fail" -ne 0 ]; then
  note ""
  note "claim-lint FAILED"
  exit 1
fi
note ""
note "claim-lint OK"
