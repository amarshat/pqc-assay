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

note "== 1. every SAW proof carries a non-vacuity guard =="
for f in qseal/proof/*.saw; do
  v=$(grep -c 'llvm_verify' "$f")
  g=$(grep -c '^fails (' "$f")
  # a `fails` line also contains llvm_verify, so the real obligation count is v - g
  obligations=$((v - g))
  printf '  %-28s obligations=%-3s mutants=%s\n' "$(basename "$f")" "$obligations" "$g"
  [ "$g" -ge 1 ] || bad "$f has $obligations obligation(s) and no 'fails (llvm_verify ...)' mutant guard"
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

note "== 3. assumed specs, listed (each needs a justification in docs/ASSUMPTIONS.md) =="
grep -rn 'unsafe_assume_spec' --include='*.saw' qseal proof implementations 2>/dev/null \
  | grep -v '^\s*//' | sed 's/^/  /' || note "  none"

note "== 4. paths cited in comments exist =="
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

note "== 5. SAW preconditions that assume attacker-controlled shape (review each) =="
grep -rn 'llvm_precond' --include='*.saw' qseal | sed 's/^/  /' || note "  none"
note "  (each of these narrows the verified domain: check the rejecting direction is verified too)"

if [ "$fail" -ne 0 ]; then
  note ""
  note "claim-lint FAILED"
  exit 1
fi
note ""
note "claim-lint OK"
