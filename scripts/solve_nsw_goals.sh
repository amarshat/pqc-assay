#!/usr/bin/env bash
# Parallel discharge of the dumped inverse-NTT nsw obligations. Every .smt2 in this directory must
# come back "unsat" for the verification to hold (each file is one proof obligation, negated).
# Usage: ./solve_all.sh [jobs] [per-goal-seconds]
set -u
cd "$(dirname "$0")"
JOBS="${1:-6}"
LIMIT="${2:-7200}"
BWZ="../../.tools/bin/bitwuzla"
RES="results.csv"
: > "$RES"

solve_one() {
  f="$1"
  s=$(date +%s)
  out=$("$BWZ" --time-limit "$(( ${LIMIT} * 1000 ))" "$f" 2>&1 | tail -1)
  e=$(( $(date +%s) - s ))
  echo "$f,$out,$e" >> results.csv
  echo "$f -> $out (${e}s)"
}
export -f solve_one
export BWZ LIMIT

ls ./*.smt2 | xargs -P "$JOBS" -I{} bash -c 'solve_one "$@"' _ {}

echo "==== summary ===="
total=$(ls ./*.smt2 | wc -l | tr -d ' ')
unsat=$(grep -c ",unsat," "$RES")
echo "unsat: $unsat / $total"
grep -v ",unsat," "$RES" | sed 's/^/NOT-UNSAT: /'
[ "$unsat" = "$total" ] && echo "ALL GOALS DISCHARGED" || echo "GOALS REMAIN (see NOT-UNSAT lines)"
