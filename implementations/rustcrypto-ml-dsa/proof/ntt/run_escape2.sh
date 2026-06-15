#!/usr/bin/env bash
# Reproduces the escape-2 contrast: same Barrett identity, integer vs bit-vector.
# Integer (NIA) discharges in ~0.04 s; bit-vector (QF_BV) times out.
# Plus a non-vacuity mutation (Q+1) that must return sat.
set -u
Z3="${Z3:-$(command -v z3 || echo ../../../../.tools/bin/z3)}"
here="$(cd "$(dirname "$0")" && pwd)"

echo "== integer (NIA), x<2^46 -- expect: unsat, ~0.04s =="
/usr/bin/time -p "$Z3" -T:300 "$here/escape2_barrett_int.smt2"

echo
echo "== non-vacuity mutation (Q+1) -- expect: sat =="
sed 's/Int 8380417/Int 8380418/' "$here/escape2_barrett_int.smt2" | "$Z3" -T:60 /dev/stdin

echo
echo "== bit-vector (QF_BV), x<2^46 -- expect: timeout =="
/usr/bin/time -p "$Z3" -T:300 "$here/escape2_barrett_bv.smt2"
