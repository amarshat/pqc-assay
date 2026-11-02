#!/usr/bin/env bash
# Every mutant section of a SAW log (from a "MUTANT-BEGIN <name>" line to the next one or the end)
# must contain a failed subgoal of <func> at <site>, so that `fails` was satisfied by a solver
# counterexample to the output postcondition and not by an error elsewhere (type error, prestate,
# override matching). <site> is a regex for the rest of the "Subgoal failed" line, for example
# 'decaps51_1.saw:138:9: error: in llvm_points_to' (the output key); default llvm_postcond.
# SAW's `print` is silent at -v 3, so the log must come from a run at the default verbosity.
# Usage: scripts/check_mutant_log.sh <log> <func> <expected sections> [site]
set -u
log=$1; func=$2; want=$3; site=${4:-llvm_postcond}
awk -v f="$func" -v want="$want" -v site="$site" '
  /^MUTANT-BEGIN /     { if (name != "") res[name] = ok; name = $2; ok = 0; n++; next }
  name != "" && $0 ~ ("Subgoal failed: " f " .*" site) { ok = 1 }
  END {
    if (name != "") res[name] = ok
    bad = 0
    for (k in res) { printf "  mutant %s: %s\n", k, (res[k] ? "counterexample at the output" : "NO FAILURE AT THE OUTPUT"); if (!res[k]) bad = 1 }
    if (n != want) { printf "  expected %d mutant sections, found %d\n", want, n; bad = 1 }
    exit bad
  }' "$log"
