#!/usr/bin/env bash
# Run SAW on every single-fault variant of decapsulation (scripts/hqc_decaps_faults.py).
#   strict (default): P1 per site. RESILIENT: proved for every fault value. BROKEN: SAW reports the
#     postcondition subgoal failed. Anything else: ERROR.
#   pres (FAULT_KIND=pres, BROKEN sites only): P3, rejection-key preservation. PRESERVED: proved
#     that a rejected ciphertext yields an output within one byte of the rejection key. VIOLATED:
#     postcondition counterexample. Anything else: ERROR.
#   fired (FAULT_KIND=fired, RESILIENT sites only): the postcondition says the fault instance never
#     executes. FIRES: SAW finds an execution where it does. NOT_FIRED: proved, so the RESILIENT
#     verdict is vacuous. Anything else: ERROR.
# Each site runs first with the inputs pinned ($FAULT_RESTRICT, 10 min), then on the full domain with
# yices and then z3 (30 min each); a counterexample in the pinned domain is a counterexample. A site
# that no run decides is TIMEOUT, reported separately and never counted as either verdict.
# Usage: scripts/hqc_decaps_faults_run.sh <p> [jobs] [tag]
set -u
p=${1:-1}; jobs=${2:-4}; tag=${3:-}
root=$(cd "$(dirname "$0")/.." && pwd)
dir=$root/${DEC_BUILD:-build/hqc-decaps}/faults_$p$tag
kind=${FAULT_KIND:-strict}; func=${DEC_TOP:-crypto_kem_dec}
if [ $kind = fired ]; then tmpl=${FIRED_TMPL:-fired51_$p.saw.in}; good=NOT_FIRED; bad=FIRES; pat=llvm_points_to; sfx=.fired
elif [ $kind = pres ]; then tmpl=${PRES_TMPL:-pres51_$p.saw.in}; good=PRESERVED; bad=VIOLATED; pat=llvm_postcond; sfx=.pres
else tmpl=${FAULT_TMPL:-faults_$p.saw.in}; good=RESILIENT; bad=BROKEN; pat=llvm_postcond; sfx=; fi
export FAULT_RESTRICT=${FAULT_RESTRICT:-}
export PATH=$root/.tools/bin:$PATH
export CRYPTOLPATH=$root/model/cryptol/hqc-decaps
run_one() {
  k=$1; dir=$2; root=$3; tmpl=$4; func=$5; good=$6; bad=$7; pat=$8; sfx=$9
  [ -s "$dir/$k$sfx.verdict" ] && return   # resume: a site with a verdict is not rerun
  s=$root/proof/hqc-decaps/_fault${sfx}_$k.saw
  # one SAW run with a time limit (perl alarm; exit 142 when it fires). $1 restriction, $2 solver.
  attempt() {
    sed -e "s#@BC@#$dir/$k.bc#" -e "s#@RESTRICT@#$1#" -e "s#w4_unint_yices UNINT#$2 UNINT#" "$root/proof/hqc-decaps/$tmpl" > "$s"
    (cd "$root/proof/hqc-decaps" && "$root/scripts/with_timeout.pl" "$3" saw "$s" > "$dir/$k$sfx.log" 2>&1)
  }
  failed_at_post() { grep -q "Subgoal failed: $func.*$pat" "$dir/$k$sfx.log"; }
  v=
  # pass 1: inputs pinned, 10 minutes. A postcondition counterexample there is a counterexample.
  if [ -n "$FAULT_RESTRICT" ]; then
    attempt "$FAULT_RESTRICT" w4_unint_yices ${PIN_LIMIT:-600}; rc=$?
    if [ $rc -ne 0 ] && [ $rc -ne 142 ]; then failed_at_post && v=$bad || v=ERROR; fi
  fi
  # pass 2 and 3: full domain, yices then z3, 30 minutes each.
  for solver in w4_unint_yices w4_unint_z3; do
    [ -n "$v" ] && break
    attempt "" $solver ${FULL_LIMIT:-1800}; rc=$?
    if [ $rc -eq 0 ]; then v=$good
    elif [ $rc -ne 142 ]; then failed_at_post && v=$bad || v=ERROR; fi
  done
  [ -n "$v" ] || v=TIMEOUT
  rm -f "$s"
  printf '%s\t%s\n' "$k" "$v" > "$dir/$k$sfx.verdict"
}
export -f run_one
if [ $kind = fired ]; then sites=$(awk -F'\t' '$2=="RESILIENT"{print $1}' "$dir/RESULTS.tsv")
elif [ $kind = pres ]; then sites=$(awk -F'\t' '$2=="BROKEN"{print $1}' "$dir/RESULTS.tsv")
else sites=$(ls "$dir"/f*.bc | xargs -n1 basename | sed 's/\.bc$//' | grep -v '\.'); fi
printf '%s\n' $sites | grep . | xargs -P "$jobs" -I{} bash -c 'run_one "$@"' _ {} "$dir" "$root" "$tmpl" "$func" "$good" "$bad" "$pat" "$sfx"
if [ $kind = fired ]; then cat "$dir"/f*.fired.verdict 2>/dev/null | sort > "$dir/FIRED.tsv"; cut -f2 "$dir/FIRED.tsv" | sort | uniq -c
elif [ $kind = pres ]; then cat "$dir"/f*.pres.verdict 2>/dev/null | sort > "$dir/PRES.tsv"; cut -f2 "$dir/PRES.tsv" | sort | uniq -c
else join -t $'\t' <(cat "$dir"/f???.verdict | sort) <(sort "$dir/MANIFEST.tsv") > "$dir/RESULTS.tsv"; cut -f2 "$dir/RESULTS.tsv" | sort | uniq -c; fi
