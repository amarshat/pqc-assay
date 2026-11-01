#!/usr/bin/env bash
# Run SAW on every single-fault variant of crypto_kem_dec (scripts/hqc_decaps_faults.py) and classify
# each site: RESILIENT (the implicit-rejection property is proved under every value of the fault) or
# BROKEN (SAW returns a counterexample: a fault instance and value for which a rejected ciphertext
# does not yield the rejection key). Usage: scripts/hqc_decaps_faults_run.sh <p> [jobs] [tag]
set -u
p=${1:-1}; jobs=${2:-4}; tag=${3:-}
root=$(cd "$(dirname "$0")/.." && pwd)
dir=$root/${DEC_BUILD:-build/hqc-decaps}/faults_$p$tag
tmpl=${FAULT_TMPL:-faults_$p.saw.in}; func=${DEC_TOP:-crypto_kem_dec}
export PATH=$root/.tools/bin:$PATH
export CRYPTOLPATH=$root/model/cryptol/hqc-decaps
run_one() {
  k=$1; dir=$2; root=$3; p=$4; tmpl=$5; func=$6
  s=$root/proof/hqc-decaps/_fault_$k.saw
  sed "s#@BC@#$dir/$k.bc#" "$root/proof/hqc-decaps/$tmpl" > "$s"
  (cd "$root/proof/hqc-decaps" && saw "$s" > "$dir/$k.log" 2>&1); rc=$?
  rm -f "$s"
  if [ $rc -eq 0 ]; then v=RESILIENT
  elif grep -q "Subgoal failed: $func.*llvm_postcond" "$dir/$k.log"; then v=BROKEN
  else v=ERROR; fi
  printf '%s\t%s\n' "$k" "$v" > "$dir/$k.verdict"
}
export -f run_one
ls "$dir"/f*.bc | xargs -n1 basename | sed 's/\.bc$//' | xargs -P "$jobs" -I{} bash -c 'run_one "$@"' _ {} "$dir" "$root" "$p" "$tmpl" "$func"
join -t $'\t' <(cat "$dir"/f*.verdict | sort) <(sort "$dir/MANIFEST.tsv") > "$dir/RESULTS.tsv"
cut -f2 "$dir/RESULTS.tsv" | sort | uniq -c
