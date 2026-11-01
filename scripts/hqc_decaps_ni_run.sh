#!/usr/bin/env bash
# Second pass over the BROKEN sites of scripts/hqc_decaps_faults_run.sh: the noninterference check
# (proof/hqc-decaps/ni_<p>.saw.in, harness scripts/hqc_decaps_dec2.c). Two decapsulations of the same
# ciphertext under the same key and the same fault, with independent G functions. LEAK: SAW finds a
# fault for which both runs reject and the outputs differ, so the output on rejection depends on G
# (the real session key). NONINTERFERENT: proved equal for every fault value.
# Usage: scripts/hqc_decaps_ni_run.sh <p> [jobs] [tag]
set -u
p=${1:-1}; jobs=${2:-4}; tag=${3:-}
root=$(cd "$(dirname "$0")/.." && pwd)
dir=$root/${DEC_BUILD:-build/hqc-decaps}/faults_$p$tag
tmpl=${NI_TMPL:-ni_$p.saw.in}; kind=${NI_KIND:-ni}; bad=${NI_BAD:-LEAK}; good=${NI_GOOD:-NONINTERFERENT}; dec2=$root/${DEC_BUILD:-build/hqc-decaps}/dec2.bc; dec2src=${DEC2_SRC:-scripts/hqc_decaps_dec2.c}
export NI_RESTRICT=${NI_RESTRICT:-'llvm_precond {{ c == zero /\\ sk == skRamp }};'}
export PATH=$root/.tools/bin:$PATH
export CRYPTOLPATH=$root/model/cryptol/hqc-decaps
LLVM_LINK=${LLVM_LINK:-/opt/homebrew/opt/llvm@22/bin/llvm-link}
test -f "$dec2" || /opt/homebrew/opt/llvm@22/bin/clang --target=x86_64-apple-darwin -isysroot "$(xcrun --show-sdk-path)" -O0 -g -c -emit-llvm "$root/$dec2src" -o "$dec2"
run_one() {
  k=$1; dir=$2; root=$3; p=$4; ll=$5; tmpl=$6; dec2=$7; kind=$8; bad=$9; good=${10}
  "$ll" "$dir/$k.bc" "$dec2" -o "$dir/$k.${kind}.bc" || { printf '%s\tERROR\n' "$k" > "$dir/$k.${kind}verdict"; return; }
  s=$root/proof/hqc-decaps/_${kind}_$k.saw
  # pass 1: c = 0 and sk a byte ramp; a counterexample there is a leak. pass 2 (only if pass 1
  # proves): the full domain.
  R=$NI_RESTRICT
  sed -e "s#@BC@#$dir/$k.${kind}.bc#" -e "s#@RESTRICT@#$R#" "$root/proof/hqc-decaps/$tmpl" > "$s"
  (cd "$root/proof/hqc-decaps" && saw "$s" > "$dir/$k.${kind}.log" 2>&1); rc=$?
  if [ $rc -eq 0 ]; then
    sed -e "s#@BC@#$dir/$k.${kind}.bc#" -e "s#@RESTRICT@##" "$root/proof/hqc-decaps/$tmpl" > "$s"
    (cd "$root/proof/hqc-decaps" && saw "$s" > "$dir/$k.${kind}.log" 2>&1); rc=$?
  fi
  rm -f "$s"
  if [ $rc -eq 0 ]; then v=$good
  elif grep -q "Subgoal failed: dec2.*llvm_postcond" "$dir/$k.${kind}.log"; then v=$bad
  else v=ERROR; fi
  printf '%s\t%s\n' "$k" "$v" > "$dir/$k.${kind}verdict"
}
export -f run_one
awk -F'\t' '$2=="BROKEN"{print $1}' "$dir/RESULTS.tsv" | xargs -P "$jobs" -I{} bash -c 'run_one "$@"' _ {} "$dir" "$root" "$p" "$LLVM_LINK" "$tmpl" "$dec2" "$kind" "$bad" "$good"
cat "$dir"/*.${kind}verdict | sort > "$dir/$(echo $kind | tr a-z A-Z).tsv"
cut -f2 "$dir/$(echo $kind | tr a-z A-Z).tsv" | sort | uniq -c
