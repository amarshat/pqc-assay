#!/usr/bin/env bash
# Second pass over the BROKEN sites of scripts/hqc_decaps_faults_run.sh: the noninterference check
# (proof/hqc-decaps/ni_<p>.saw.in, harness scripts/hqc_decaps_dec2.c). Two decapsulations of the same
# ciphertext under the same key and the same fault, with independent G functions. LEAK: SAW finds a
# fault for which both runs reject and the outputs differ, so the output on rejection depends on G
# (the real session key). NONINTERFERENT: proved equal for every fault value.
# NI_G=hashGk NI_POST=noLeakK switches only the session-key half of G's output between the runs
# (P2K); NI_G=hashGt NI_POST=noLeakT only the re-encryption randomness half (P2theta). Set NI_KIND too.
# Usage: scripts/hqc_decaps_ni_run.sh <p> [jobs] [tag]
set -u
p=${1:-1}; jobs=${2:-4}; tag=${3:-}
root=$(cd "$(dirname "$0")/.." && pwd)
dir=$root/${DEC_BUILD:-build/hqc-decaps}/faults_$p$tag
tmpl=${NI_TMPL:-ni_$p.saw.in}; kind=${NI_KIND:-ni}; bad=${NI_BAD:-LEAK}; good=${NI_GOOD:-NONINTERFERENT}; dec2=$root/${DEC2_BC:-${DEC_BUILD:-build/hqc-decaps}/dec2.bc}; dec2src=${DEC2_SRC:-scripts/hqc_decaps_dec2.c}
export NI_RESTRICT=${NI_RESTRICT:-'llvm_precond {{ c == zero /\\ sk == skRamp }};'}
export PATH=$root/.tools/bin:$PATH
export CRYPTOLPATH=$root/model/cryptol/hqc-decaps
LLVM_LINK=${LLVM_LINK:-/opt/homebrew/opt/llvm@22/bin/llvm-link}
test -f "$dec2" || /opt/homebrew/opt/llvm@22/bin/clang --target=x86_64-apple-darwin -isysroot "$(xcrun --show-sdk-path)" -O0 -g -c -emit-llvm "$root/$dec2src" -o "$dec2"
run_one() {
  k=$1; dir=$2; root=$3; p=$4; ll=$5; tmpl=$6; dec2=$7; kind=$8; bad=$9; good=${10}
  [ -s "$dir/$k.${kind}verdict" ] && return   # resume
  "$ll" "$dir/$k.bc" "$dec2" -o "$dir/$k.${kind}.bc" || { printf '%s\tERROR\n' "$k" > "$dir/$k.${kind}verdict"; return; }
  s=$root/proof/hqc-decaps/_${kind}_$(basename $dir)_$k.saw
  attempt() {
    sed -e "s#@BC@#$dir/$k.${kind}.bc#" -e "s#@RESTRICT@#$1#" -e "s#w4_unint_yices UNINT#$2 UNINT#" \
        -e "s#{{ hashGe e h mm s }}#{{ ${NI_G:-hashGe} e h mm s }}#" -e "s#{{ noLeak c dk k1 k2 }}#{{ ${NI_POST:-noLeak} c dk k1 k2 }}#" \
        "$root/proof/hqc-decaps/$tmpl" > "$s"
    (cd "$root/proof/hqc-decaps" && "$root/scripts/with_timeout.pl" "$3" saw "$s" > "$dir/$k.${kind}.log" 2>&1)
  }
  failed_at_post() { grep -q "Subgoal failed: dec2.*llvm_postcond" "$dir/$k.${kind}.log"; }
  v=
  # pass 1: c = 0 and the key a byte ramp, 10 minutes; a counterexample there is a leak.
  attempt "$NI_RESTRICT" w4_unint_yices ${PIN_LIMIT:-600}; rc=$?
  if [ $rc -ne 0 ] && [ $rc -ne 142 ]; then failed_at_post && v=$bad || v=ERROR; fi
  # pass 2 and 3: the full domain, yices then z3, 30 minutes each.
  for solver in w4_unint_yices w4_unint_z3; do
    [ -n "$v" ] && break
    attempt "" $solver ${FULL_LIMIT:-1800}; rc=$?
    if [ $rc -eq 0 ]; then v=$good
    elif [ $rc -ne 142 ]; then failed_at_post && v=$bad || v=ERROR; fi
  done
  [ -n "$v" ] || v=TIMEOUT
  rm -f "$s"
  printf '%s\t%s\n' "$k" "$v" > "$dir/$k.${kind}verdict"
}
export -f run_one
# NI_FROM=<TSV>:<verdicts> (e.g. NI.tsv:LEAK|TIMEOUT) runs on those sites instead of every BROKEN one.
from=${NI_FROM:-RESULTS.tsv:BROKEN}
export NI_G NI_POST
awk -F'\t' -v re="^(${from#*:})\$" '$2 ~ re {print $1}' "$dir/${from%%:*}" | xargs -P "$jobs" -I{} bash -c 'run_one "$@"' _ {} "$dir" "$root" "$p" "$LLVM_LINK" "$tmpl" "$dec2" "$kind" "$bad" "$good"
cat "$dir"/*.${kind}verdict | sort > "$dir/$(echo $kind | tr a-z A-Z).tsv"
cut -f2 "$dir/$(echo $kind | tr a-z A-Z).tsv" | sort | uniq -c
