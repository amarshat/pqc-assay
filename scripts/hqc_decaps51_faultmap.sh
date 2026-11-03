#!/usr/bin/env bash
# Single-fault map of v5.1.0 decapsulation at hqc-1 (paper 2, Sections 4 to 6). Usage:
#   scripts/hqc_decaps51_faultmap.sh <variant> [jobs]
# Region: hqc_kem_decaps_internal from the XOF initialization (key regeneration included) to the
# end of the selection; every call in it can be skipped (scripts/hqc_decaps_faults.py SKIPPABLE).
# A fired check runs on every RESILIENT site (FIRED.tsv; NOT_FIRED would make the verdict vacuous).
# variant: shipped (target/hqc-5.1 as vendored), v4, v41, v42 or v43 (proof/hqc-decaps/hardened/<v>.patch
# applied to a copy of hqc-kem.c). Four passes, each a SAW run per fault site:
#   strict  (faults51_1.saw.in): a rejected ciphertext yields the rejection key. RESILIENT / BROKEN.
#   fired   (fired51_1.saw.in, RESILIENT sites only): the fault instance can execute. FIRES /
#           NOT_FIRED.
#   ni      (ni51_1.saw.in, BROKEN sites only; P2, G-independence): two runs with independent G;
#           both reject implies equal outputs. NONINTERFERENT / LEAK.
#   pres    (pres51_1.saw.in, BROKEN sites only; P3): a rejected ciphertext yields an output that
#           differs from the rejection key in at most one byte. PRESERVED / VIOLATED.
# Verdicts land in build/hqc-decaps51/faults_1<tag>/{RESULTS,FIRED,NI,PRES}.tsv. ERROR means SAW failed
# somewhere other than the postcondition; such a site is reported, never counted as either verdict.
set -eu
v=${1:?variant: shipped, v4, v41, v42 or v43}; jobs=${2:-4}
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
B=build/hqc-decaps51
LLVM=${AVX_LLVM_BIN:-/opt/homebrew/opt/llvm@22/bin/}
CC="${LLVM}clang --target=x86_64-apple-darwin -isysroot $(xcrun --show-sdk-path) -D_FORTIFY_SOURCE=0 -O0 -g"
mkdir -p $B/cm
case $v in
  shipped) tag=; src=$B/_dec.c; inc=
           printf '#include "crypto_memset.c"\n#include "vector.c"\n#include "parsing.c"\n#include "hqc-kem.c"\n' > $src ;;
  v4|v41|v42|v43) tag=_$v; src=$B/cm/_dec_$v.c; inc="-I $B/cm"
           patch -s -o $B/cm/kem_$v.c target/hqc-5.1/kem/hqc-kem.c proof/hqc-decaps/hardened/$v.patch
           printf '#include "crypto_memset.c"\n#include "vector.c"\n#include "parsing.c"\n#include "kem_%s.c"\n' $v > $src ;;
  *) echo "unknown variant $v"; exit 2 ;;
esac
$CC -S -emit-llvm $inc -I target/hqc-5.1/kem -I target/hqc-5.1/hqc-1 -o $B/dec_1$tag.ll $src
if [ -z "${RESUME:-}" ]; then rm -rf $B/faults_1$tag; fi
DEC_BUILD=$B DEC_FUNC=hqc_kem_decaps_internal DEC_REGION_START='AFTER_INIT:@xof_init_dom_sep(' python3 scripts/hqc_decaps_faults.py 1 "$tag"
for f in $B/faults_1$tag/f???.ll; do ${LLVM}llvm-as "$f" -o "${f%.ll}.bc" 2>/dev/null; done
restrict='llvm_precond {{ c == zero /\\ dk == dkRamp }};'
echo ">> strict ($v)"
DEC_BUILD=$B FAULT_TMPL=faults51_1.saw.in DEC_TOP=hqc_kem_decaps FAULT_RESTRICT="$restrict" scripts/hqc_decaps_faults_run.sh 1 "$jobs" "$tag"
echo ">> fired check on RESILIENT sites ($v)"
DEC_BUILD=$B FAULT_KIND=fired DEC_TOP=hqc_kem_decaps FAULT_RESTRICT="$restrict" scripts/hqc_decaps_faults_run.sh 1 "$jobs" "$tag"
rm -f $B/dec2.bc
common="DEC_BUILD=$B DEC2_SRC=scripts/hqc_decaps51_dec2.c"
echo ">> noninterference ($v)"
env $common NI_TMPL=ni51_1.saw.in NI_RESTRICT="$restrict" scripts/hqc_decaps_ni_run.sh 1 "$jobs" "$tag"
echo ">> rejection-key preservation, P3 ($v)"
DEC_BUILD=$B FAULT_KIND=pres DEC_TOP=hqc_kem_decaps FAULT_RESTRICT="$restrict" scripts/hqc_decaps_faults_run.sh 1 "$jobs" "$tag"
