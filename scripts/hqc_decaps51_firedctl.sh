#!/usr/bin/env bash
# Controls for the fired checks of the v5.1.0 fault map (paper 2, Section 4). A fired check that
# says FIRES whatever happens would make every fired verdict empty, so each template is also run
# with the fault instance pinned to one that never executes (fault_J == 1000000; no region has that
# many instances). Then SAW must prove that fault_fired stays 0, on the same site and premise:
#   fired51_1.saw.in on the first RESILIENT site of the shipped map;
#   nifired51_1.saw.in with the P2K premise (hashGk) on the first site where P2K holds.
# Needs the shipped map (scripts/hqc_decaps51_faultmap.sh shipped). Exit 0 when both controls verify.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
d=$root/build/hqc-decaps51/faults_1
LLVM=${AVX_LLVM_BIN:-/opt/homebrew/opt/llvm@22/bin/}
export PATH=$root/.tools/bin:$PATH CRYPTOLPATH=$root/model/cryptol/hqc-decaps
pin='llvm_precond {{ c == zero /\\ dk == dkRamp /\\ J == 1000000 }};'
log=$root/build/hqc-decaps51/firedctl; mkdir -p "$log"

k=$(awk -F'\t' '$2=="RESILIENT"{print $1; exit}' "$d/RESULTS.tsv")
s=proof/hqc-decaps/_ctl_fired.saw
sed -e "s#@BC@#$d/$k.bc#" -e "s#@RESTRICT@#$pin#" proof/hqc-decaps/fired51_1.saw.in > $s
(cd proof/hqc-decaps && saw "$(basename $s)" > "$log/fired.log" 2>&1) || { rm -f $s; echo "!! fired control failed at $k ($log/fired.log)"; exit 1; }
rm -f $s
echo "VERIFIED: fired51_1 with fault_J == 1000000 at $k: fault_fired stays 0"

k=$(awk -F'\t' '$2=="NONINTERFERENT"{print $1; exit}' "$d/NIK.tsv")
[ -f "$d/$k.nifiredk.bc" ] || {
  [ -f build/hqc-decaps51/dec2.bc ] || ${LLVM}clang --target=x86_64-apple-darwin -isysroot "$(xcrun --show-sdk-path)" -O0 -g -c -emit-llvm scripts/hqc_decaps51_dec2.c -o build/hqc-decaps51/dec2.bc
  ${LLVM}llvm-link "$d/$k.bc" build/hqc-decaps51/dec2.bc -o "$d/$k.nifiredk.bc"; }
s=proof/hqc-decaps/_ctl_nifired.saw
sed -e "s#@BC@#$d/$k.nifiredk.bc#" -e "s#@RESTRICT@#$pin#" -e 's#{{ hashGe e h mm s }}#{{ hashGk e h mm s }}#' \
    -e 's#@PREM@#premP2K#g' proof/hqc-decaps/nifired51_1.saw.in > $s
(cd proof/hqc-decaps && saw "$(basename $s)" > "$log/nifired.log" 2>&1) || { rm -f $s; echo "!! two-run fired control failed at $k ($log/nifired.log)"; exit 1; }
rm -f $s
echo "VERIFIED: nifired51_1 (P2K premise) with fault_J == 1000000 at $k: fault_fired stays 0"
