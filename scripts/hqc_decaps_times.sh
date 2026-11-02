#!/usr/bin/env bash
# Wall clock of each decapsulation SAW run, one at a time (paper 2, Table in Section 3). Needs the
# bitcode and generated scripts of make hqc-decaps, hqc-decaps51, hqc-decaps51-O2 and
# hqc-decaps51-hardened. Writes proof/hqc-decaps/logs/proof-times.txt: one row per script with the
# exit code and seconds, then the VERIFIED/REFUTED lines that script printed.
set -u
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
SAW=$root/.tools/bin/saw
out=proof/hqc-decaps/logs/proof-times.txt
tmp=$(mktemp -d)
{
  echo "# Wall clock of single SAW runs, one at a time, $(sysctl -n machdep.cpu.brand_string), SAW $($SAW --version 2>&1 | head -1), $(date +%F)."
  echo "# Command per row: cd proof/hqc-decaps && CRYPTOLPATH=model/cryptol/hqc-decaps saw <script> (scripts/hqc_decaps_times.sh)."
} > "$out"
for s in decaps_1.saw decaps_3.saw decaps_5.saw decaps51_1.saw decaps51_3.saw decaps51_5.saw spec51_1.saw \
         ../../build/hqc-decaps51/decaps51_1_O2.saw ../../build/hqc-decaps51/decaps51_1_v4.saw \
         ../../build/hqc-decaps51/decaps51_1_v41.saw ../../build/hqc-decaps51/decaps51_1_v42.saw; do
  n=$(basename "$s")
  t0=$(date +%s)
  (cd proof/hqc-decaps && CRYPTOLPATH=$root/model/cryptol/hqc-decaps "$SAW" "$s" > "$tmp/$n.log" 2>&1); rc=$?
  echo "$n exit=$rc $(( $(date +%s) - t0 ))s" >> "$out"
  grep -hE '^(VERIFIED|REFUTED)' "$tmp/$n.log" | sed "s#^#  #" >> "$out"
done
rm -rf "${tmp:?}"
cat "$out"
