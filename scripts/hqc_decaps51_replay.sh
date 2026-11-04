#!/usr/bin/env bash
# Native replay of the call skips that SAW refutes in v4.3 (and the same calls in shipped v5.1.0),
# hqc-1, with the real primitives (paper 2, Section 6). Upstream sources at the pinned commit, as in
# scripts/hqc_decaps51_bench.sh. Each skip build has one call's outputs redirected to scratch
# (scripts/hqc-replay/skip.py); scripts/hqc-replay/replay.c runs it on two key pairs and four
# ciphertexts; scripts/hqc-replay/judge.py compares with the unfaulted build.
# Output: proof/hqc-decaps/logs/replay.txt. Usage: scripts/hqc_decaps51_replay.sh
set -eu
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
U=build/hqc-upstream-5.1; REV=06567ccbad10580d78dd7863b15d23f41076d57f; B=build/hqc-decaps51/replay
if [ ! -d $U/.git ]; then git clone -q --filter=blob:none --no-checkout https://gitlab.com/pqc-hqc/hqc.git $U; fi
git -C $U checkout -q $REV
cmp $U/src/common/hqc-kem.c target/hqc-5.1/kem/hqc-kem.c
mkdir -p $B
cp $U/src/common/hqc-kem.c $B/kem_shipped.c
patch -s -o $B/kem_v43.c $U/src/common/hqc-kem.c proof/hqc-decaps/hardened/v43.patch
for t in shipped v43; do python3 scripts/hqc-replay/skip.py $B/kem_$t.c $B $t > $B/skips.txt; done
CC=${CC:-/usr/bin/clang}; SDK=$(xcrun --show-sdk-path)
INC="-I scripts/hqc-bench -I $U/src/common -I $U/src/common/hqc-1 -I $U/src/ref -I $U/src/ref/hqc-1 -I $U/lib/fips202"
objs=""
for f in $U/src/common/code.c $U/src/common/crypto_memset.c $U/src/common/symmetric.c $U/src/ref/*.c $U/lib/fips202/fips202.c scripts/hqc-replay/replay.c; do
  o=$B/$(basename $f .c).o; $CC -isysroot $SDK -O2 $INC -c $f -o $o; objs="$objs $o"
done
out=$B/runs.txt; : > $out
for t in shipped v43; do
  for k in none 0 1 2 3 4 5 6; do
    src=$B/kem_$t.c; [ $k = none ] || src=$B/kem_${t}_s$k.c
    $CC -isysroot $SDK -O2 $INC -c $src -o $B/kem.o
    $CC -isysroot $SDK $objs $B/kem.o -o $B/replay
    echo "== $t $k" >> $out; $B/replay >> $out || echo "!! exit $?" >> $out
  done
done
{ echo "# scripts/hqc_decaps51_replay.sh, $(uname -m), $($CC --version | head -1), $(date +%F)"
  echo "# skips: $(tr '\n' ' ' < $B/skips.txt)"
  python3 scripts/hqc-replay/judge.py $out; } > proof/hqc-decaps/logs/replay.txt
cat proof/hqc-decaps/logs/replay.txt
