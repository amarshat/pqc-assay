#!/usr/bin/env bash
# Cost of the hardened decapsulation (paper 2, Section 6): HQC v5.1.0 hqc-1, upstream sources at
# the pinned commit, every file a separate object at -O3 as upstream builds them, native AArch64
# (scripts/hqc-bench/immintrin.h stands in for the x86 header that src/ref/vector.h includes and
# does not use). Binaries for shipped hqc-kem.c and each hardened variant in $VARIANTS (default v42;
# proof/hqc-decaps/hardened/<v>.patch) run alternately, so every round pairs them under the same
# machine state; each run prints median and mean ns of N decapsulations and a hash of the key.
# Usage: scripts/hqc_decaps51_bench.sh [rounds] [N]
set -eu
rounds=${1:-5}; n=${2:-2000}; VARIANTS=${VARIANTS:-v42}
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
U=build/hqc-upstream-5.1; REV=06567ccbad10580d78dd7863b15d23f41076d57f; B=build/hqc-decaps51/bench
if [ ! -d $U/.git ]; then git clone -q --filter=blob:none --no-checkout https://gitlab.com/pqc-hqc/hqc.git $U; fi
git -C $U checkout -q $REV
cmp $U/src/common/hqc-kem.c target/hqc-5.1/kem/hqc-kem.c
mkdir -p $B
for v in $VARIANTS; do patch -s -o $B/kem_$v.c $U/src/common/hqc-kem.c proof/hqc-decaps/hardened/$v.patch; done
SDK=$(xcrun --show-sdk-path)
INC="-I scripts/hqc-bench -I $U/src/common -I $U/src/common/hqc-1 -I $U/src/ref -I $U/src/ref/hqc-1 -I $U/lib/fips202"
for cc in ${AVX_CLANG:-/opt/homebrew/opt/llvm@22/bin/clang} /usr/bin/clang; do
  name=$([ $cc = /usr/bin/clang ] && echo apple || echo clang22)
  objs=""
  for f in $U/src/common/code.c $U/src/common/crypto_memset.c $U/src/common/symmetric.c $U/src/ref/*.c $U/lib/fips202/fips202.c scripts/hqc-bench/bench.c; do
    o=$B/${name}_$(basename $f .c).o; $cc -isysroot $SDK -O3 $INC -c $f -o $o; objs="$objs $o"
  done
  $cc -isysroot $SDK -O3 $INC -c $U/src/common/hqc-kem.c -o $B/${name}_kem_shipped.o
  for v in $VARIANTS; do $cc -isysroot $SDK -O3 $INC -I $U/src/common -c $B/kem_$v.c -o $B/${name}_kem_$v.o; done
  for v in shipped $VARIANTS; do $cc -isysroot $SDK $objs $B/${name}_kem_$v.o -o $B/bench_${name}_$v; done
  echo "== $name ($($cc --version | head -1)), $(uname -m), N=$n"
  for r in $(seq $rounds); do
    for v in shipped $VARIANTS; do echo "-- $v round $r"; $B/bench_${name}_$v $n; done
  done
done
