#!/bin/bash
# Native differential test (not a proof): the repaired AVX2 vect_mul (hqc-1/3; hqc-5 as shipped) against
# the reference vect_mul, compiled for x86-64 at -O0, at -O3 -flto (the upstream build flags) and with
# AddressSanitizer, on random operands of degree below n plus the 16 pairs of {0, all ones, 1, x^(n-1)}.
# Also checks that the AVX2 call writes nothing past VEC_N_SIZE_BYTES and that bits at or above n are
# zero. Runs natively on x86-64 or under Rosetta 2 (macOS 15+, which executes AVX2). The repaired
# hqc-1/3 sources are made with the Makefile's AVX_FIX_SED, as `make hqc-avx` makes them.
# Usage: scripts/hqc_native/run.sh [iterations]
set -euo pipefail
cd "$(dirname "$0")/../.."
N=${1:-3000}; D=build/hqc/native; mkdir -p $D build/hqc/fixed
FIX=$(sed -n 's/^AVX_FIX_SED = //p' Makefile)
for p in 1 3; do
  sed -e "$FIX" target/hqc/avx2/hqc-$p/gf2x.c > build/hqc/fixed/gf2x_$p.c
  [ "$(diff target/hqc/avx2/hqc-$p/gf2x.c build/hqc/fixed/gf2x_$p.c | grep -c '^<')" = 1 ] || { echo "repair did not apply as one line"; exit 1; }
done
SDK=$(xcrun --show-sdk-path 2>/dev/null || true)
CC="${NATIVE_CC:-clang} ${SDK:+-arch x86_64 -isysroot $SDK} -mavx -mavx2 -mbmi -mpclmul"
RUN=""; [ "$(uname -m)" = arm64 ] && RUN="arch -x86_64"
fail=0
for p in 1 3 5; do
  SRC=build/hqc/fixed/gf2x_$p.c; [ $p = 5 ] && SRC=target/hqc/avx2/hqc-5/gf2x.c
  AI="-I target/hqc/avx2/hqc-$p -I target/hqc/hqc-$p -I target/hqc/avx2 -I target/hqc"
  for cfg in O0 O3lto asan; do
    case $cfg in O0) F="-O0"; n=$N;; O3lto) F="-O3 -flto"; n=$N;; asan) F="-O1 -g -fsanitize=address -fno-omit-frame-pointer"; n=$((N / 10));; esac
    $CC $F -Dvect_mul=ref_vect_mul -I target/hqc/hqc-$p -I target/hqc -c target/hqc/gf2x.c -o $D/ref.o
    $CC $F $AI -c $SRC -o $D/avx.o
    $CC $F $AI -c scripts/hqc_native/harness.c -o $D/h.o
    $CC $F $D/h.o $D/avx.o $D/ref.o -o $D/diff_${p}_$cfg
    printf 'hqc-%s %-6s ' $p $cfg; $RUN $D/diff_${p}_$cfg $n || fail=1
  done
done
[ $fail = 0 ] && echo "NATIVE OK: AVX2 == reference on every test, all sets and configurations" || { echo "NATIVE FAILED"; exit 1; }
