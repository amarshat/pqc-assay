#!/bin/bash
# Native differential test (not a proof) of the additive-FFT reference C (target/hqc-fft/gf264_ref) at
# the three HQC lengths, against the schoolbook product in harness.c: decode_64 repaired as in
# `make hqc-fft` (FFT_FIX_SED) and as shipped, each at -O0, -O2 and -O1 with AddressSanitizer and
# UndefinedBehaviorSanitizer. Negative control: the repaired copy with one output byte flipped must
# mismatch. Portable C, so it runs natively on arm64 or x86-64.
# Usage: scripts/hqc_fft_native/run.sh [random pairs per run]
set -euo pipefail
cd "$(dirname "$0")/../.."
N=${1:-100}; D=build/hqc-fft/native; mkdir -p $D
SRC=target/hqc-fft/gf264_ref
FILES=$(sed -n 's/^FFT_C *:= //p' Makefile)
eval "FIX=($(sed -n 's/^FFT_FIX_SED = //p' Makefile | sed 's/\$\$/$/g'))"
sed "${FIX[@]}" $SRC/dencoder.c > $D/dencoder_fixed.c
[ "$(diff $SRC/dencoder.c $D/dencoder_fixed.c | grep -c '^<')" = 2 ] || { echo "repair did not apply"; exit 1; }
sed 's/= mat0\[j\];/= mat0[j] ^ (k == 3 \&\& j == 5);/' $D/dencoder_fixed.c > $D/dencoder_mut.c
CC=${NATIVE_CC:-clang}
fail=0
build() {  # build <variant> <flags> <p>
  local v=$1 f=$2 p=$3 objs=""
  for x in $FILES; do
    local s=$SRC/$x.c
    if [ $x = dencoder ]; then case $v in fixed) s=$D/dencoder_fixed.c;; mut) s=$D/dencoder_mut.c;; esac; fi
    $CC $f -std=c11 -I $SRC -c $s -o $D/$x.$v.o; objs="$objs $D/$x.$v.o"
  done
  $CC $f -std=c11 -I $SRC -DHQC_P=$p -c scripts/hqc_fft_native/harness.c -o $D/h.o
  $CC $f $D/h.o $objs -o $D/t_${p}_$v
}
for p in 1 3 5; do
  for v in fixed asis; do
    for cfg in O0 O2 san; do
      case $cfg in O0) F="-O0"; n=$N;; O2) F="-O2"; n=$N;; san) F="-O1 -g -fsanitize=address,undefined -fno-sanitize-recover=all -fno-omit-frame-pointer"; n=$((N / 5));; esac
      build $v "$F" $p
      printf 'hqc-%s %-5s %-3s ' $p $v $cfg; $D/t_${p}_$v $n || fail=1
    done
  done
  build mut -O2 $p
  printf 'hqc-%s mutant O2  ' $p
  if $D/t_${p}_mut 10 2>/dev/null; then echo "!! negative control not caught"; fail=1; else echo "(caught, expected)"; fi
done
[ $fail = 0 ] && echo "FFT NATIVE OK: the FFT entry points == schoolbook on every test, all lengths and configurations" || { echo "FFT NATIVE FAILED"; exit 1; }
