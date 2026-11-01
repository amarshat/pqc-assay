#!/usr/bin/env bash
# Code-generation check for HQC v5.1.0 decapsulation (paper 2, Section 7), hqc-1, x86_64.
# Fetches upstream at the pinned v5.1.0 commit (the KEM file is the vendored one, compared byte for
# byte) and reports, for each build, how many "test; jcc" pairs _hqc_kem_decaps contains. The
# selection's branch on the acceptance bit shows up as one such pair; loop exits use cmp, not test.
#   tu      vector.c, parsing.c, hqc.c, hqc-kem.c in one translation unit
#   nohqc   the same without hqc.c (hqc_pke_decrypt stays external)
#   barrier tu with __asm__("" : "+r"(result)) after "result -= 1;"
#   v41     tu with proof/hqc-decaps/hardened/v41.patch applied
#   lto     every source file of src/common, src/ref and lib/fips202 as a separate -flto object,
#           linked into one shared library by ld64 with that compiler's libLTO. The driver passes no
#           optimization level to ld64, so the link-time pipeline is libLTO's default; the opt column
#           is the level the objects were compiled at.
# Observed 2026-11-01 (clang 22.1.8, Apple clang 14.0.3): clang 22 branches for tu at -O2/-O3/-Os and
# for lto at -O1 (hqc_pke_decrypt not inlined; its constant return value is propagated across
# modules and the call's result is dropped). No other row has a test-and-jump.
set -eu
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
B=build/hqc-decaps51/cc; U=build/hqc-upstream-5.1; REV=06567ccbad10580d78dd7863b15d23f41076d57f
CLANG22=${AVX_CLANG:-/opt/homebrew/opt/llvm@22/bin/clang}; APPLE=/usr/bin/clang
SDK=$(xcrun --show-sdk-path)
if [ ! -d $U/.git ]; then git clone -q --filter=blob:none --no-checkout https://gitlab.com/pqc-hqc/hqc.git $U; fi
git -C $U checkout -q $REV
cmp $U/src/common/hqc-kem.c target/hqc-5.1/kem/hqc-kem.c
mkdir -p $B/lto; cd $B
INC="-I ../../../$U/src/common -I ../../../$U/src/common/hqc-1 -I ../../../$U/src/ref -I ../../../$U/src/ref/hqc-1 -I ../../../$U/lib/fips202 -I ."
sed 's/^    result -= 1;$/    result -= 1;\n    __asm__("" : "+r"(result));/' ../../../$U/src/common/hqc-kem.c > hqc-kem-bar.c
grep -q '__asm__("" : "+r"(result));' hqc-kem-bar.c
patch -s -o kem_v41.c ../../../$U/src/common/hqc-kem.c ../../../proof/hqc-decaps/hardened/v41.patch
hdr='#include "crypto_memset.c"\n#include "vector.c"\n#include "parsing.c"\n'
printf "$hdr"'#include "hqc.c"\n#include "hqc-kem.c"\n' > tu.c
printf "$hdr"'#include "hqc-kem.c"\n' > nohqc.c
printf "$hdr"'#include "hqc.c"\n#include "hqc-kem-bar.c"\n' > barrier.c
printf "$hdr"'#include "hqc.c"\n#include "kem_v41.c"\n' > v41.c
count() { otool -tvV "$1" | awk '/^_hqc_kem_decaps:/{f=1;next} f&&/^_[A-Za-z]/{f=0} f' \
          | grep -A1 -E '\stest[bwlq]\s' | grep -cE '\sj[a-z]+\s' || true; }
printf '%-10s %-8s %-4s %s\n' compiler build opt test+jcc
for cc in $CLANG22 $APPLE; do
  name=$([ $cc = $APPLE ] && echo apple14 || echo clang22)
  for O in O1 O2 O3 Os; do
    for u in tu nohqc barrier v41; do
      $cc --target=x86_64-apple-darwin -isysroot $SDK -D_FORTIFY_SOURCE=0 -$O -c $INC $u.c -o $u.o
      printf '%-10s %-8s %-4s %s\n' $name $u $O "$(count $u.o)"
    done
    rm -f lto/*.o
    for f in ../../../$U/src/common/*.c ../../../$U/src/ref/*.c ../../../$U/lib/fips202/*.c; do
      $cc --target=x86_64-apple-darwin -isysroot $SDK -D_FORTIFY_SOURCE=0 -$O -flto $INC -c $f -o lto/$(basename $f .c).o
    done
    LD=$([ $cc = $APPLE ] && echo "" || echo "-fuse-ld=ld -Wl,-lto_library,$(dirname $cc)/../lib/libLTO.dylib")
    $cc --target=x86_64-apple-darwin -isysroot $SDK -$O -flto $LD -shared -undefined dynamic_lookup lto/*.o -o lto/libhqc.dylib 2>/dev/null
    printf '%-10s %-8s %-4s %s\n' $name lto $O "$(count lto/libhqc.dylib)"
  done
done
