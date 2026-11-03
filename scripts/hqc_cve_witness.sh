#!/usr/bin/env bash
# CVE-2024-54137 on the real code (paper 2, Section 3): build the hqc-128 reference implementation of
# the HQC submissions of 2024-10-30 (vulnerable) and 2025-02-19 (fixed) from the HQC team's archive,
# with scripts/hqc-cve/witness.cpp as the driver, and run both. The driver flips one bit of v in an
# honest ciphertext and reports whether decapsulation returns the accept key SHAKE256-512(m'||u||v)
# or the reject key SHAKE256-512(sigma||u||v), each recomputed from the implementation's own
# decryption and hash. Expected: 2024-10-30 returns the accept key, 2025-02-19 the reject key.
# Compiles and runs code from the downloaded archive (hashes pinned below).
set -eu
# The reference code's gf2x.cpp uses NTL (brew install ntl; GMP comes with it).
NTL=${NTL:-$(brew --prefix ntl)}; GMP=${GMP:-$(brew --prefix gmp)}
root=$(cd "$(dirname "$0")/.." && pwd); cd "$root"
B=build/hqc-cve; mkdir -p $B
ARCH=$B/archive_submissions.zip
[ -f $ARCH ] || curl -sL -o $ARCH https://pqc-hqc.org/doc/archive_submissions.zip
echo "c7a156416cce979763cdf8a1b29dbdf7edbc9cd43fd17a10ea64d9ed6aead886  $ARCH" | shasum -a 256 -c -
for d in 2024-10-30 2025-02-19; do
  (cd $B && unzip -q -o archive_submissions.zip hqc-submission_$d.zip)
  case $d in
    2024-10-30) h=d62d5416dd2beaa628a66e24c3a39ecd212eaebdcbbee2a3960d8e3250b9dfd6 ;;
    2025-02-19) h=aad85cc1e29213a11c40523eb67f583bec9adcefef208952beba8ee3cd246736 ;;
  esac
  echo "$h  $B/hqc-submission_$d.zip" | shasum -a 256 -c -
  mkdir -p $B/$d; (cd $B/$d && unzip -q -o ../hqc-submission_$d.zip 'Reference_Implementation/hqc-128/*')
  R=$B/$d/Reference_Implementation/hqc-128
  ${CXX:-clang++} -std=c++11 -O2 -w -I $R/src -I $R/lib/fips202 -I $NTL/include -x c++ \
    $R/src/code.cpp $R/src/fft.cpp $R/src/gf.cpp $R/src/gf2x.cpp $R/src/hqc.cpp $R/src/kem.cpp \
    $R/src/parsing.cpp $R/src/reed_muller.cpp $R/src/reed_solomon.cpp $R/src/shake_ds.cpp \
    $R/src/shake_prng.cpp $R/src/vector.cpp $R/lib/fips202/fips202.c scripts/hqc-cve/witness.cpp \
    -x none -L $NTL/lib -L $GMP/lib -lntl -lgmp -o $B/witness_$d
  echo "== HQC submission $d, hqc-128 reference"
  $B/witness_$d
done
