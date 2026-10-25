#!/usr/bin/env bash
# Pin the exact bytes of the vendored target under proof, and record where they came from.
#
# The verified C lives in target/pqclean/, vendored verbatim from PQClean's ml-dsa-44/clean at the
# commit below. PQClean's `clean` implementation tracks the pq-crystals/dilithium reference (PQClean
# only adds the PQCLEAN_MLDSA44_CLEAN_ symbol prefix); the pq-crystals commit it imports is recorded
# below so a reviewer can diff target/pqclean against that reference directly.
#
# This script recomputes SHA-256 over the vendored files and compares against the values pinned at
# vendoring time (also recorded in target/README.md). A mismatch means the bytes under proof changed,
# so the proof no longer applies to the recorded source. Exit 0 = unchanged, 1 = changed.
set -euo pipefail

cd "$(dirname "$0")/.."

PQCLEAN_COMMIT="202a8f96315f9ed219387a50f7e40d04af037ea8"   # PQClean, crypto_sign/ml-dsa-44/clean/
PQCRYSTALS_COMMIT="cbcd8753a43402885c90343cd6335fb54712cda1" # pq-crystals/dilithium the clean impl tracks
HQC_COMMIT="f46e54222ffb76706678a9ec8a43cd2188a12ab1"        # gitlab.com/pqc-hqc/hqc, tag v5.0.0 (target/hqc/)
FFT_COMMIT="c94c84dbaaa5b2d92ce15ce1ac8966e1fa9e1d43"        # github.com/ChunTaoPengim/HQC_with_addFFT_tches2026 (target/hqc-fft/)

# expected_sha256  path  (pinned at vendoring; see target/README.md)
EXPECTED="
8f57fd817a50d4e9d0e6f719da352ad503ac0bacf76ea492a7f3885520857af9  target/pqclean/reduce.c
c9fd2b30ef1175f2c66b14c4385a68b22bf500e8349c16d0b5fe1fecf31e5470  target/pqclean/ntt.c
c56a083ce9ea4da55a17e9c2f2da74e7277cdede5b2f8e758e441ff9e0813863  target/pqclean/reduce.h
72e60747ac88f6e3dc9ea7b7b67aed3fa120633bb1e2acfc9a9db948069cecf1  target/pqclean/ntt.h
0210251cea61d26e49b2dad16c4ed86d65474fbffa54c61af7a22c677ddd3cd2  target/pqclean/params.h
9ae04a2bf234ee6fd380826f4cc9f5fe0c55b6a04e0d8818a52da1b68c10e6d2  target/pqclean/poly.c
e6cbe386564946336452ef0694583bc9d8081ed2d81310622644bb9e36560f14  target/pqclean/poly.h
2e258d4407da8cc1fa4ffafdeb2ef1796ffbbdec74d8524e5fa7827d95e533aa  target/pqclean/rounding.h
a1b2b731875c0cf33b251e063917db54c4e251a4b84cc55be780d89cdf642139  target/pqclean/symmetric.h
bf99a54bc1988380418054a18bd5a14d059770e70c1aac23b6d9c914539168e0  target/pqclean/fips202.h
461a4b048c84c27e73daa7b9aaec94942cdcead3ea55dca5cac63bcf4f443d96  target/pqclean/polyvec.c
7fc533b6536819f5d52b31c7a4fa29d15d1f0804138b4ea82ff42bd6a8aaffdf  target/pqclean/polyvec.h
474d7a8c33b45a5e19d9f8a76f501c7ecaa6ca667171a0f40942c71456cbbec2  target/pqclean/sign.c
b1157ba9d0fc7bd89029e77311373c294e52587a32c497c1bdd3c58d9c7fe964  target/pqclean/sign.h
55eded057c9d78299e169ff5329915dc3beba291634186ca69f445c71167b5ea  target/pqclean/packing.h
7ae401d4d5eeb41bfa738d1281d57da3f78f915ca94388d89f4f33cbe6a3fe1e  target/pqclean/randombytes.h
b13ac4224f66fac9f0bd9f1bbee6e102c1d28e86d3ba27ac2e5c5de7036658e0  target/hqc/LICENSE
9d8a1fc01bc5f144bed3e0cd06b3828b4386fc712be4cc2efc8749d64fb36771  target/hqc/gf2x.c
a8c4d13088bedb6467dddc271b155b592d1e8c2ae407f05109edc23a49b3a773  target/hqc/gf2x.h
a1bc67f2fe4bb7a24acd974dbff42d10d96f1f00a3ee37b4504dd6210f5f245e  target/hqc/hqc-1/api.h
d3120e315e7aeb9258b95da8526d9a536b324edd4c358156bc3b99ac2580c3af  target/hqc/hqc-1/parameters.h
024ef0fddbd6b26aa9973d5e96da034e40bdeaf81b11e554d4df883a8adb9928  target/hqc/hqc-3/api.h
9791b1e7aab57065d7734b0dc55f96c14dc0ae3e56082118794c20b79dfc3aa0  target/hqc/hqc-3/parameters.h
27c0bebf61d47627c214d5957198f6845afcfe54e688221c89625d76a94b076b  target/hqc/hqc-5/api.h
7276cda5b2cacfc162408f3354aba7b20088cf9e3c613c2863434ae9a18d1e45  target/hqc/hqc-5/parameters.h
1a754338d50cdd5f723e3067d593a3d969fa412e9e0b0df9cd2b97f51ca9d278  target/hqc/gf.c
d99bde43376d8532eaef3a99ba6647cbf990d14eb5e728147759df5668a8e3b6  target/hqc/gf.h
9e01d64d7b91dd5f8a91a9a9ead64d24cfb9240c94929be9cdd2fcf232b4551c  target/hqc/reed_solomon.c
35582ebecd5ff2fb8be628453178d4672e1bdec4532b699a06e9d6b6c85f60da  target/hqc/fft.h
95094245695db2847fc591523467f7005c0c32f1d663d52737a48a29b39bda6d  target/hqc/crypto_memset.h
0261e1f19e20251d3308bab300eff3eb33f00eb57c931d8bda41854ee28ca25b  target/hqc/hqc-1/reed_solomon.h
353c8e9a8846087229f444be055c4291f710d571f995a098228cd3a1b5d2e39b  target/hqc/hqc-3/reed_solomon.h
93256f74d61759aa4c3cdde932341ab3396d43c4da5afb19b1528ee5a3b74757  target/hqc/hqc-5/reed_solomon.h
520299dee42260aa13ed9b3bd7e19d8a87f553f60e81ca0b1738efc19e1468aa  target/hqc/avx2/gf2x.h
f66470b16dc27541a10766297bd5baa8c031241c73d2551c0dcfacef1bad4276  target/hqc/avx2/hqc-1/gf2x.c
4a4c9bb9c5bc46d2bc2ea4edccff3ae7562d90068be3c4b1a67d54e3f12a5fa3  target/hqc/avx2/hqc-3/gf2x.c
61cd83cac56be72d4c2e5980b0c04602d51d862a40ac41de98a06f7e053b5f4a  target/hqc/avx2/hqc-5/gf2x.c
67d797df231275bfe2ab49ba7dffc1d8779fee349ffc6b6eab4703dc00e1e2d2  target/hqc/avx2/hqc-1/parameters.h
6f8fc90e9977fb2c56aa29a072ba0ac63d83dd46019f5ce2306c96b2c16adf0b  target/hqc/avx2/hqc-3/parameters.h
151c83ea287d686c391c062f6d31ad1fe40ea2310fb221ff8f46e269a3793acf  target/hqc/avx2/hqc-5/parameters.h
9c81e85b45c1e3d8a9e8288e9c25d538ca1574a740665c41c522b8ccbfafe1ad  target/hqc/reed_muller.c
05a4f24eee801f55507f41e1f9e4550b81c35710227fa8ca8faf7918595cd18b  target/hqc/reed_muller.h
c2bb3b7be30a125abdfdbd60de6321c9b4edd52f01d54bdfcfcee78fa632c8b1  target/hqc/data_structures.h
c207b7708c2e7b894c31b1d31166534af73bc07d855b4d99d3e956862c7626af  target/hqc/code.c
afbd3a2e0baf952a5a0d08175deb94e6f89236c207132f3ce6ff613064cbe8d3  target/hqc/code.h
906d712f2e4b67f172c7cc5596c23d618c3004eb9173e1f4f94cc8bbf2b89c24  target/hqc/crypto_memset.c
6b0382b16279f26ff69014300541967a356a666eb0b91b422f6862f6b7dad17e  target/hqc-fft/UNLICENSE
b89136baf5741b6d66e417d0f8f22063ec2e9891c6da45010c6d3a51c13a6643  target/hqc-fft/gf264_ref/bc_1.h
c513eb095052d3306de7d4d7671b53948a46184912fee22293c33dce06dffc39  target/hqc-fft/gf264_ref/bc_1_ref.c
d57733c56817c338e1f98135d1bd7d94cc0a993576555e7bc692138ec4af8ca8  target/hqc-fft/gf264_ref/bc_256.h
c5cce4754b1735ebf39021ee909cfa382b78d94f3386b486c64de4a430a00977  target/hqc-fft/gf264_ref/bc_256_ref.c
258e72ab0bbbc62312d20f6fb2a800e9683d672ac55af0893a71277467568476  target/hqc-fft/gf264_ref/btfy.c
f1944407e48ea86984b05b2e84adf64099c6795ffec4d19bd6e1da445b97447e  target/hqc-fft/gf264_ref/btfy.h
33c24876dcea5229a994bfd6d6b21cbf0a05813cf9f397a80ea24464c9bbe80d  target/hqc-fft/gf264_ref/btfy_consts_2stages.c
f031d6a889a7faede8697ebfce665267929ee3bf14cf1f86d69af855cc8863b8  target/hqc-fft/gf264_ref/cantor_to_gf264.c
e721a883a4c584107633fc667319f7f66c1a47a4f0c80d18d87ebbfea5480b77  target/hqc-fft/gf264_ref/cantor_to_gf264.h
481e359599a7c287f9d3cff484bd10ddd842e861de81e974c34dcf8d3d929e8a  target/hqc-fft/gf264_ref/cantor_to_gf264_2x.c
0ed85188eb9acd6f1918479564784b2eda636e70b33111c59136ce2cb05434ca  target/hqc-fft/gf264_ref/dencoder.c
237927c75ea44380f4158df64ae49b9df017f5ea982a6cd4d4cd70bfa79069ba  target/hqc-fft/gf264_ref/dencoder.h
b54f8cb5ba433eb007d58714ccc92e605abadb4ce2bf9469d0a0a922258bd098  target/hqc-fft/gf264_ref/gf264.c
f15893b07a032abb0a3701b02cca9c188634443b7d7f73f8684b52c79ff57d65  target/hqc-fft/gf264_ref/gf264.h
359f955b4bd0cc48a221bf67e60943e52e4c2bb26a84d2a6c4022b376220627c  target/hqc-fft/gf264_ref/polymul.c
1dae4fc41908985af8c545b32a3bd7fef0bc3da6ff89770f14724f716d45835e  target/hqc-fft/gf264_ref/polymul.h
a67dae6c95813bd0888fd4a939b6b115c628d9c16461a58cd8e55a897437c2d7  target/hqc-fft/gf264_ref/polymul_hqclen.h
45ceff27d3d7553ac7ede76e4797f68de5b1eb5710b92516b9b47fe93454202c  target/hqc-fft/gf264_ref/polymul_hqclen_ref.c
"

SHA="shasum -a 256"; command -v sha256sum >/dev/null 2>&1 && SHA="sha256sum"

echo ">> verifying vendored target bytes (PQClean $PQCLEAN_COMMIT, tracks pq-crystals $PQCRYSTALS_COMMIT; HQC $HQC_COMMIT; HQC-FFT $FFT_COMMIT)"
fail=0
while read -r want path; do
  [ -z "${want:-}" ] && continue
  got=$($SHA "$path" | awk '{print $1}')
  if [ "$got" = "$want" ]; then
    echo "   ok    $path"
  else
    echo "   CHANGED $path"; echo "     expected $want"; echo "     got      $got"; fail=1
  fi
done <<< "$EXPECTED"

if [ "$fail" -ne 0 ]; then
  echo "!! target bytes differ from the pinned snapshot; the proof does not apply to the current files." >&2
  exit 1
fi
echo ">> target identity OK: vendored bytes match the pinned snapshot."
echo ">> to confirm against pq-crystals: diff target/pqclean against pq-crystals/dilithium@$PQCRYSTALS_COMMIT"
echo "   (ref/reduce.c, ref/ntt.c, ...), modulo the PQCLEAN_MLDSA44_CLEAN_ prefix."
