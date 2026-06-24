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

# expected_sha256  path  (pinned at vendoring; see target/README.md)
EXPECTED="
8f57fd817a50d4e9d0e6f719da352ad503ac0bacf76ea492a7f3885520857af9  target/pqclean/reduce.c
c9fd2b30ef1175f2c66b14c4385a68b22bf500e8349c16d0b5fe1fecf31e5470  target/pqclean/ntt.c
c56a083ce9ea4da55a17e9c2f2da74e7277cdede5b2f8e758e441ff9e0813863  target/pqclean/reduce.h
72e60747ac88f6e3dc9ea7b7b67aed3fa120633bb1e2acfc9a9db948069cecf1  target/pqclean/ntt.h
0210251cea61d26e49b2dad16c4ed86d65474fbffa54c61af7a22c677ddd3cd2  target/pqclean/params.h
"

SHA="shasum -a 256"; command -v sha256sum >/dev/null 2>&1 && SHA="sha256sum"

echo ">> verifying vendored target bytes (PQClean $PQCLEAN_COMMIT, tracks pq-crystals $PQCRYSTALS_COMMIT)"
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
