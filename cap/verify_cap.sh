#!/usr/bin/env bash
# Machine-check the Cap-V1 TBS bijection/injectivity properties with Kani (CBMC backend).
# Exits 0 only if all three harnesses verify and none fails.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"

command -v cargo-kani >/dev/null 2>&1 || command -v kani >/dev/null 2>&1 || {
  echo "FAIL: kani not found (install with 'cargo install --locked kani-verifier && cargo kani setup')"; exit 2; }

cd "$HERE"
OUT="$(cargo kani 2>&1)"
echo "$OUT"

# The final line reports "N successfully verified harnesses, M failures, T total".
if printf '%s\n' "$OUT" | grep -qE '3 successfully verified harnesses, 0 failures, 3 total'; then
  echo "OK: Cap-V1 TBS bijective + injective (3/3 Kani harnesses verified)"
  exit 0
fi
echo "FAIL: expected 3 verified harnesses and 0 failures"
exit 1
