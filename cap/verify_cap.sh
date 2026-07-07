#!/usr/bin/env bash
# Machine-check the Cap-V1 Kani harnesses (format bijection, delegation attenuation, accept gate,
# signature binding) with Kani (CBMC backend). Exits 0 only if every harness verifies and none fails.
# See docs/cap/CAP-V1.md for which harnesses carry independent content vs are definition checks.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"

command -v cargo-kani >/dev/null 2>&1 || command -v kani >/dev/null 2>&1 || {
  echo "FAIL: kani not found (install with 'cargo install --locked kani-verifier && cargo kani setup')"; exit 2; }

cd "$HERE"
OUT="$(cargo kani 2>&1)"
echo "$OUT"

# The final line reports "N successfully verified harnesses, M failures, T total".
# Pass only if failures == 0 and every harness verified (verified == total, total > 0).
LINE="$(printf '%s\n' "$OUT" | grep -E 'successfully verified harnesses' | tail -1)"
VERIFIED="$(printf '%s\n' "$LINE" | sed -E 's/.* ([0-9]+) successfully verified harnesses.*/\1/')"
FAILURES="$(printf '%s\n' "$LINE" | sed -E 's/.*harnesses, ([0-9]+) failures.*/\1/')"
TOTAL="$(printf '%s\n' "$LINE" | sed -E 's/.*failures, ([0-9]+) total.*/\1/')"

if [ -n "$LINE" ] && [ "$FAILURES" = "0" ] && [ "$VERIFIED" = "$TOTAL" ] && [ "$TOTAL" -gt 0 ]; then
  echo "OK: Cap-V1 Kani properties verified ($VERIFIED/$TOTAL harnesses, 0 failures)"
  exit 0
fi
echo "FAIL: expected all harnesses verified and 0 failures; got '$LINE'"
exit 1
