#!/usr/bin/env bash
# Source-level mutants of the HQC C under proof: does the unchanged SAW script reject a wrong program?
#
# The gated mutants (make hqc, make hqc-avx) perturb the specification and must fail; they show the
# equality is checked. This script perturbs the C instead: each mutant is a one-line change to a copy
# of the vendored file (target/ is never edited), compiled exactly as the gated run compiles it, and
# the unchanged proof script for hqc-1 is run against it. A mutant counts as caught when saw exits
# non-zero. A measurement, out of band (make hqc-c-mutants); it never gates the build.
#
# Usage: scripts/hqc_c_mutants.sh [ref|avx|all]   (default all; avx needs AVX_CLANG, see Makefile)
set -uo pipefail
cd "$(dirname "$0")/.."
ROOT="$(pwd)"; export PATH="$ROOT/.tools/bin:$PATH"
WHICH="${1:-all}"
AVX_CLANG="${AVX_CLANG:-/opt/homebrew/opt/llvm@22/bin/clang}"
M="$ROOT/build/hqc/cmut"; rm -rf "$M"; mkdir -p "$M"
printf '%-22s %-9s %-7s %s\n' mutant verdict seconds "first failure reported by saw"

run_mutant() {  # name  kind(ref|avx)  sed-expression
  local name=$1 kind=$2 expr=$3 d="$M/$1" src dst bc script
  mkdir -p "$d/proof/hqc" "$d/build/hqc"
  if [ "$kind" = ref ]; then src=target/hqc/gf2x.c; script=karatsuba_1.saw; else src=target/hqc/avx2/hqc-1/gf2x.c; script=avx_1.saw; fi
  dst="$d/gf2x.c"; sed -e "$expr" "$src" > "$dst"
  if cmp -s "$src" "$dst"; then printf '%-22s %-9s %-7s %s\n' "$name" ERROR - "mutation did not apply"; return; fi
  [ "$(diff "$src" "$dst" | grep -c '^<')" -le 1 ] || { printf '%-22s %-9s %-7s %s\n' "$name" ERROR - "mutation touched more than one line"; return; }
  if [ "$kind" = ref ]; then
    clang -c -emit-llvm -O0 -g -I target/hqc/hqc-1 -I target/hqc -o "$d/build/hqc/gf2x_1.bc" "$dst" || return
  else
    "$AVX_CLANG" --target=x86_64-apple-darwin -isysroot "$(xcrun --show-sdk-path)" -D_FORTIFY_SOURCE=0 -O0 -mavx -mavx2 -mbmi -mpclmul \
      -I target/hqc/avx2/hqc-1 -I target/hqc/hqc-1 -I target/hqc/avx2 -I target/hqc -c -emit-llvm -o "$d/build/hqc/avx_1.raw.bc" "$dst" 2>/dev/null || return
    python3 scripts/hqc_avx_ir.py "$(dirname "$AVX_CLANG")/" "$d/build/hqc/avx_1.raw.bc" "$d/build/hqc/avx_1.bc" --slack > /dev/null || return
  fi
  cp "proof/hqc/$script" "$d/proof/hqc/"
  local start; start=$(date +%s)
  (cd "$d" && CRYPTOLPATH="$ROOT/model/cryptol/hqc" saw "proof/hqc/$script" > saw.log 2>&1); local rc=$?
  local secs=$(( $(date +%s) - start ))
  local why; why=$(grep -m1 -E 'Subgoal failed: [a-z_0-9]+|Symbolic execution failed|error:' "$d/saw.log" | cut -c1-70)
  if [ $rc -ne 0 ]; then printf '%-22s %-9s %-7s %s\n' "$name" caught "$secs" "${why:-exit $rc}"; else printf '%-22s %-9s %-7s %s\n' "$name" MISSED "$secs" "saw exit 0"; fi
}

if [ "$WHICH" != avx ]; then
  run_mutant ref-schoolbook-carry ref '/r\[base + j + 1\] \^= (b\[j\] >> inv) \& mask;/d'
  run_mutant ref-karatsuba-mid    ref 's/uint64_t mid = zmid\[i\] \^ z0i \^ z2i;/uint64_t mid = zmid[i] ^ z2i;/'
  run_mutant ref-child-overlap    ref 's/uint64_t \*child_buffer = tmp_buffer + 8 \* n;/uint64_t *child_buffer = tmp_buffer + 7 * n;/'
  run_mutant ref-reduce-shift     ref 's/a\[i + VEC_N_SIZE_64 - 1\] >> (PARAM_N \& 0x3F);/a[i + VEC_N_SIZE_64 - 1] >> ((PARAM_N - 1) \& 0x3F);/'
  run_mutant ref-reduce-mask      ref '/o\[VEC_N_SIZE_64 - 1\] \&= BITMASK(PARAM_N, 64);/d'
fi
if [ "$WHICH" != ref ]; then
  run_mutant avx-prefix-xor       avx 's/B\[i\] = B\[i - 1\] \^ A\[i\];/B[i] = A[i];/'
fi
