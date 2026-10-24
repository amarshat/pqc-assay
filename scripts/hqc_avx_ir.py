#!/usr/bin/env python3
"""Normalize the LLVM IR of the HQC AVX2 gf2x.c for SAW (crucible-llvm 0.9, SAW 1.5.1).

Usage: hqc_avx_ir.py <llvm-bindir> <in.bc> <out.bc> [--slack] [--poison=ones]

The C in target/hqc/avx2 is not edited. The bitcode clang 22 emits for it is rewritten in three
places, each listed in docs/ASSUMPTIONS.md (A-HQC-AVX) because the proof is about the rewritten IR:

1. Vector constants with poison lanes. clang lowers `(__m256i){a, b, 0, 0}` to `insertelement` on
   a constant such as `<i64 0, i64 0, i64 0, i64 poison>`. Crucible refuses to evaluate a poison
   lane ("Attempting to evaluate poison value"). Every poison lane is replaced by 0, and a whole
   `poison` vector operand (the unused second operand of `shufflevector`) by `zeroinitializer`.
   This refines an undefined lane to one value; the lanes are overwritten before use, so the
   program's defined behaviour does not change. That the lanes are overwritten is read from the
   source; --poison=ones replaces them by all-ones instead, and a proof that passes on both
   bitcodes shows the result does not depend on the choice (make hqc-avx-poison, out of band).

2. One `<4 x i64>` of slack on the static arrays `toom_3_mult.W0` and `toom_3_mult.W2`. In the
   hqc-1 and hqc-3 toom_3_mult the loop "W2 = (W2 + W0)/x" loads 32 bytes from one 64-bit word
   past the start of each vector, so its last iteration reads one word past the end of both
   arrays (an out-of-bounds read in the vendored code; the word read is overwritten before it is
   used). Crucible stops at the read. The arrays get one extra vector, which is zero and never
   written, so the proof covers the program as the C compiler lays it out only under the
   assumption that the over-read does not fault. Only with --slack, which the Makefile passes for
   hqc-1 and hqc-3; hqc-5's arrays keep their declared size, so its proof witnesses that its
   toom_3_mult stays in bounds.

3. Constant GEPs with a negative index. `&ro256[T] - 2` (uint64_t arithmetic on a static array)
   is folded by clang into `getelementptr (i64, getelementptr (..., i64 T), i64 -2)`, which
   Crucible rejects ("Computed offset overflow in constant GEP"). It is rewritten as a byte
   offset from the array base, `getelementptr (i8, ptr @ro256, i64 32*T - 16)`, the same address.
"""
import re
import subprocess
import sys


def main():
    bindir, src, dst = sys.argv[1:4]
    slack = '--slack' in sys.argv[4:]
    ones = '--poison=ones' in sys.argv[4:]
    lane32, lane64 = ('i32 -1', 'i64 -1') if ones else ('i32 0', 'i64 0')
    vec = (lambda m: f'<{m.group(1)} x i{m.group(2)}> <{", ".join([f"i{m.group(2)} -1"] * int(m.group(1)))}>') if ones else (lambda m: f'<{m.group(1)} x i{m.group(2)}> zeroinitializer')
    ll = subprocess.run([f'{bindir}/llvm-dis', src, '-o', '-'], check=True, capture_output=True, text=True).stdout
    n_poison = len(re.findall(r'\bpoison\b', ll))
    ll = re.sub(r'<(\d+) x i(32|64)> poison', vec, ll)
    ll = re.sub(r'i64 poison', lane64, ll)
    ll = re.sub(r'i32 poison', lane32, ll)
    assert not re.search(r'\bpoison\b', re.sub(r'^;.*$', '', ll, flags=re.M)), 'unexpected poison form left'
    n_slack = 0
    if slack:
        ll, n_slack = re.subn(r'^(@toom_3_mult\.(?:W0|W2) = internal global )\[(\d+) x <4 x i64>\]',
                              lambda m: f'{m.group(1)}[{int(m.group(2)) + 1} x <4 x i64>]', ll, flags=re.M)
        assert n_slack == 2, f'expected W0 and W2, found {n_slack}'
    gep = re.compile(r'getelementptr inbounds \(i64, ptr getelementptr inbounds \(\[(\d+) x <4 x i64>\], '
                     r'ptr (@[\w.]+), i64 0, i64 (\d+)\), i64 -(\d+)\)')
    ll, n_gep = gep.subn(lambda m: f'getelementptr inbounds (i8, ptr {m.group(2)}, i64 {int(m.group(3)) * 32 - int(m.group(4)) * 8})', ll)
    assert not re.search(r'getelementptr[^\n]*, i64 -\d', ll), 'a negative constant index remains'
    subprocess.run([f'{bindir}/llvm-as', '-', '-o', dst], check=True, input=ll, text=True)
    print(f'{dst}: {n_poison} poison lanes set to {"all ones" if ones else "zero"}, {n_slack} arrays given one vector of slack, {n_gep} constant GEPs rewritten')


if __name__ == '__main__':
    main()
