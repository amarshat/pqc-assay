#!/usr/bin/env python3
"""Normalize the LLVM IR of the HQC AVX2 gf2x.c for SAW (crucible-llvm 0.9, SAW 1.5.1).

Usage: hqc_avx_ir.py <llvm-bindir> <in.bc> <out.bc> [--slack] [--poison=symbolic|zero|ones]

The C in target/hqc/avx2 is not edited. The bitcode clang 22 emits for it is rewritten in three
places, each listed in docs/ASSUMPTIONS.md (A-HQC-AVX) because the proof is about the rewritten IR:

1. Vector constants with poison lanes. clang lowers `(__m256i){a, b, 0, 0}` to `insertelement` on
   a constant such as `<i64 0, i64 0, i64 0, i64 poison>`, and `shufflevector` gets a whole
   `poison` second operand. Crucible refuses to evaluate a poison lane ("Attempting to evaluate
   poison value"). By default (--poison=symbolic) every such operand is replaced by a load from its
   own fresh global `@__poison_k` (declared at the end of the module; the defined lanes of a partly
   poison constant are re-inserted after the load), and the sidecar `<out.bc>.poison.saw` lists the
   globals so that the SAW specs allocate each with fresh symbolic contents. A proof on that bitcode
   therefore holds for every value of every poison lane: it does not refine poison to one value,
   it quantifies over it. Before rewriting, poison_never_read checks that no poison lane is ever read
   (every chain overwrites it, every shuffle selects around it), so the rewrite does not change the
   program's semantics and the symbolic globals are a second line of evidence (the proof shows the
   result does not depend on them). --poison=zero and --poison=ones are the earlier single-value
   refinements, kept for the record (make hqc-avx-poison measured both before 2026-10-25).

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


def poison_never_read(ll):
    """Check, per function, that no poison lane can be observed. Two shapes occur: (a) an
    insertelement chain that starts from a vector with poison lanes and whose intermediates have
    no use except the next insertelement of the chain, ending in a vector with every lane written;
    (b) a shufflevector whose second operand is poison and whose mask selects only lanes of the first
    operand. Any other instruction with a poison operand fails the build. When this holds, the
    program's value at every instruction other than the chain intermediates is the same whatever the
    poison lanes are, so replacing them by globals of any contents does not change the semantics.
    Returns (chains, shuffles)."""
    chains = shuffles = 0
    for fn in re.split(r'\ndefine ', ll)[1:]:
        fn = fn.split('\n}\n')[0]
        uses, defs = {}, {}
        for l in fn.split('\n')[1:]:
            if l.lstrip().startswith(';'):
                continue
            m = re.match(r'\s*(%[\w.]+) = (.*)', l)
            if m:
                defs[m.group(1)] = m.group(2)
            for u in re.findall(r'%[\w.]+', m.group(2) if m else l):
                uses.setdefault(u, []).append(m.group(1) if m else None)
        for v, d in defs.items():
            if not re.search(r'\bpoison\b', d):
                continue
            if d.startswith('insertelement'):
                n = int(re.search(r'<(\d+) x', d).group(1))
                c = re.match(r'insertelement <\d+ x i\d+> (poison|<[^>]*>),', d).group(1)
                undef = set(range(n)) if c == 'poison' else {i for i, t in enumerate(c.strip('<>').split(', ')) if 'poison' in t}
                cur, dd = v, d
                while True:
                    undef.discard(int(re.search(r'i32 (\d+)\s*$', dd).group(1)))
                    if not undef:
                        break
                    us = uses.get(cur, [])
                    nx = us[0] if len(us) == 1 else None
                    assert nx and re.match(r'insertelement <[^>]*> ' + re.escape(cur) + r',', defs.get(nx, '')), \
                        f'poison lanes {sorted(undef)} of {v} reach a use other than insertelement: {us}'
                    cur, dd = nx, defs[nx]
                chains += 1
            elif d.startswith('shufflevector'):
                m = re.match(r'shufflevector <(\d+) x \w+> %[\w.]+, <\d+ x \w+> poison, <\d+ x i32> <(.*)>$', d.strip())
                assert m and all(int(x.split()[-1]) < int(m.group(1)) for x in m.group(2).split(', ')), \
                    f'a shufflevector may select a poison lane: {d}'
                shuffles += 1
            else:
                raise AssertionError(f'poison operand outside the two handled shapes: {v} = {d}')
    return chains, shuffles


def main():
    bindir, src, dst = sys.argv[1:4]
    slack = '--slack' in sys.argv[4:]
    mode = 'symbolic'
    for a in sys.argv[4:]:
        if a.startswith('--poison='):
            mode = a[len('--poison='):]
    assert mode in ('symbolic', 'zero', 'ones'), mode
    ll = subprocess.run([f'{bindir}/llvm-dis', src, '-o', '-'], check=True, capture_output=True, text=True).stdout
    n_poison = len(re.findall(r'\bpoison\b', re.sub(r'^;.*$', '', ll, flags=re.M)))
    n_chains, n_shuf = poison_never_read(ll)
    globals_ = []                                   # (name, lane width) for the sidecar SAW snippet
    if mode == 'symbolic':
        # Each poison operand becomes a load from its own fresh global @__poison_k, declared at the
        # end of the module; a constant vector with some poison lanes is the load with the defined
        # lanes re-inserted. The SAW specs allocate every @__poison_k with fresh symbolic contents
        # (the sidecar <dst>.poison.saw lists them), so the proofs hold for every lane value.
        out, k = [], 0
        vec_const = re.compile(r'<(\d+) x i(32|64)> (<(?:i(?:32|64) (?:-?\d+|poison)(?:, )?)+>|poison)')
        for line in ll.split('\n'):
            if 'poison' in line and not line.lstrip().startswith(';') and not line.startswith('@'):
                assert ' phi ' not in line, f'poison in a phi: {line}'
                indent = line[:len(line) - len(line.lstrip())]
                def repl(m):
                    nonlocal k
                    n, bits, body = int(m.group(1)), m.group(2), m.group(3)
                    if 'poison' not in body:
                        return m.group(0)
                    assert not (line.lstrip().split(' = ')[-1].startswith('shufflevector') and m.end() == len(line.rstrip())), \
                        f'poison in a shufflevector mask is not handled: {line}'
                    name = f'__poison_{k}'; k += 1
                    globals_.append((name, bits))
                    cur = f'%{name}'
                    out.append(f'{indent}{cur} = load <{n} x i{bits}>, ptr @{name}, align 32')
                    if body != 'poison':
                        lanes = re.findall(r'i(?:32|64) (-?\d+|poison)', body)
                        assert len(lanes) == n, body
                        for li, v in enumerate(lanes):
                            if v != 'poison':
                                nxt = f'%{name}.{li}'
                                out.append(f'{indent}{nxt} = insertelement <{n} x i{bits}> {cur}, i{bits} {v}, i32 {li}')
                                cur = nxt
                    return f'<{n} x i{bits}> {cur}'
                line = vec_const.sub(repl, line)
            out.append(line)
        ll = '\n'.join(out)
        ll += '\n' + '\n'.join(f'@{name} = internal global <4 x i{bits}> zeroinitializer, align 32' for name, bits in globals_) + '\n'
    else:
        ones = mode == 'ones'
        lane32, lane64 = ('i32 -1', 'i64 -1') if ones else ('i32 0', 'i64 0')
        vec = (lambda m: f'<{m.group(1)} x i{m.group(2)}> <{", ".join([f"i{m.group(2)} -1"] * int(m.group(1)))}>') if ones else (lambda m: f'<{m.group(1)} x i{m.group(2)}> zeroinitializer')
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
    def gep_bytes(m):
        # &arr[T] - k as i64 words is byte 32 T - 8 k of arr; the rewrite is only made when that byte
        # offset lies inside the array, so the new address is the old one and is in bounds.
        size, t, k = int(m.group(1)), int(m.group(3)), int(m.group(4))
        off = t * 32 - k * 8
        assert 0 <= off <= size * 32 and t <= size, f'GEP rewrite out of range: {m.group(0)}'
        return f'getelementptr inbounds (i8, ptr {m.group(2)}, i64 {off})'
    ll, n_gep = gep.subn(gep_bytes, ll)
    assert not re.search(r'getelementptr[^\n]*, i64 -\d', ll), 'a negative constant index remains'
    subprocess.run([f'{bindir}/llvm-as', '-', '-o', dst], check=True, input=ll, text=True)
    with open(dst + '.poison.saw', 'w') as f:
        f.write('// GENERATED by scripts/hqc_avx_ir.py: the globals that replace poison operands; each is allocated\n'
                '// with fresh symbolic contents by the specs, so the proofs quantify over every lane value.\n')
        f.write('let poison_globals = [' + ', '.join(f'("{n}", {b})' for n, b in globals_) + '];\n')
    how = {'symbolic': f'replaced by {len(globals_)} fresh symbolic globals', 'zero': 'set to zero', 'ones': 'set to all ones'}[mode]
    print(f'{dst}: {n_poison} poison lanes (never read: {n_chains} insertelement chains, {n_shuf} shuffles) {how}, {n_slack} arrays given one vector of slack, {n_gep} constant GEPs rewritten')


if __name__ == '__main__':
    main()
