#!/usr/bin/env python3
"""Single-fault variants of HQC crypto_kem_dec, at the LLVM IR level.

Reads the -O0 IR of $DEC_BUILD/dec_<p><tag>.ll (default build/hqc-decaps) and writes one .ll per
fault site into $DEC_BUILD/faults_<p><tag>/. $DEC_FUNC names the function holding the
decapsulation logic (default crypto_kem_dec; hqc_kem_decaps_internal for v5.1.0). The fault region
runs from the first call matching $DEC_REGION_START in that function (default the call to
hqc_pke_decrypt; the v5.1.0 driver starts at xof_init_dom_sep, so key regeneration is included) to
the end of the selection loop (the first call through memset_volatile).

Fault models, each at one dynamic instance chosen by the symbolic global @fault_J:
  V  value: an integer SSA value (i1, i8, i32, i64) is replaced by the symbolic global of its type
     when @fault_J equals the current loop iteration (0 outside the loop). Arbitrary value, so it
     covers bit flips, stuck-at and set/reset faults.
  S  skip: a store writes back the old contents instead (instruction skip).
  C  call skip: a call in SKIPPABLE writes its outputs to scratch buffers instead, at that instance.
In the fault region the nsw/nuw flags are dropped: a faulted register wraps, it does not create
poison. For @fault_J outside the executed instances the variant is the original program, so every
property must also hold unfaulted.

Each loop index is the alloca compared against the loop bound in the loop header; its loads and
increment are not fault sites (a corrupted index changes the iteration count, which symbolic
execution cannot bound; out of the model). The exit test itself is a site: a flipped outcome at one
iteration ends the loop early or runs one iteration past the end.
"""
import os
import re
import sys

INT_RE = re.compile(r'^(\s*)(%[\w.]+) = (.*)$')


def region(lines, fstart, start_pat):
    # 'AFTER_INIT:<pat>': start after the last llvm.memset (the zero-initialization of the local
    # arrays) that precedes the first call matching <pat>, so that code a variant adds before that
    # call is in the region too.
    after_init = start_pat.startswith('AFTER_INIT:')
    pat = start_pat.split(':', 1)[1] if after_init else start_pat
    start = next(i for i in range(fstart, len(lines)) if pat in lines[i] and 'call' in lines[i])
    if after_init:
        start = max(i for i in range(fstart, start) if '@llvm.memset' in lines[i]) + 1
    end = next(i for i in range(start, len(lines)) if '@memset_volatile' in lines[i])
    return start, end


# Calls that can be skipped, and which pointer arguments are their outputs. A skipped call writes its
# outputs to scratch buffers, so the real destinations keep their earlier contents. hqc_pke_encrypt
# takes (outputs..., ek, m, theta); keygen and the parser take (outputs..., input); xof_get_bytes
# takes (ctx, out, len) and only out is redirected (the XOF state still advances).
def call_outputs(callee, args):
    if callee == 'hqc_pke_encrypt':
        return args[:len(args) - 3]
    if callee in ('hqc_pke_keygen', 'hqc_c_kem_from_string'):
        return args[:len(args) - 1]
    if callee == 'xof_get_bytes':
        return args[1:2]
    return args[:1]


SKIPPABLE = ('llvm.memcpy.p0.p0.i64', 'xof_init_dom_sep', 'xof_get_bytes', 'hqc_pke_keygen',
             'hqc_c_kem_from_string', 'hqc_pke_decrypt', 'hash_h', 'hash_g', 'hash_j', 'hqc_pke_encrypt')


def result_type(rhs):
    """Integer type of an SSA definition's value, or None."""
    m = re.match(r'(?:call (?:zeroext |signext )?(i\d+) )', rhs)
    if m:
        return m.group(1)
    m = re.match(r'load (?:volatile )?(i\d+),', rhs)
    if m:
        return m.group(1)
    m = re.match(r'icmp ', rhs)
    if m:
        return 'i1'
    m = re.match(r'(?:add|sub|mul|and|or|xor|shl|lshr|ashr)(?: nsw| nuw| exact| disjoint)* (i\d+) ', rhs)
    if m:
        return m.group(1)
    m = re.match(r'(?:zext|sext|trunc)(?: nuw| nsw| nneg)* i\d+ %[\w.]+ to (i\d+)', rhs)
    if m:
        return m.group(1)
    return None


def main():
    p = sys.argv[1] if len(sys.argv) > 1 else '1'
    tag = sys.argv[2] if len(sys.argv) > 2 else ''
    build = os.environ.get('DEC_BUILD', 'build/hqc-decaps')
    func = os.environ.get('DEC_FUNC', 'crypto_kem_dec')
    start_pat = os.environ.get('DEC_REGION_START', '@hqc_pke_decrypt(')
    src = f'{build}/dec_{p}{tag}.ll'
    # DEC_SKIP_STATE=1: only the squeeze call sites, as a true skip (out dir faults_<p><tag>_xs).
    state_skip = os.environ.get('DEC_SKIP_STATE') == '1'
    out = f'{build}/faults_{p}{tag}' + ('_xs' if state_skip else '')
    os.makedirs(out, exist_ok=True)
    text = open(src).read()
    lines = text.split('\n')
    fstart = next(i for i, l in enumerate(lines) if l.startswith('define') and f'@{func}(' in l)
    s, e = region(lines, fstart, start_pat)
    assert fstart < s < e

    # Counted loops in the region: "icmp ult i64 %X, N" (N a constant) with %X = load i64, ptr %IDX.
    # Each loop
    # spans from its header (the first load of IDX) to its exit label.
    loops = []  # (header line, exit-label line, index alloca)
    for i in range(s, e):
        m = re.search(r'(%[\w.]+) = icmp ult i64 (%[\w.]+), \d+(?:,|$)', lines[i])
        if not m:
            continue
        ld = next(j for j in range(i, s, -1) if re.match(rf'\s*{re.escape(m.group(2))} = load i64, ptr (%[\w.]+)', lines[j]))
        idx = re.search(r'load i64, ptr (%[\w.]+)', lines[ld]).group(1)
        br = re.search(r'br i1 %[\w.]+, label %[\w.]+, label %([\w.]+)', lines[i + 1])
        assert br, f'no conditional branch after the loop test at line {i + 1}'
        ex = next(j for j in range(i, len(lines)) if re.match(rf'^{re.escape(br.group(1))}:', lines[j]))
        loops.append((ld, ex, idx))
    assert loops, 'selection loop not found'
    idxs = {l[2] for l in loops}
    index_regs = set()
    for i in range(s, e):
        m = re.match(r'\s*(%[\w.]+) = load i64, ptr (%[\w.]+),', lines[i])
        if m and m.group(2) in idxs:
            index_regs.add(m.group(1))
    for i in range(s, e):
        m = re.match(r'\s*(%[\w.]+) = (?:add|icmp) .*?(%[\w.]+)', lines[i])
        if m and any(re.search(rf'{re.escape(r)}\b', lines[i]) for r in index_regs):
            index_regs.add(m.group(1))

    def loop_of(i):
        for h, x, ix in loops:
            if h <= i < x:
                return ix
        return None

    # @fault_fired is set when the chosen instance executes; the fired check (fired51_1.saw.in)
    # proves that it can be set, so a RESILIENT verdict is never about a fault that cannot happen.
    globals_ir = ('@fault_J = global i64 0\n@fault_v1 = global i1 false\n@fault_v8 = global i8 0\n'
                  '@fault_v32 = global i32 0\n@fault_v64 = global i64 0\n@fault_fired = global i8 0\n')
    sites = []
    for i in range(s, e):
        l = lines[i].split(', !dbg')[0]
        in_loop = loop_of(i)
        cm = re.match(r'\s*(?:%[\w.]+ = )?(?:tail )?call (?:void|zeroext i8|i8|i32|ptr) @([\w.]+)\(', l)
        if state_skip:
            if cm and cm.group(1) == 'xof_get_bytes':
                sites.append(('C', i, cm.group(1), in_loop))
            continue
        if cm and cm.group(1) in SKIPPABLE:
            sites.append(('C', i, cm.group(1), in_loop))
        m = INT_RE.match(l)
        if m and re.search(r'= icmp ult i64 %[\w.]+, \d+$', l):
            # the selection loop's exit test, two sites: forced false at one iteration ends the loop
            # early (E); forced true at one iteration runs past the end (O), which SAW reports as an
            # out-of-bounds access
            ind, reg, rhs = m.groups()
            sites.append(('E', i, reg, 'false', ind, rhs, in_loop))
            sites.append(('E', i, reg, 'true', ind, rhs, in_loop))
            continue
        if m and not l.strip().startswith('call void'):
            ind, reg, rhs = m.groups()
            t = result_type(rhs)
            if t and reg not in index_regs and not any(re.search(rf'{re.escape(x)}\b', rhs) for x in idxs):
                sites.append(('V', i, reg, t, ind, rhs, in_loop))
                continue
        sm = re.match(r'(\s*)store (?:volatile )?(i\d+) (%[\w.]+|-?\d+), ptr (%[\w.]+)', l)
        if sm and sm.group(4) not in idxs:
            sites.append(('S', i, sm, in_loop))
            continue

    manifest = []
    for n, site in enumerate(sites):
        L = list(lines)
        kind = site[0]
        k = f'f{n:03d}'
        iter_load = f'  %{k}.it = load i64, ptr {site[-1]}, align 8' if site[-1] else None
        it = f'%{k}.it' if site[-1] else '0'
        pre = [f'  %{k}.j = load i64, ptr @fault_J, align 8']
        if iter_load:
            pre.append(iter_load)
        pre.append(f'  %{k}.hit = icmp eq i64 %{k}.j, {it}')
        pre += [f'  %{k}.f0 = load i8, ptr @fault_fired, align 1',
                f'  %{k}.f1 = select i1 %{k}.hit, i8 1, i8 %{k}.f0',
                f'  store i8 %{k}.f1, ptr @fault_fired, align 1']
        if kind == 'V':
            _, i, reg, t, ind, rhs, _ = site
            g = {'i1': '@fault_v1', 'i8': '@fault_v8', 'i32': '@fault_v32', 'i64': '@fault_v64'}[t]
            full_rhs = INT_RE.match(lines[i]).group(3)
            new = [f'{ind}%{k}.orig = {full_rhs}'] + pre + [
                f'  %{k}.fv = load {t}, ptr {g}, align 1',
                f'  {reg} = select i1 %{k}.hit, {t} %{k}.fv, {t} %{k}.orig']
            L[i] = '\n'.join(new)
            desc = f'V {t} {reg} = {rhs[:60]}'
        elif kind == 'E':
            _, i, reg, forced, ind, rhs, _ = site
            full_rhs = INT_RE.match(lines[i]).group(3)
            new = [f'{ind}%{k}.orig = {full_rhs}'] + pre + [
                f'  {reg} = select i1 %{k}.hit, i1 {forced}, i1 %{k}.orig']
            L[i] = '\n'.join(new)
            desc = f'E loop exit test forced {forced} ({"early exit" if forced == "false" else "overrun"})'
        elif kind == 'S':
            _, i, sm, _ = site
            ind, t, val, ptr = sm.groups()
            vol = 'volatile ' if ' store volatile ' in ' ' + lines[i].lstrip() else ''
            # The first store to a location in the function: skipping it leaves stale stack, an
            # arbitrary value, which the symbolic global of its type models.
            first = not any(re.search(rf'store (?:volatile )?i\d+ [^,]+, ptr {re.escape(ptr)},', x) for x in lines[fstart:i])
            g = {'i1': '@fault_v1', 'i8': '@fault_v8', 'i32': '@fault_v32', 'i64': '@fault_v64'}[t]
            oldv = f'  %{k}.old = load {t}, ptr {g}, align 1' if first else f'  %{k}.old = load {t}, ptr {ptr}, align 1'
            new = pre + [oldv,
                         f'  %{k}.v = select i1 %{k}.hit, {t} %{k}.old, {t} {val}',
                         f'  store {vol}{t} %{k}.v, ptr {ptr}, align 1']
            L[i] = '\n'.join(new)
            desc = f'S store {vol}{t} {val} -> {ptr}'
        else:
            _, i, callee, _ = site
            call = lines[i].split(', !dbg')[0]
            head, rest = call.split('(', 1)
            args = re.findall(r'ptr (?:align \d+ )?(?:noundef )?(?:nonnull )?(%[\w.]+)', rest)
            outs = call_outputs(callee, args)
            assert outs, f'no output pointer for {callee} at line {i + 1}'
            new = list(pre)
            if state_skip:
                # True skip of a squeeze: the context is saved before the call and, when the fault
                # hits, restored after it, so it does not advance; the output goes to scratch. The
                # restore selects on the saved value rather than the pointer, so the call keeps a
                # single context pointer for override matching.
                ctx = args[0]
                new += [f'  %{k}.sctx = alloca [208 x i8], align 16',
                        f'  call void @llvm.memcpy.p0.p0.i64(ptr align 16 %{k}.sctx, ptr align 8 {ctx}, i64 208, i1 false)']
                post = [f'  %{k}.cnew = load [208 x i8], ptr {ctx}, align 1',
                        f'  %{k}.cold = load [208 x i8], ptr %{k}.sctx, align 1',
                        f'  %{k}.cv = select i1 %{k}.hit, [208 x i8] %{k}.cold, [208 x i8] %{k}.cnew',
                        f'  store [208 x i8] %{k}.cv, ptr {ctx}, align 1']
            for j, o in enumerate(outs):
                scratch = f'%{k}.scratch{j}'
                new += [f'  {scratch} = alloca [65536 x i8], align 16',
                        f'  %{k}.dst{j} = select i1 %{k}.hit, ptr {scratch}, ptr {o}']
                rest = re.sub(rf'(ptr (?:align \d+ )?(?:noundef )?){re.escape(o)}(?=[,)])', rf'\g<1>%{k}.dst{j}', rest, count=1)
            L[i] = '\n'.join(new + [head + '(' + rest] + (post if state_skip else []))
            desc = f'C skip {callee} -> {", ".join(outs)}' + (' (state not advanced)' if state_skip else '')
        for j in range(s, e):
            L[j] = re.sub(r' (nsw|nuw)\b', '', L[j]) if not L[j].lstrip().startswith(('call', 'store')) and 'getelementptr' not in L[j] else L[j]
        body = '\n'.join(L)
        body = body.replace('\ndefine ', '\n' + globals_ir + '\ndefine ', 1)
        open(f'{out}/{k}.ll', 'w').write(body)
        manifest.append(f'{k}\t{lines[site[1]].strip()[:100]}\t{desc}')
    open(f'{out}/MANIFEST.tsv', 'w').write('\n'.join(manifest) + '\n')
    print(f'{len(sites)} fault sites written to {out}/ ({len(loops)} loop(s), index allocas {sorted(idxs)})')


if __name__ == '__main__':
    main()
