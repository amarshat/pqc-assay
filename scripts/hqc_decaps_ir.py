#!/usr/bin/env python3
"""Replace the vectorizer's poison placeholders in optimized IR so that SAW 1.5.1 can execute it.

Crucible (SAW 1.5.1) panics on evaluating a poison constant ("Attempting to evaluate poison value"),
and clang 22 at -O2 writes three placeholder shapes that never let a poison lane reach a use:

  1. %v = insertelement <N x T> poison, T %x, i64 0
     followed, as the only use of %v, by
     %w = shufflevector <N x T> %v, <N x T> poison, <N x i32> zeroinitializer
     (a broadcast of lane 0: every result lane is lane 0 of %v, which is %x).
  2. the second operand of such a broadcast shufflevector (never selected by an all-zero mask).
  3. %v = insertelement <N x T> <T poison, T c1, ...>, T %x, i64 0  (lane 0 overwritten).

Each is rewritten with zero in place of poison, which does not change any lane that is observed.
The script checks the shape of every poison it replaces and fails on any other poison, so a new
compiler pattern stops the build instead of being rewritten silently.
Usage: hqc_decaps_ir.py in.ll out.ll
"""
import re
import sys


def main():
    src, dst = sys.argv[1], sys.argv[2]
    lines = open(src).read().split('\n')
    # uses of each SSA name, per function (local names repeat across functions)
    uses = {}
    fn = 0
    for i, l in enumerate(lines):
        if l.startswith('define '):
            fn += 1
        for r in re.findall(r'%[\w.]+', l.split(' = ', 1)[1] if ' = ' in l else l):
            uses.setdefault((fn, r), []).append(i)
    fn_of = []
    fn = 0
    for l in lines:
        if l.startswith('define '):
            fn += 1
        fn_of.append(fn)
    out = list(lines)
    n = 0
    for i, l in enumerate(lines):
        if 'poison' not in l:
            continue
        m = re.match(r'^(\s*)(%[\w.]+) = insertelement <(\d+) x (\w+)> poison, \4 (%[\w.]+|-?\d+), i64 0$', l)
        if m:
            v = m.group(2)
            us = [u for u in uses.get((fn_of[i], v), []) if u != i]
            ok = len(us) == 1 and re.match(
                rf'^\s*%[\w.]+ = shufflevector <{m.group(3)} x {m.group(4)}> {re.escape(v)}, '
                rf'<{m.group(3)} x {m.group(4)}> poison, <{m.group(3)} x i32> zeroinitializer$', lines[us[0]])
            if not ok:
                sys.exit(f'!! line {i + 1}: insertelement into poison not used only by a lane-0 broadcast')
            out[i] = l.replace('> poison,', '> zeroinitializer,', 1)
            n += 1
            continue
        m = re.match(r'^(\s*%[\w.]+ = shufflevector <(\d+) x (\w+)> %[\w.]+, <\2 x \3> )poison(, <\2 x i32> zeroinitializer)$', l)
        if m:
            out[i] = m.group(1) + 'zeroinitializer' + m.group(4)
            n += 1
            continue
        m = re.match(r'^(\s*%[\w.]+ = insertelement <(\d+) x (\w+)> <)\3 poison((?:, \3 -?\d+)+>, \3 (?:%[\w.]+|-?\d+), i64 0)$', l)
        if m:
            out[i] = m.group(1) + m.group(3) + ' 0' + m.group(4)
            n += 1
            continue
        if l.lstrip().startswith(('declare', '!', ';', 'attributes')):
            continue
        sys.exit(f'!! line {i + 1}: poison in an unrecognized shape: {l.strip()[:120]}')
    open(dst, 'w').write('\n'.join(out))
    print(f'{n} poison placeholders replaced')


if __name__ == '__main__':
    main()
