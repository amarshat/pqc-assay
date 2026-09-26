#!/usr/bin/env python3
"""Emit `spec obligations mutants` for one SAW script.

Pairs each llvm_verify/mir_verify obligation with the `fails (...)` guard aimed at the same spec.
Two conventions exist in this tree: qseal/ keeps the spec and points it at a mutated C function,
proof/saw/ keeps the function and mutates the spec as X_mut_spec. Both are credited to X_spec.

Statements are joined to the terminating `;` before matching, because a verify call whose spec name
wraps onto a continuation line would otherwise be invisible, and an unseen guard is a check that
cannot fail.
"""
import re, sys
from collections import defaultdict

src = open(sys.argv[1]).read()
src = re.sub(r'//[^\n]*', '', src)            # line comments
src = re.sub(r'/\*.*?\*/', '', src, flags=re.S)  # block comments

obl, guard, seen = defaultdict(int), defaultdict(int), set()
for stmt in src.split(';'):
    if not re.search(r'\b(llvm|mir)_verify\b', stmt):
        continue
    names = re.findall(r"[A-Za-z_][A-Za-z0-9_']*_spec\b", stmt)
    if not names:
        continue
    spec = names[-1]
    if re.search(r'\bfails\s*\(', stmt):
        base = re.sub(r'_mut_spec$', '_spec', spec)
        guard[base] += 1
        seen.add(base)
    else:
        obl[spec] += 1
        seen.add(spec)

for s in sorted(seen):
    print(f"{s} {obl[s]} {guard[s]}")
