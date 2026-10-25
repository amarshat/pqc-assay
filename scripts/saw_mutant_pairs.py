#!/usr/bin/env python3
"""Emit `spec obligations mutants` for one SAW script.

Pairs each llvm_verify/mir_verify obligation with the `fails (...)` guard aimed at the same spec.
Three conventions exist in this tree: a script may keep the spec and point it at a mutated C
function, keep the function and mutate the spec as X_mut_spec (both credited to X_spec), or build
the spec from a function with a size argument, `(spec 32 (\a b -> ...))`, in which case the key is
the function name with its size ("spec(32)", "spec_top"). Without the third form the AVX2 ladder
and multi-way obligations were invisible to the lint (found by review, 2026-10-25).

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
    if names:
        spec = names[-1]
    else:
        m = re.search(r"\b(?:true|false)\s*\(\s*([A-Za-z_][A-Za-z0-9_']*)(?:\s+(\d+))?", stmt)
        if not m:
            continue
        spec = m.group(1) + ('(' + m.group(2) + ')' if m.group(2) else '')
    if re.search(r'\bfails\s*\(', stmt):
        base = re.sub(r'_mut_spec$', '_spec', spec)
        guard[base] += 1
        seen.add(base)
    else:
        obl[spec] += 1
        seen.add(spec)

for s in sorted(seen):
    print(f"{s} {obl[s]} {guard[s]}")
