#!/usr/bin/env python3
"""Emit the size figures the paper's Table 1 reports, as LaTeX rows.

The paper claims every figure is produced by a named target. This is that target for Table 1. It also
fixes a counting bug: the previous hand-count dropped only lines whose FIRST character opened a
comment, so every continuation line of a block comment was counted as code. The ProVerif row was 2.1x
too large as a result.

Usage: scripts/paper-figures.py [--check]
"""
import glob
import re
import sys

GROUPS = [
    ("Q-SEAL \\tool{Cryptol} models", ["qseal/model/*.cry"]),
    ("Q-SEAL C references (including injected mutants)", ["qseal/ref/*.c"]),
    ("Q-SEAL \\tool{SAW} scripts", ["qseal/proof/*.saw"]),
    ("Q-SEAL \\tool{ProVerif} models", ["qseal/proof/proverif/*.pv"]),
    ("FIPS 204 hint anchor (model, C, proof)",
     ["cve-anchor/model/*.cry", "cve-anchor/ref/*.c", "cve-anchor/proof/*.saw"]),
    ("GSMA SGP.29 anchor (model, C, proof)",
     ["esim-eid/model/*.cry", "esim-eid/ref/*.c", "esim-eid/proof/*.saw"]),
    ("gates, runners and experiment harnesses",
     ["scripts/claim-lint.sh", "qseal/verify_*.sh", "qseal/mutation/mutate.py",
      "esim-eid/spec_mutation.py", "cve-anchor/fidelity/*.py", "cve-anchor/fidelity/*.sh",
      "qseal/proof/proverif/gen_variants.py", "esim-eid/verify.sh"]),
]

BLOCK = {".cry": None, ".c": ("/*", "*/"), ".saw": None, ".pv": ("(*", "*)"),
         ".sh": None, ".py": None}
LINE = {".cry": "//", ".c": "//", ".saw": "//", ".pv": None, ".sh": "#", ".py": "#"}


def count(path):
    """Non-comment, non-blank lines, stripping block comments across line boundaries."""
    ext = "." + path.rsplit(".", 1)[-1]
    block, line_marker = BLOCK.get(ext), LINE.get(ext)
    n, in_block = 0, False
    for raw in open(path, errors="ignore"):
        s = raw.strip()
        if in_block:
            if block and block[1] in s:
                in_block = False
                s = s.split(block[1], 1)[1].strip()
            else:
                continue
        if block and block[0] in s:
            before = s.split(block[0], 1)[0].strip()
            if block[1] not in s.split(block[0], 1)[1]:
                in_block = True
            s = before
        if line_marker and s.startswith(line_marker):
            continue
        if s:
            n += 1
    return n


def totals():
    return [(name, sum(count(f) for pat in pats for f in sorted(glob.glob(pat))))
            for name, pats in GROUPS]


if __name__ == "__main__":
    rows = totals()
    if "--check" in sys.argv:
        tex = open("paper/paper-methods.tex").read()
        bad = 0
        # the prose repeats two of these numbers; an earlier version of this check looked only at the
        # table rows and sat green while the cost section contradicted the table it cites
        arte = sum(n for name, n in rows if "gates" not in name)
        gates = [n for name, n in rows if "gates" in name][0]
        for want, label in ((arte, "artifact lines"), (gates, "gate lines")):
            if str(want) not in tex:
                print(f"STALE PROSE: {label} = {want} appears nowhere in the paper")
                bad = 1
        for m2 in re.finditer(r"(\d{3,4}) lines of gates", tex):
            if int(m2.group(1)) != gates:
                print(f"STALE PROSE: paper says {m2.group(1)} lines of gates, measured {gates}")
                bad = 1
        for m2 in re.finditer(r"against\s+(\d{3,4})\s*\n?lines of\s*\n?models", tex):
            if int(m2.group(1)) != arte:
                print(f"STALE PROSE: paper says {m2.group(1)} lines of models, measured {arte}")
                bad = 1
        for name, n in rows:
            key = re.escape(name.split("(")[0].strip())
            m = re.search(key + r"[^\\\\]*&\s*(\d+)", tex)
            if m and int(m.group(1)) != n:
                print(f"STALE: {name}: paper says {m.group(1)}, measured {n}")
                bad = 1
        print("paper-figures --check:", "STALE" if bad else "table 1 matches the tree")
        sys.exit(bad)
    for name, n in rows:
        print(f"{name} & {n} \\\\")
    print(f"% models+references+proofs = "
          f"{sum(n for name, n in rows if 'gates' not in name)}, "
          f"gates = {[n for name, n in rows if 'gates' in name][0]}")
