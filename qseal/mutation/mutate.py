#!/usr/bin/env python3
"""Mutation-adequacy harness for the Q-SEAL C references.

The per-property SAW proofs each carry one hand-injected mutant, which shows the proof is sensitive to
that one clause. This measures adequacy instead of sensitivity: it applies a defined operator set to the
C reference systematically (one mutation per occurrence), reruns the matching SAW proof against the
mutated code, and reports how many mutants the proof kills.

Operators (the class CVE-2026-24850 lived in, plus logical):
  relational  >= <-> >   <= <-> <   > <-> >=   < <-> <=   == <-> !=   != <-> ==
  logical     && <-> ||   || <-> &&

A mutant is KILLED if the SAW proof no longer discharges (the C stops matching the Cryptol model),
SURVIVED if the proof still passes (the mutant is semantically equivalent, or the spec does not
constrain that byte -- an adequacy gap to inspect), or STILLBORN if it does not compile (not a valid
behavioral mutant; excluded from the ratio). Runs on a copy; tracked files are never modified.

Usage:  python3 qseal/mutation/mutate.py            # all reference files
        python3 qseal/mutation/mutate.py nonce.c    # one file
"""

import os
import re
import shutil
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
QSEAL = os.path.join(REPO, "qseal")

# reference file -> the verify script that exercises it
TARGETS = {
    "tbs_v1.c": "verify_ref.sh",
    "tbs_v2.c": "verify_ref.sh",
    "assertion.c": "verify_assertion.sh",
    "hybrid.c": "verify_hybrid.sh",
    "nonce.c": "verify_nonce.sh",
    "nonce_exp.c": "verify_nonce.sh",
    "validate.c": "verify_validate.sh",
    "evidence.c": "verify_evidence.sh",
}

# longest-match first so >= is matched before >
SWAPS = [
    (">=", ">"), ("<=", "<"), ("==", "!="), ("!=", "=="),
    ("&&", "||"), ("||", "&&"),
    (">", ">="), ("<", "<="),
]
OPS = [s[0] for s in SWAPS]
SWAP_MAP = {}
for a, b in SWAPS:
    SWAP_MAP.setdefault(a, b)

# Functions that exist only as injected-bug demos for the SAW `fails` guards. They are NOT the verified
# artifact, so mutating them is meaningless for adequacy; skip them. The list below is the legacy set;
# anything named in a `fails (llvm_verify m "...")` line is added automatically, so a new hand-injected
# mutant cannot silently enter the adequacy denominator.
EXCLUDE_FUNC = ["_noconsume", "_downgrade", "_nosuitecheck", "_nocomplete", "_allowobserved"]


def _mutant_names_from_proofs():
    """Every function a SAW script asserts must FAIL is a deliberate mutant, not part of the artifact."""
    names = set()
    proof_dir = os.path.join(QSEAL, "proof")
    pat = re.compile(r'fails\s*\(\s*llvm_verify\s+\w+\s+"([^"]+)"')
    for fn in sorted(os.listdir(proof_dir)):
        if not fn.endswith(".saw"):
            continue
        with open(os.path.join(proof_dir, fn)) as fh:
            names.update(pat.findall(fh.read()))
    return sorted(names)


EXCLUDE_FUNC = sorted(set(EXCLUDE_FUNC) | set(_mutant_names_from_proofs()))
FUNC_RE = re.compile(r"^\s*(?:static\s+)?(?:int|void|unsigned|size_t)\s+(\w+)\s*\(")


def mask_comments(text):
    """Return text with // and /* */ comments blanked to spaces (positions and line count preserved),
    so operator scanning, brace counting, and function detection ignore comment contents."""
    out = list(text)
    i, n = 0, len(text)
    in_line, in_block = False, False
    while i < n:
        c = text[i]
        two = text[i:i + 2]
        if in_line:
            if c == "\n":
                in_line = False
            else:
                out[i] = " "
            i += 1
        elif in_block:
            if two == "*/":
                out[i] = out[i + 1] = " "
                in_block = False
                i += 2
            else:
                if c != "\n":
                    out[i] = " "
                i += 1
        elif two == "//":
            out[i] = out[i + 1] = " "
            in_line = True
            i += 2
        elif two == "/*":
            out[i] = out[i + 1] = " "
            in_block = True
            i += 2
        else:
            i += 1
    return "".join(out)


def gen_mutants(text):
    """Yield (line_no, col, op, replacement, mutated_text) for each relational/logical operator
    occurrence in code (not comments, not preprocessor lines, not the injected-bug demo functions)."""
    lines = text.split("\n")
    masked = mask_comments(text).split("\n")
    depth = 0
    skip_func = False
    for ln, mline in enumerate(masked):
        prev_depth = depth
        if depth == 0:
            m = FUNC_RE.match(mline)
            if m:
                skip_func = any(s in m.group(1) for s in EXCLUDE_FUNC)
        depth += mline.count("{") - mline.count("}")
        if prev_depth > 0 and depth <= 0:
            skip_func = False  # just closed a function, back at file scope
        if skip_func or mline.lstrip().startswith("#"):
            continue
        line = lines[ln]
        j = 0
        while j < len(mline):
            matched = None
            for op in OPS:
                if mline.startswith(op, j):
                    matched = op
                    break
            if matched is None:
                j += 1
                continue
            prev = mline[j - 1] if j > 0 else ""
            nxt = mline[j + len(matched)] if j + len(matched) < len(mline) else ""
            if matched in (">", "<") and (prev in ("-", "<", ">") or nxt in ("<", ">")):
                j += len(matched)
                continue
            rep = SWAP_MAP[matched]
            new_line = line[:j] + rep + line[j + len(matched):]
            mutated = "\n".join(lines[:ln] + [new_line] + lines[ln + 1:])
            yield (ln + 1, j + 1, matched, rep, mutated)
            j += len(matched)


def run(cmd, cwd, env):
    return subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=300)


def main():
    only = sys.argv[1] if len(sys.argv) > 1 else None
    files = [only] if only else list(TARGETS)
    for f in files:
        if f not in TARGETS:
            print(f"unknown reference file: {f} (known: {', '.join(TARGETS)})")
            return 2

    env = dict(os.environ)
    env["PATH"] = os.path.join(REPO, ".tools", "bin") + os.pathsep + env.get("PATH", "")

    tmp = tempfile.mkdtemp(prefix="qseal_mut_")
    dst = os.path.join(tmp, "qseal")
    shutil.copytree(
        QSEAL, dst,
        ignore=shutil.ignore_patterns("build", "target", "*.bc", ".git"),
    )

    totals = {"killed": 0, "survived": 0, "stillborn": 0}
    survivors = []
    print(f"Mutation-adequacy run (copy at {dst})\n")
    for f in files:
        ref_path = os.path.join(dst, "ref", f)
        with open(ref_path) as fh:
            pristine = fh.read()
        script = os.path.join(dst, TARGETS[f])
        k = s = b = 0
        muts = list(gen_mutants(pristine))
        print(f"{f}: {len(muts)} mutants  ({TARGETS[f]})")
        for (ln, col, op, rep, mutated) in muts:
            with open(ref_path, "w") as fh:
                fh.write(mutated)
            # compile check first: non-compiling => stillborn, not a behavioral mutant
            syn = run(["clang", "-fsyntax-only", "-I", os.path.join(dst, "ref"), ref_path], dst, env)
            if syn.returncode != 0:
                b += 1
                tag = "stillborn"
            else:
                res = run(["bash", script], dst, env)
                if res.returncode == 0:
                    s += 1
                    tag = "SURVIVED"
                    survivors.append(f"{f}:{ln}:{col}  {op} -> {rep}")
                else:
                    k += 1
                    tag = "killed"
            with open(ref_path, "w") as fh:
                fh.write(pristine)  # restore for the next mutant
            if tag in ("SURVIVED", "stillborn"):
                print(f"    {f}:{ln}:{col}  {op} -> {rep}   [{tag}]")
        totals["killed"] += k
        totals["survived"] += s
        totals["stillborn"] += b
        valid = k + s
        ratio = f"{k}/{valid}" if valid else "0/0"
        print(f"  -> killed {k}, survived {s}, stillborn {b}   kill ratio {ratio}\n")

    shutil.rmtree(tmp, ignore_errors=True)

    kk, ss, bb = totals["killed"], totals["survived"], totals["stillborn"]
    valid = kk + ss
    print("=" * 60)
    print(f"TOTAL: killed {kk}, survived {ss}, stillborn {bb} (excluded)")
    print(f"KILL RATIO: {kk}/{valid} = {100.0 * kk / valid:.1f}%" if valid else "no valid mutants")
    if survivors:
        print("\nSURVIVORS (each is either a semantically equivalent mutant, or an adequacy gap to")
        print("inspect by hand; a loop-bound `< -> <=` guarded downstream is the usual equivalent case):")
        for x in survivors:
            print(f"  {x}")
    # This is a report, not a gate: equivalent mutants legitimately survive, so exit 0 and leave the
    # survivor classification to a human.
    return 0


if __name__ == "__main__":
    sys.exit(main())
