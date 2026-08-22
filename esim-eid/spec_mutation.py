#!/usr/bin/env python3
"""Specification-mutation experiment: which checks catch a rule we got wrong in BOTH places?

Code mutation, the usual kind, changes the implementation and leaves the specification alone, so an
equality proof necessarily fails and the kill rate says almost nothing. The failure that matters is the
one where the specification and the implementation are wrong together, because somebody misread the
standard. Nothing internal can catch that: the proof still passes, since the two sides still agree.

This applies paired mutations to the GSMA SGP.29 model and the C reference at once, then runs both
checks and reports which one notices:

  - SAW C == Cryptol             expected to still PASS, because both sides moved together
  - clause-directed vectors      expected to FAIL, because they are tied to the standard's text

Runs on a copy; tracked files are untouched.
"""
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SRC = REPO / "esim-eid"

# Each entry drops or weakens one clause in BOTH the model and the C reference.
MUTATIONS = [
    {
        "name": "drop AE.R02 (the reserved 89 prefix)",
        "cry": ("notE118Reserved ds = ~ ((ds @ 0 == 8) && (ds @ 1 == 9))",
                "notE118Reserved ds = True"),
        "c":   ("if (d[0] == 8 && d[1] == 9) ok = 0;             /* AE.R02: 89 is reserved for ITU-T E.118 */",
                "/* clause dropped by the spec-mutation experiment */"),
    },
    {
        "name": "drop the decimal-digit range check",
        "cry": ("digitsOnly ds = and [ d <= 9 | d <- ds ]",
                "digitsOnly ds = True"),
        "c":   ("        if (d[i] > 9) ok = 0;                       /* decimal digits only */",
                "        (void)d[i];"),
    },
    {
        "name": "accept remainder 0 as well as 1 (misreading section 10)",
        "cry": ("checkDigitsValidFold ds = foldRem ds == 1",
                "checkDigitsValidFold ds = (foldRem ds == 1) || (foldRem ds == 0)"),
        "c":   ("    if (acc != 1u) ok = 0;",
                "    if (acc != 1u && acc != 0u) ok = 0;"),
    },
]


def run(cmd, cwd, timeout=900):
    return subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True, timeout=timeout)


def apply_pair(work, mut):
    cry = work / "model" / "EID.cry"
    c = work / "ref" / "eid.c"
    for path, (old, new) in ((cry, mut["cry"]), (c, mut["c"])):
        text = path.read_text()
        if old not in text:
            raise SystemExit(f"mutation anchor not found in {path.name}: {old!r}")
        path.write_text(text.replace(old, new, 1))


def main():
    tools = REPO / ".tools" / "bin"
    results = []
    for mut in MUTATIONS:
        with tempfile.TemporaryDirectory(prefix="eid_specmut_") as td:
            work = Path(td) / "esim-eid"
            shutil.copytree(SRC, work, ignore=shutil.ignore_patterns("build"))
            (work / "build").mkdir(exist_ok=True)
            apply_pair(work, mut)

            env = f'export PATH="{tools}:$PATH"; '
            clang = (f'{env}clang -c -emit-llvm -O0 -g -I {work}/ref {work}/ref/eid.c '
                     f'-o {work}/build/eid.bc')
            r = run(clang, work)
            if r.returncode != 0:
                results.append((mut["name"], "STILLBORN (did not compile)", ""))
                continue

            saw = run(f'{env}saw eid.saw', work / "proof")
            saw_pass = "VERIFIED:" in saw.stdout

            vectors = run(
                f'{env}cryptol -b /dev/stdin <<\'EOF\'\n'
                f':l EID.cry\n:set prover=z3\n'
                f':prove kav_good\n:prove kav_badcheck\n:prove kav_e118\n:prove kav_nondigit\n'
                f':prove kav_nondigit_isolating\n:prove kav_remzero\nEOF',
                work / "model")
            n_qed = vectors.stdout.count("Q.E.D.")
            vec_pass = n_qed == 6

            results.append((mut["name"],
                            "PASSES (blind to it)" if saw_pass else "fails",
                            f"CATCHES it ({6 - n_qed}/6 vectors fail)" if not vec_pass else "blind to it"))

    print("\nPaired specification+implementation mutations, GSMA SGP.29 anchor")
    print("=" * 78)
    print(f"{'mutation':<46} {'C == spec proof':<22} vectors")
    print("-" * 78)
    for name, saw, vec in results:
        print(f"{name:<46} {saw:<22} {vec}")
    print("-" * 78)
    blind = sum(1 for _, saw, _ in results if saw.startswith("PASSES"))
    caught = sum(1 for _, _, vec in results if vec.startswith("CATCHES"))
    print(f"{blind}/{len(results)} invisible to the equality proof; {caught}/{len(results)} caught by "
          f"vectors tied to the standard's text")
    return 0 if (blind == len(results) and caught == len(results)) else 1


if __name__ == "__main__":
    sys.exit(main())
