#!/usr/bin/env python3
"""Static survey: do third-party SAW developments carry any evidence their obligations can fail?

This is deliberately NOT the weakening probe in ../vacuity_probe.py and ../pinning_probe.py. Those
run the proofs. Running someone else's SAW development means matching their pinned SAW version and
building their C, which for a production repository is hours and a container. This asks a cheaper
question that needs no build:

    for every proof obligation, is there a paired guard showing the obligation can fail at all?

A missing guard does not make a proof vacuous. It means the development contains no witness that
its obligations are falsifiable, so a reader cannot tell from the artifact whether they are. That
is exactly the position we were in before adding ours.

Usage:  survey.py <name> <path-to-checkout>
"""
import subprocess, sys, pathlib, re

HERE = pathlib.Path(__file__).resolve().parents[2]
PAIRS = HERE / "scripts" / "saw_mutant_pairs.py"

def main():
    name, root = sys.argv[1], pathlib.Path(sys.argv[2])
    saws = sorted(root.rglob("*.saw"))
    # Count EVERY verify-like combinator, not just llvm_verify. An earlier version of this script
    # counted only llvm_verify and then reported "169/169 coverage", silently excluding about fifty
    # llvm_verify_x86 / crucible_llvm_verify / fixpoint calls. A survey that hides what it did not
    # look at is the failure this directory exists to measure.
    combinators = {}
    for f in saws:
        try: txt = f.read_text(errors="ignore")
        except OSError: continue
        txt = re.sub(r'//[^\n]*', '', txt)          # drop line comments
        # SAW's verify combinators only. A bare `*_verify*` match also picks up C function and
        # spec names (pkey_rsa_verify, ecdsa_do_verify_no_self_test_spec), which are not calls.
        for m in re.findall(r'\b(?:crucible_llvm|llvm|mir|jvm)_verify[a-z0-9_]*\b', txt):
            combinators[m] = combinators.get(m, 0) + 1
    raw_verify = sum(combinators.values())

    obl = grd = isolable = 0
    for f in saws:
        out = subprocess.run([sys.executable, str(PAIRS), str(f)],
                             capture_output=True, text=True).stdout.strip()
        if not out: continue
        isolable += 1
        for line in out.splitlines():
            _, o, g = line.rsplit(" ", 2)
            obl += int(o); grd += int(g)

    other = {k: sum(1 for f in saws if k in f.read_text(errors="ignore").lower())
             for k in ("fails", "mutant", "sanity")}

    print(f"corpus:                         {name}")
    print(f"  .saw files:                   {len(saws)}")
    print(f"  verify calls, all combinators: {raw_verify}")
    for k, v in sorted(combinators.items(), key=lambda kv: -kv[1]):
        print(f"      {k:<38} {v}")
    print(f"  files with an isolable spec:  {isolable}")
    print(f"  obligations paired by parser: {obl}")
    print(f"  paired mutant guards:         {grd}")
    print(f"  files mentioning fails:       {other['fails']}")
    print()
    pct = (100.0 * obl / raw_verify) if raw_verify else 0.0
    print(f"  parser isolates {obl} of {raw_verify} verify calls ({pct:.0f}%). The remainder use")
    print(f"  combinators or call forms this parser does not handle, and are counted neither as")
    print(f"  guarded nor as unguarded. The guard count above is over the isolated subset only.")

main()
