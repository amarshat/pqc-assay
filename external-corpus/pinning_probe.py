#!/usr/bin/env python3
"""Second probe: a precondition that is satisfiable but pins the input.

vacuity_probe.py injects `llvm_precond {{ False }}` and SAW rejects it every
time: the path condition is unsatisfiable and symbolic execution reports an
infeasible branch. That is the crude form of the failure. This probe injects
`llvm_precond {{ v == zero }}` on the spec's first fresh variable instead. The
path stays feasible, so the tool has nothing to complain about, and the proof
now covers one input where it used to cover all of them. Nothing in the script
distinguishes the two outcomes.

The mutation edits the spec definition, so it applies to every use of that spec,
and results are reported per spec rather than per call site.
"""
import re, shutil, subprocess, json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SAW_EXAMPLES = ROOT.parent / ".tools/saw-1.5.1/examples"
SCRATCH = Path("/private/tmp/claude-501/-Users-amar-akshat-code-assay-assay/f21db848-2a86-4b09-871e-a68da5b43872/scratchpad/pinning")
TIMEOUT = 300

# A spec's first symbolic input, whether bound directly or through one of the
# ptr_to_fresh-style helpers these examples define, which return (value, pointer).
FRESH = re.compile(r"^(\s*)(?:([A-Za-z_][A-Za-z0-9_']*)|\(\s*([A-Za-z_][A-Za-z0-9_']*)\s*,[^)]*\))"
                   r"\s*<-\s*(?:llvm_fresh_var|ptr_to_fresh)\s", re.M)
EXEC  = re.compile(r'^(\s*)llvm_execute_func\b', re.M)

def run(script):
    p = subprocess.run(['saw', script.name], cwd=script.parent,
                       capture_output=True, text=True, timeout=TIMEOUT)
    return p.returncode, p.stdout + p.stderr

def spec_blocks(text):
    """(name, start, end) for each `let NAME ... = do { ... };` block."""
    for m in re.finditer(r'^let\s+([A-Za-z_][A-Za-z0-9_\']*)[^=\n]*=\s*do\s*\{', text, re.M):
        i, d = text.index('{', m.end() - 1), 0
        j = i
        while j < len(text):
            if text[j] == '{': d += 1
            elif text[j] == '}':
                d -= 1
                if d == 0: break
            j += 1
        yield m.group(1), m.end(), j

def main():
    if SCRATCH.exists(): shutil.rmtree(SCRATCH)
    shutil.copytree(SAW_EXAMPLES, SCRATCH)
    results, dropped = [], []

    for rel in (ROOT / "corpus.txt").read_text().split():
        rel = Path(rel)
        script = SCRATCH / rel.relative_to("examples")
        original = script.read_text()
        rc, _ = run(script)
        if rc != 0:
            dropped.append((str(rel), "baseline does not pass in scratch")); continue
        blocks = list(spec_blocks(original))
        if not blocks:
            dropped.append((str(rel), "no `let NAME = do {...}` spec the parser could isolate")); continue

        used = set(re.findall(r'llvm_verify\s+\S+\s+"[^"]+"\s+\[[^\]]*\]\s+(?:true|false)\s+\(?\s*([A-Za-z_][A-Za-z0-9_\']*)', original))
        for name, a, b in blocks:
            if name not in used:
                dropped.append((f"{rel}::{name}", "spec is not a verification target here")); continue
            body = original[a:b]
            fv, ex = FRESH.search(body), EXEC.search(body)
            if not fv or not ex or fv.end() > ex.start():
                dropped.append((f"{rel}::{name}", "no symbolic input bound before llvm_execute_func")); continue
            var = fv.group(2) or fv.group(3)
            inject = f"{ex.group(1)}llvm_precond {{{{ {var} == zero }}}};\n"
            nb = body[:ex.start()] + inject + body[ex.start():]
            mutant = original[:a] + nb + original[b:]
            assert mutant != original and inject.strip() in mutant
            script.write_text(mutant)
            try: mrc, mout = run(script)
            except subprocess.TimeoutExpired: mrc, mout = 124, "timeout"
            finally: script.write_text(original)
            silent = (mrc == 0)

            # Liveness control. A spec site that the run never reaches would also
            # look silent, so inject an unsatisfiable precondition at the same
            # place: SAW reports an infeasible branch on any site that is live.
            # A site that stays quiet for `False` proves nothing when pinned.
            ctrl = body[:ex.start()] + f"{ex.group(1)}llvm_precond {{{{ False }}}};\n" + body[ex.start():]
            script.write_text(original[:a] + ctrl + original[b:])
            try: crc, cout = run(script)
            except subprocess.TimeoutExpired: crc, cout = 124, "timeout"
            finally: script.write_text(original)
            live = (crc != 0)

            results.append({"script": str(rel), "spec": name, "var": var, "silent": silent,
                            "live": live,
                            "tail": "" if silent else mout.strip().splitlines()[-1][:70]})
            if not live:
                print(f"  NOT LIVE {rel}::{name} -- unsatisfiable precondition also passed")
            print(f"{'SILENT ' if silent else 'signal '} {rel}::{name}  (pinned {var})"
                  + ("" if silent else f"   <- {results[-1]['tail']}"))

    (ROOT / "pinning_results.json").write_text(json.dumps({"results": results, "dropped": dropped}, indent=2) + "\n")
    live = [r for r in results if r["live"]]
    s = sum(1 for r in live if r["silent"])
    print(f"\n{len(live)} of {len(results)} spec sites are live "
          f"(an unsatisfiable precondition there is rejected)")
    print(f"{s} of {len(live)} pinned specs still reported success, with no signal")
    for d in dropped: print(f"  dropped: {d[0]}: {d[1]}")

main()
