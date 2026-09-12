#!/usr/bin/env python3
"""Apply this project's non-vacuity check to SAW proofs we did not write.

For every llvm_verify call in the corpus, replace the spec argument S with
(do { llvm_precond {{ False }}; S; }) at that one call site and re-run the
script. The precondition is unsatisfiable, so the obligation is vacuous: a
verification that still reports success is one whose result would survive the
specification being emptied out.

Only the one call site is rewritten, so overrides and `fails` guards elsewhere
in the same script keep their original meaning.
"""
import re, shutil, subprocess, sys, json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SAW_EXAMPLES = ROOT.parent / ".tools/saw-1.5.1/examples"
SCRATCH = Path("/private/tmp/claude-501/-Users-amar-akshat-code-assay-assay/f21db848-2a86-4b09-871e-a68da5b43872/scratchpad/vacuity")
TIMEOUT = 300

VERIFY = re.compile(r'llvm_verify\s+\S+\s+"[^"]+"\s+\[[^\]]*\]\s+(?:true|false)\s+')

def read_arg(s, i):
    """Return (end_index) of one SAW argument starting at s[i]."""
    if s[i] == '(':
        d = 0
        while i < len(s):
            if s[i] == '(': d += 1
            elif s[i] == ')':
                d -= 1
                if d == 0: return i + 1
            i += 1
        return None
    if s.startswith('{{', i):
        j = s.find('}}', i)
        return j + 2 if j >= 0 else None
    m = re.compile(r'[A-Za-z_][A-Za-z0-9_\']*').match(s, i)
    if not m: return None
    if m.group(0) == 'do':                      # inline do-block spec
        j = s.find('{', m.end())
        if j < 0: return None
        d = 0
        while j < len(s):
            if s[j] == '{': d += 1
            elif s[j] == '}':
                d -= 1
                if d == 0: return j + 1
            j += 1
        return None
    return m.end()

def sites(text):
    """Yield (start_of_spec, end_of_spec) for each non-guarded llvm_verify."""
    for m in VERIFY.finditer(text):
        line_start = text.rfind('\n', 0, m.start()) + 1
        line = text[line_start:m.start()]
        if 'fails' in line or line.lstrip().startswith('//'):
            continue                              # guard, or commented out
        end = read_arg(text, m.end())
        if end is None:
            continue
        yield m.end(), end

def run(script: Path):
    p = subprocess.run(['saw', script.name], cwd=script.parent,
                       capture_output=True, text=True, timeout=TIMEOUT)
    return p.returncode, (p.stdout + p.stderr)

def main():
    if SCRATCH.exists(): shutil.rmtree(SCRATCH)
    shutil.copytree(SAW_EXAMPLES, SCRATCH)
    scripts = [Path(l.strip()) for l in (ROOT / "corpus.txt").read_text().split() if l.strip()]
    results, dropped = [], []

    for rel in scripts:
        script = SCRATCH / rel.relative_to("examples")
        original = script.read_text()
        rc, out = run(script)
        if rc != 0:
            dropped.append((str(rel), "baseline does not pass in scratch"))
            continue
        found = list(sites(original))
        if not found:
            dropped.append((str(rel), "no unguarded llvm_verify call the parser could isolate"))
            continue
        for n, (a, b) in enumerate(found):
            spec = original[a:b]
            mutant = original[:a] + "(do { llvm_precond {{ False }}; " + spec + "; })" + original[b:]
            assert mutant != original
            script.write_text(mutant)
            try:
                mrc, mout = run(script)
            except subprocess.TimeoutExpired:
                mrc, mout = 124, "timeout"
            finally:
                script.write_text(original)
            results.append({
                "script": str(rel), "site": n, "spec": spec.strip()[:60],
                "silent": mrc == 0,
                "why": "" if mrc == 0 else classify(mout),
            })
            print(f"{'SILENT ' if mrc==0 else 'signal '} {rel}:{n}  {spec.strip()[:44]}")

    (ROOT / "vacuity_results.json").write_text(json.dumps(
        {"results": results, "dropped": dropped}, indent=2) + "\n")
    silent = sum(1 for r in results if r["silent"])
    print(f"\n{silent} of {len(results)} vacuous specs verified with no signal")
    for d in dropped: print(f"  dropped: {d[0]}: {d[1]}")

def classify(out):
    if "timeout" in out: return "timeout"
    if "Proof failed" in out or "Unsat" not in out and "prove" in out.lower(): return "proof failed"
    if "override" in out.lower(): return "override could not be applied"
    if "fails" in out.lower(): return "guard inverted"
    return "error"

main()
