#!/usr/bin/env python3
"""Cross-tabulate the pinning results against how each spec's result is used.

The question is what, if anything, notices when a specification is silently
weakened. Two candidate mechanisms exist in this corpus: a `fails` guard that
asserts the proof should not go through, and a downstream proof that consumes
the result as an override and has to re-establish the precondition at the call
site. This works out which of the two, if either, applied to each spec.
"""
import json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
EX = ROOT.parent / ".tools/saw-1.5.1/examples"
res = [r for r in json.load(open(ROOT / "pinning_results.json"))["results"] if r["live"]]

VERIFY = re.compile(r'(?:([A-Za-z_][A-Za-z0-9_\']*)\s*<-\s*)?llvm_verify\s+\S+\s+"[^"]+"\s+'
                    r'\[([^\]]*)\]\s+(?:true|false)\s+\(?\s*([A-Za-z_][A-Za-z0-9_\']*)')

rows = []
for r in res:
    text = (EX.parent / r["script"]).read_text()
    bound, used_as_override, guarded = set(), False, False
    for m in VERIFY.finditer(text):
        if m.group(3) == r["spec"]:
            if m.group(1): bound.add(m.group(1))
            line = text[text.rfind('\n', 0, m.start()) + 1:m.start()]
            if 'fails' in line: guarded = True
    for m in VERIFY.finditer(text):
        if m.group(3) != r["spec"] and bound & set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", m.group(2))):
            used_as_override = True
    rows.append({**r, "consumed": used_as_override, "guarded": guarded})

def n(**kw): return [x for x in rows if all(x[k] == v for k, v in kw.items())]
print(f"corpus: {len(rows)} specs across {len(set(r['script'] for r in rows))} third-party scripts\n")
print(f"{'':28}{'signal':>8}{'silent':>8}")
for label, sel in [("consumed as an override", dict(consumed=True)),
                   ("terminal (not consumed)", dict(consumed=False))]:
    print(f"{label:28}{len(n(**sel, silent=False)):>8}{len(n(**sel, silent=True)):>8}")
print(f"\nsignals that came from the proof of the spec itself: "
      f"{len([x for x in rows if not x['silent'] and not x['consumed']])}")
print(f"specs carrying a `fails` guard: {len(n(guarded=True))}")
print("\nconsumed as an override yet still silent:")
for x in n(consumed=True, silent=True): print(f"   {x['script']}::{x['spec']}")
json.dump(rows, open(ROOT / "analysis.json", "w"), indent=2)
