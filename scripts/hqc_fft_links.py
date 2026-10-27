#!/usr/bin/env python3
"""Check that the additive-FFT entry-point proofs assume only what their make target proves.

fft_<p>.saw assumes each routine with llvm_unsafe_assume_spec m "F" (E). The check passes only if a
script of the same target (run earlier, in its own SAW process) contains llvm_verify m "F" [...] false (E)
with the same E, character for character after collapsing white space. Both sides build E from the one
definition in proof/hqc-fft/specs.saw, and no script may redefine a name that specs.saw defines.
decode_64 at hqc-3/5 is proved in parts (r3_dec.saw, r5_dec.saw), so the assumed whole-output spec
dec_spec N 0 {{ N : [32] }} (\\x -> {{ decode<p> x }}) is accepted only if: the parts file is the
generator's output (scripts/hqc_fft_dec.py --check, which also checks that the runs cover each output
byte once), every part is verified in it, every part uses dec_pre N 0 of the assumed spec, and
proof/hqc-fft/lemmas.icry proves dbytes<p>_cover. The step from the parts to the whole (each part
constrains disjoint bytes of the output of the same call from the same precondition) is the one
argument made outside a tool; A-HQC-FFT item 8 states it.
Usage: hqc_fft_links.py   (all three targets; exit 1 on any unlinked assumption)."""
import re, sys, pathlib, subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / 'proof/hqc-fft'
TARGETS = {  # must match the Makefile's hqc-fft, hqc-fft-3, hqc-fft-5 lists
    'fft_1': ['ref_1', 'ref_2', 'ref_3', 'ref_3d', 'ref_4', 'ref_4b'],
    'fft_3': ['ref_1', 'r3_net', 'r3_enc', 'r3_dec', 'r3_bc'],
    'fft_5': ['ref_1', 'r5_net', 'r5_enc', 'r5_dec', 'r5_bc'],
}

def norm(s):
    return ' '.join(s.split())

def balanced(s, i):
    """s[i] == '('; return the text up to and including the matching ')'."""
    depth = 0
    for j in range(i, len(s)):
        depth += {'(': 1, ')': -1}.get(s[j], 0)
        if depth == 0:
            return s[i:j + 1]
    raise ValueError('unbalanced')

def text(name, seen=None):
    """Script text with include "x.saw" expanded (other than specs.saw)."""
    seen = seen or set()
    s = (D / f'{name}.saw').read_text()
    def inc(m):
        n = m.group(1)[:-4]
        if n == 'specs' or n in seen:
            return ''
        seen.add(n)
        return text(n, seen)
    return re.sub(r'include "([\w.]+)";', inc, s)

def calls(s, kind):
    pat = {'verify': r'llvm_verify m "(\w+)" (?:\[[^\]]*\]|\w+) false ', 'assume': r'llvm_unsafe_assume_spec m "(\w+)" '}[kind]
    out = []
    for m in re.finditer(pat, s):
        # skip mutants: a verify wrapped in fails (...)
        if kind == 'verify' and s[max(0, m.start() - 7):m.start()] == 'fails (':
            continue
        j = m.end()
        e = balanced(s, j) if s[j] == '(' else re.match(r'\w+', s[j:]).group(0)
        out.append((m.group(1), norm(e)))
    return out

def main():
    specs = (D / 'specs.saw').read_text()
    shared = set(re.findall(r'^let (\w+)', specs, re.M))
    lemmas = (D / 'lemmas.icry').read_text()
    bad = []
    if subprocess.run([sys.executable, str(ROOT / 'scripts/hqc_fft_dec.py'), '--check']).returncode:
        bad.append('decode parts are stale')
    for top, provers in TARGETS.items():
        for f in [top] + provers:
            raw = (D / f'{f}.saw').read_text()
            if 'include "specs.saw";' not in raw and 'include "ref_1.saw";' not in raw:
                bad.append(f'{f}.saw does not include specs.saw')
            for n in re.findall(r'^let (\w+)', raw, re.M):
                if n in shared:
                    bad.append(f'{f}.saw redefines {n} from specs.saw')
            if f != top and 'llvm_unsafe_assume_spec' in raw:
                bad.append(f'{f}.saw assumes a spec; only {top}.saw may')
        proved = set()
        parts = {}
        for f in provers:
            s = text(f)
            proved.update(calls(s, 'verify'))
            for name, body in re.findall(r'let (dec\d_part\d+) = do \{\n(.*?)\n\};', s, re.S):
                parts[name] = body
        n_ok = 0
        for fn, e in calls(text(top), 'assume'):
            if (fn, e) in proved:
                n_ok += 1
                continue
            m = re.fullmatch(r'\(dec_spec (\d+) 0 \{\{ \1 : \[32\] \}\} \(\\x -> \{\{ decode(\d) x \}\}\)\)', e)
            if fn == 'decode_64' and m:
                n, p = int(m.group(1)), m.group(2)
                want = [f'dec{p}_part{k}' for k in range(n // 256)]
                ok = all(('decode_64', w) in proved for w in want)
                ok = ok and all(parts.get(w, '').startswith(f'  (rp, x) <- dec_pre {n} 0 {{{{ {n} : [32] }}}};') for w in want)
                ok = ok and re.search(rf'^:prove dbytes{p}_cover$', lemmas, re.M) is not None
                if ok:
                    n_ok += 1
                    continue
            bad.append(f'{top}.saw assumes {fn} {e} but no script of its target verifies it')
        print(f'{top}: {n_ok} assumed specs, each verified by a script of the same target')
    for b in bad:
        print('!!', b)
    sys.exit(1 if bad else 0)

if __name__ == '__main__':
    main()
