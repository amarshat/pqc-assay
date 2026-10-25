#!/usr/bin/env bash
# Build dist/hqc-artifact.zip: the HQC part of this repository, for double-blind review.
#
# Contents: the vendored HQC C (target/hqc), the Cryptol models (model/cryptol/hqc), the SAW scripts
# and their generator (proof/hqc), the Isabelle session (spec/isabelle/hqc), the Makefile, the setup
# and measurement scripts, HQC-only versions of the target-identity and lift checks (the full
# versions name other targets in this repository), the A-HQC section of docs/ASSUMPTIONS.md with the
# HQC open finding, and an anonymous README. Nothing else from the tree. The last step greps the
# result for author-identifying strings and fails if any remain.
set -euo pipefail
cd "$(dirname "$0")/.."
OUT=dist/hqc-artifact
rm -rf "$OUT" dist/hqc-artifact.zip; mkdir -p "$OUT"

git archive HEAD Makefile LICENSE model/cryptol/hqc proof/hqc spec/isabelle/hqc target/hqc target/README.md \
  scripts/setup.sh scripts/setup_isabelle_cryptol.sh scripts/hqc_avx_ir.py scripts/hqc_solver_study.sh \
  scripts/hqc_rme_scaling.sh scripts/hqc_c_mutants.sh scripts/saw_mutant_pairs.py scripts/check_target_identity.sh scripts/lift_check_all.sh \
  | tar -x -C "$OUT"

python3 - "$OUT" <<'PY'
import re, sys
out = sys.argv[1]
# HQC-only identity list and lift manifest: keep the scripts, drop the lines about other targets.
p = f'{out}/scripts/check_target_identity.sh'; s = open(p).read()
s = re.sub(r'EXPECTED="\n(.*?)\n"', lambda m: 'EXPECTED="\n' + '\n'.join(l for l in m.group(1).split('\n') if 'target/hqc' in l) + '\n"', s, flags=re.S)
s = s.replace('echo ">> to confirm against pq-crystals: diff target/pqclean against pq-crystals/dilithium@$PQCRYSTALS_COMMIT"\necho "   (ref/reduce.c, ref/ntt.c, ...), modulo the PQCLEAN_MLDSA44_CLEAN_ prefix."\n', '')
open(p, 'w').write(s)
p = f'{out}/scripts/lift_check_all.sh'; s = open(p).read()
s = re.sub(r'MANIFEST="\n(.*?)\n"', lambda m: 'MANIFEST="\n' + '\n'.join(l for l in m.group(1).split('\n') if 'spec/isabelle/hqc' in l) + '\n"', s, flags=re.S)
open(p, 'w').write(s)
# target/README.md: the HQC section only.
p = f'{out}/target/README.md'; s = open(p).read()
i = s.index('## HQC target'); j = s.find('\n## ', i + 1)
open(p, 'w').write('# Vendored target\n\n' + s[i:] if j < 0 else '# Vendored target\n\n' + s[i:j] + '\n')
# ASSUMPTIONS: the A-HQC section and the HQC open finding.
s = open('docs/ASSUMPTIONS.md').read()
i = s.index('## A-HQC'); j = s.find('\n## ', i + 1); hqc = s[i:] if j < 0 else s[i:j]
k = s.index('- **OF-5'); l = s.find('\n- **OF-', k + 1); of5 = s[k:] if l < 0 else s[k:l]
open(f'{out}/ASSUMPTIONS-HQC.md', 'w').write('# Assumptions and open findings (HQC)\n\nThe A-HQC section of the repository\'s docs/ASSUMPTIONS.md, and its HQC entry under "Open findings".\n\n' + hqc.rstrip('\n') + '\n\n## Open findings\n\n' + of5.rstrip('\n') + '\n')
PY

cat > "$OUT/README.md" <<'MD'
# Artifact: machine-checked multiplication and encoding in HQC v5.0.0

The HQC part of a larger verification repository. It contains the vendored HQC v5.0.0 C under proof
(`target/hqc`, pinned by SHA-256 in `scripts/check_target_identity.sh`), the Cryptol models
(`model/cryptol/hqc`), the SAW scripts and the generator that writes the per-parameter-set files
(`proof/hqc`), the Isabelle session (`spec/isabelle/hqc`, session `HQC`), and `ASSUMPTIONS-HQC.md`,
which lists every assumption and the normalizations applied to the AVX2 bitcode.

## Requirements

macOS on Apple Silicon (the pinned SAW, Cryptol, cryptol-to-isabelle and bitwuzla builds are arm64;
`scripts/setup.sh` also names the Linux x86_64 assets but that path is untested). Xcode command-line
tools (Apple clang 17). For the AVX2 proofs, Homebrew `llvm@22` (`clang` with `llvm-dis` and `llvm-as`
beside it). For the bitwuzla row of the solver study, Homebrew `gmp` and `mpfr`. Python 3.

    ./scripts/setup.sh                   # pinned SAW 1.5.1 bundle, Isabelle2025-2, bitwuzla 0.9.1
    ./scripts/setup_isabelle_cryptol.sh  # the Cryptol Isabelle session that lifted theories import (slow, once)

## What to run

| Command | What it checks | Time (Apple M2 Max) |
|---|---|---|
| `make hqc` | reference `vect_mul` = Karatsuba model (SAW), GF(2^8), Reed-Solomon, Reed-Muller and `code_encode` against their code properties; every spec's mutant rejected | about 25 min |
| `make hqc-avx` | AVX2 `vect_mul` = Toom/Karatsuba model, three sets, mutants rejected | 263 s + 1167 s + 2062 s (58 min) |
| `make hqc-isabelle` | the lifted models compute (a*b) mod (x^n - 1), oracle-free (`HQC_Gate`) | about 30 s |
| `make lift-check` | every committed lifted theory equals `cryptol-to-isabelle` of its Cryptol source | about 1 min |
| `scripts/check_target_identity.sh` | the vendored bytes match the pinned hashes | seconds |
| `make hqc-avx-poison` | the AVX2 proofs on bitcode with all-ones poison lanes | about 90 min |
| `make hqc-solvers`, `make hqc-rme-scaling` | the solver tables of the paper | up to 50 min, 11 min |
| `make hqc-c-mutants` | seven one-line source mutants of copies of the C against the unchanged hqc-1 scripts (the Mutants paragraphs) | about 75 min |

`python3 proof/hqc/gen_hqc.py --check` confirms the committed generated files are current.

## Map to the paper

Section 3 (model): `model/cryptol/hqc/{GF2X,KM<p>,Fold}.cry`. Section 4 (C equals the model):
`proof/hqc/karatsuba_<p>.saw`. Section 5 (the model multiplies): `spec/isabelle/hqc/{HQC_Poly,HQC_Seq,HQC_P<p>}.thy`.
Section 6 (AVX2): `target/hqc/avx2`, `scripts/hqc_avx_ir.py`, `model/cryptol/hqc/{AVXK,Toom,Toom5,AVX<p>}.cry`,
`proof/hqc/avx_<p>.saw`, `spec/isabelle/hqc/{AVX_Seq,AVX_Toom,AVX_Toom5,AVX_P<p>}.thy`. Section 7
(field and encoders): `proof/hqc/gf.saw`, `proof/hqc/code_<p>.saw`, `model/cryptol/hqc/{GF256,RS,RM}.cry`.
Section 8 (solvers): `scripts/hqc_solver_study.sh`, `scripts/hqc_rme_scaling.sh`; source-level mutants: `scripts/hqc_c_mutants.sh`. Findings:
`ASSUMPTIONS-HQC.md`, OF-5. Appendix: the theorem statements in the theories named above.
MD

# HQC-only Makefile: the variable header and the hqc* targets (the full Makefile names other targets).
python3 - "$OUT" <<'PY'
import re, sys
out = sys.argv[1]; s = open('Makefile').read()
header = s[:s.index('\n## ')]                      # variables up to the first target comment
blocks = re.split(r'\n(?=## )', s)
keep = [b for b in blocks if re.search(r'^hqc[-\w]*:', b, re.M)]
tail = ('## Every committed lifted theory equals cryptol-to-isabelle of its Cryptol source.\nlift-check:\n'
        '\t./scripts/lift_check_all.sh\n\nclean:\n\trm -rf build\n')
phony = '.PHONY: hqc hqc-avx hqc-avx-poison hqc-isabelle hqc-solvers hqc-rme-scaling hqc-c-mutants lift-check clean'
header = re.sub(r'^\.PHONY:.*$', phony, header, flags=re.M)
open(f'{out}/Makefile', 'w').write(header.rstrip('\n') + '\n\n' + '\n\n'.join(b.strip('\n') for b in keep) + '\n\n' + tail)
PY

# Scrub: nothing author-identifying may remain ("hadamard" matches 'amar' and is excluded).
if grep -rIl -i -E 'akshat|amarshat|mpsc\.io|zenodo' "$OUT" | grep -v '^$'; then
  echo "!! identifying strings remain (above)" >&2; exit 1
fi
if grep -rIn -i -E '\bamar\b' "$OUT" | grep -v -i hadamard | grep -q .; then
  echo "!! identifying strings remain" >&2; exit 1
fi
( cd dist && zip -qr hqc-artifact.zip hqc-artifact )
echo ">> dist/hqc-artifact.zip: $(find "$OUT" -type f | wc -l | tr -d ' ') files, $(du -sh dist/hqc-artifact.zip | cut -f1)"
