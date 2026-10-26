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
  target/hqc-fft model/cryptol/hqc-fft proof/hqc-fft scripts/hqc_native \
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
i = s.index('## A-HQC-FFT'); j = s.find('\n## ', i + 1); hqc = hqc.rstrip('\n') + '\n\n' + (s[i:] if j < 0 else s[i:j])
k = s.index('- **OF-5'); l = s.find('\n- **OF-', k + 1); of5 = s[k:] if l < 0 else s[k:l]
open(f'{out}/ASSUMPTIONS-HQC.md', 'w').write('# Assumptions and open findings (HQC)\n\nThe A-HQC and A-HQC-FFT sections of the repository\'s docs/ASSUMPTIONS.md, and its HQC entry under "Open findings".\n\n' + hqc.rstrip('\n') + '\n\n## Open findings\n\n' + of5.rstrip('\n') + '\n')
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
| `make hqc` | reference `vect_mul` = Karatsuba model (SAW), GF(2^8), Reed-Solomon, Reed-Muller and `code_encode` against their code properties; every spec's mutant rejected | 28 to 34 min |
| `make hqc-avx` | AVX2 `vect_mul` = Toom/Karatsuba model, three sets (hqc-1/3 on the repaired source), poison lanes checked never read and quantified over, mutants rejected | 68 min on a loaded machine (hqc-1 alone 267 s idle) |
| `make hqc-isabelle` | the lifted models compute (a*b) mod (x^n - 1); `HQC_Gate` fails the build on an oracle, a skipped proof, or an axiom beyond Main that is not a definition or generated type axiom | about 30 s |
| `make lift-check` | every committed lifted theory equals `cryptol-to-isabelle` of its Cryptol source | about 1 min |
| `scripts/check_target_identity.sh` | the vendored bytes match the pinned hashes | seconds |
| `make hqc-avx-asis` | the AVX2 proofs on the source as shipped (hqc-1/3 with one vector of symbolic slack on `W0`/`W2`); the gated `make hqc-avx` proves the repaired hqc-1/3 source | same as `make hqc-avx` |
| `make hqc-solvers`, `make hqc-rme-scaling` | the solver tables of the paper (both depend on `make hqc`, which runs first if its outputs are absent) | up to 50 min, 11 min |
| `make hqc-fft`, `make hqc-fft-3`, `make hqc-fft-5` | additive-FFT reference C (`target/hqc-fft`) = Cryptol model (`model/cryptol/hqc-fft`), every routine and the entry points, at the three lengths; mutants rejected | 761 s and 5561 s (Apple M4 Pro, 24 GB); 14585 s with 25.7 GB peak (M2 Max) |
| `scripts/hqc_native/run.sh` | evidence, not a proof: repaired AVX2 `vect_mul` against the reference natively at `-O0`, `-O3 -flto` and with ASan (x86-64, or Rosetta 2 on macOS 15) | a few minutes |
| `make hqc-fft-lemmas` | the model lemmas those proofs use (Cryptol, abc) | 1152 s (M4 Pro) |
| `make hqc-c-mutants` | seven one-line source mutants of copies of the C against the unchanged hqc-1 scripts, nine rows with the two concrete-input rows (the Mutants paragraphs); depends on `make hqc` | about 90 min after `make hqc` |

`make` with no target runs `hqc`, `hqc-avx` and `hqc-isabelle`.

## Logs behind the tables

`logs/` holds the runs the paper's numbers come from, so a table can be checked without a rerun:
`make_hqc_v3.out` (`make hqc`, 34 min 24 s, exit 0), `make_avx.out` (the earlier zero-lane, slack
configuration of `make hqc-avx`, 263/1167/2062 s, exit 0), `make_avx_fixed.out` (`make hqc-avx` as
shipped here: repaired hqc-1/3 source, symbolic lanes, exit 0 in 4103 s on a busy machine),
`cmut.table` and `cmut_concrete.out` (`make hqc-c-mutants`, all rows), `solvers_false.out` and
`solvers_cmut.out` (the two false obligations of the solver table), all on the Apple M2 Max.

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
keep = [b.replace('(run 40120098008)', '(a CI run)') for b in keep]
for b in keep:
    assert not re.search(r'\$\((TARGET_C|BITCODE|SAW_SCRIPT|ISA_SESSION)\)', b), b[:80]
tail = ('## Every committed lifted theory equals cryptol-to-isabelle of its Cryptol source.\nlift-check:\n'
        '\t./scripts/lift_check_all.sh\n\nclean:\n\trm -rf build\n')
phony = '.PHONY: hqc hqc-avx hqc-avx-asis hqc-isabelle hqc-solvers hqc-rme-scaling hqc-c-mutants hqc-fft hqc-fft-3 hqc-fft-5 hqc-fft-lemmas hqc-fft-bitcode lift-check clean'
header = re.sub(r'^\.PHONY:.*$', phony, header, flags=re.M)
header = header.replace('# Assay — one-command reproduction.\n# Each target fails loudly; `make verify` is the whole pipeline.', '# One-command reproduction of the HQC proofs. Each target fails loudly.')
header = re.sub(r'^(TARGET_C|BITCODE|SAW_SCRIPT|ISA_SESSION)\s*:=.*\n', '', header, flags=re.M)
header = header.replace('all: verify', 'all: hqc hqc-avx hqc-isabelle')
header = header.replace(' — ', ': ')
assert 'all: hqc hqc-avx hqc-isabelle' in header and 'ISA_SESSION' not in header
open(f'{out}/Makefile', 'w').write(header.rstrip('\n') + '\n\n' + '\n\n'.join(b.strip('\n') for b in keep) + '\n\n' + tail)
PY

# Other scripts: drop the sentences about other targets of the full repository.
python3 - "$OUT" <<'PYS'
import re, sys
out = sys.argv[1]
def sub(path, pairs):
    p = f'{out}/{path}'; s = open(p).read()
    for old, new in pairs:
        assert old in s, (path, old[:50]); s = s.replace(old, new)
    open(p, 'w').write(s)
sub('scripts/setup.sh', [
    ('for the Q-SEAL reachability property (section 16 property 5)', 'for a protocol leg of the full repository, not used here'),
    ('(implementations/rustcrypto-ml-dsa/proof/ntt) needs it; the Q-SEAL legs do not', 'the solver study (one table row) needs it'),
    ('(Q-SEAL reachability leg; optional, needs OCaml)', '(optional, needs OCaml; not used by the HQC targets)'),
    ('See qseal/proof/proverif/README.md.', 'Not needed for the HQC targets.'),
    ('(Q-SEAL reachability leg)', '(not used by the HQC targets)'),
    (' — ', ': '),
])
sub('scripts/check_target_identity.sh', [
    ("""# The verified C lives in target/pqclean/, vendored verbatim from PQClean's ml-dsa-44/clean at the
# commit below. PQClean's `clean` implementation tracks the pq-crystals/dilithium reference (PQClean
# only adds the PQCLEAN_MLDSA44_CLEAN_ symbol prefix); the pq-crystals commit it imports is recorded
# below so a reviewer can diff target/pqclean against that reference directly.
""", """# The verified C lives in target/hqc/, vendored verbatim from the HQC v5.0.0 release at the
# commit recorded in target/README.md.
"""),
    ('echo ">> verifying vendored target bytes (PQClean $PQCLEAN_COMMIT, tracks pq-crystals $PQCRYSTALS_COMMIT; HQC $HQC_COMMIT; HQC-FFT $FFT_COMMIT)"',
     'echo ">> verifying vendored target bytes (HQC $HQC_COMMIT; additive-FFT artifact $FFT_COMMIT)"'),
])
p2 = f'{out}/scripts/check_target_identity.sh'; s2 = open(p2).read()
s2 = re.sub(r'^(PQCLEAN_COMMIT|PQCRYSTALS_COMMIT)=.*\n', '', s2, flags=re.M)
open(p2, 'w').write(s2)
sub('scripts/lift_check_all.sh', [
    ("""# scripts/lift_check.sh enforced that for MLDSA_NTT and lift_check_barrett.sh for the Barrett lift,
# which left two lifts ungated: the ML-KEM model and the FIPS-204 reference transcription. Both were
# in sync when this script was written, so the gap was latent rather than live, but "currently in
# sync" is not a check.
""", """# Every lifted theory in the manifest below is regenerated and compared byte for byte.
"""),
])
PYS
mkdir -p "$OUT/logs"
for f in make_hqc_v3.out make_avx.out make_avx_fixed.out cmut.table cmut_concrete.out solvers_false.out solvers_cmut.out; do
  sed -e "s#/Users/[^ ]*/assay/assay#\$ROOT#g" "build/hqc/$f" > "$OUT/logs/$f"
done
for f in "$OUT"/scripts/*.sh; do bash -n "$f"; done
if grep -rIn -E 'Assay|Q-SEAL|qseal|rustcrypto|mldsa|MLDSA|ml-dsa|pq-crystals|—|40120098008' "$OUT" | grep -q .; then
  grep -rIn -E 'Assay|Q-SEAL|qseal|rustcrypto|mldsa|MLDSA|ml-dsa|pq-crystals|—|40120098008' "$OUT" | head; echo "!! other-target breadcrumbs remain (above)" >&2; exit 1
fi
# Scrub: nothing author-identifying may remain ("hadamard" matches 'amar' and is excluded).
if grep -rIl -i -E 'akshat|amarshat|mpsc\.io|zenodo' "$OUT" | grep -v '^$'; then
  echo "!! identifying strings remain (above)" >&2; exit 1
fi
if grep -rIn -i -E '\bamar\b' "$OUT" | grep -v -i hadamard | grep -q .; then
  echo "!! identifying strings remain" >&2; exit 1
fi
( cd dist && zip -qr hqc-artifact.zip hqc-artifact )
echo ">> dist/hqc-artifact.zip: $(find "$OUT" -type f | wc -l | tr -d ' ') files, $(du -sh dist/hqc-artifact.zip | cut -f1)"
