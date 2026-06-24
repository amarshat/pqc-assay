# IACR ePrint submission fields

Copy-paste these into https://eprint.iacr.org/submit . The abstract here is plaintext
(ePrint does not take LaTeX). Upload `paper/pqc-assay-paper.pdf` (compile the zip on Overleaf
first). Fields marked (you) need a decision from you.

---

## Title
Mechanically Checking the ML-DSA Reference Forward NTT Against FIPS 204

## Authors
One author:
- Name: Amar Akshat
- Affiliation: Independent Researcher
- Email: amar.akshat@gmail.com
- ORCID: (you, optional)

## Corresponding / contact email
amar.akshat@gmail.com

## Category
Implementation
(alternative if the form pushes back: Public-key cryptography)

## Keywords
ML-DSA, FIPS 204, formal verification, refinement proof, SAW, Cryptol, Isabelle/HOL, number-theoretic transform, Montgomery reduction, post-quantum cryptography

## License (you)
Recommended: Creative Commons Attribution 4.0 (CC BY 4.0). It is the usual ePrint choice and lets
others cite and reuse with attribution. Pick another CC option only if you have a reason.

## Abstract (plaintext)
We give a machine-checked proof that the forward number-theoretic transform (NTT) in the PQClean /
pq-crystals ML-DSA reference C computes the FIPS 204 negacyclic transform, modulo q. The proof is one
connected chain. SAW proves the C equal to a Cryptol model under a -fwrapv build; cryptol-to-isabelle
lifts that model into Isabelle/HOL; and an Isabelle theorem, ntt_bridge, shows the lifted model at each
output position k equals the FIPS 204 negacyclic DFT coefficient at the bit-reversed index brv_8(k), mod
q. The one non-mechanized link is that the -fwrapv execution coincides with the ordinary one (no
signed-overflow undefined behavior) on the input domain; we support it with a separate machine-checked
coefficient-bound proof and state it as an argued composition. We also verify the reduce.c arithmetic
layer (montgomery_reduce, reduce32, caddq, freeze) from C to spec. Two choices keep the NTT result
honest: the theorem is about the same model SAW checks the C against (the montgomery-domain model),
joined to the FIPS transform by an explicit eight-layer bridge rather than a hand-written restatement;
and a claim table separates what is machine-checked from what is argued or assumed. A proof-engineering
note records the restructuring the development relied on: a direct bit-vector equivalence for wide-domain
modular reduction did not discharge in our setup, while the same relation in unbounded-integer arithmetic
did, and the matching total-invariant induction is what makes the NTT overflow bound tractable. We
disclose two off-by-one defects in the reference's documented contracts. The development reproduces from a
single command (make verify: SAW plus the full Isabelle chain, including the NTT bridge) and runs green in
CI; it uses no vendor verification artifacts.

## Publication status (you)
Preprint; not submitted to or published in a peer-reviewed venue at the time of posting. (Adjust if you
have submitted somewhere; ePrint asks whether it is published/submitted elsewhere.)

## DOI of published version
None.

## Funding
None.

## Artifact / data availability (put in the submission notes or leave for the PDF)
Source and proofs: https://github.com/amarshat/pqc-assay (release v2.0).
Archived artifact (Zenodo): re-archive v2.0 before submission and put the DOI here.

---

## PDF to upload
paper/pqc-assay-paper.pdf  (compile paper/pqc-assay-paper.zip on Overleaf; confirm Table 1 on p.3 and
the formula on p.5 fit the margin after the last fixes).

## Pre-submission checklist
- [ ] Compile the zip on Overleaf; verify no overflow on p.3 (Table 1) and p.5 (the ntt_bridge formula).
- [ ] Hard-check reference [35] (IACR ePrint 2026/1032) on its landing page: title, author order,
      ePrint number, year. (Automated fetch was blocked during verification.)
- [ ] Re-archive the v2.0 release on Zenodo and paste the DOI into the artifact note above.
- [ ] Pick the license (CC BY 4.0 recommended).
