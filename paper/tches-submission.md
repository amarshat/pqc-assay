# IACR TCHES submission notes

Target: IACR Transactions on Cryptographic Hardware and Embedded Systems (TCHES). Source file for this
venue is `paper/paper-tches.tex` (iacrtrans class). The `paper/paper.tex` (article) version stays for
ePrint.

## Deadlines
TCHES has four fixed quarterly submission dates: 15 Jul, 15 Oct, 15 Jan, 15 Apr; notification about two
months later; accepted papers are presented at the matching CHES event. The 2026-volume windows have all
closed (last was 15 Apr 2026), so the next is the 2027-volume Issue 1, deadline about 15 July 2026.
Confirm the exact date on https://tches.iacr.org . The OJS portal is closed between cycles and opens
near the deadline.

## Format (mandatory)
- iacrtrans class is required. Submission build is already set in `paper-tches.tex`:
  `\documentclass[journal=tches,submission,review]{iacrtrans}` (the `review` option adds line numbers).
  For camera-ready switch to `\documentclass[journal=tches]{iacrtrans}`.
- Get the class from https://github.com/Cryptosaurus/iacrtrans , or on Overleaf start from the
  "IACR Transactions" template and paste in `paper-tches.tex` (the class ships with the template).

## Anonymity (verify before submitting)
TCHES is non-anonymous by default (author names shown), so `paper-tches.tex` keeps the author block. If
the call for the target issue says otherwise, add the `anonymous` option to `\documentclass` and strip
identifying text (the GitHub URL in the title footnote / artifact mentions).

## Fields to enter in OJS
Same content as `paper/eprint-submission.md`:
- Title: Mechanically Checking the ML-DSA Reference Forward NTT Against FIPS 204
- Author: Amar Akshat, Independent Researcher, amar.akshat@gmail.com
- Abstract: the plaintext block in `eprint-submission.md`
- Keywords: ML-DSA, FIPS 204, formal verification, refinement proof, SAW, Cryptol, Isabelle/HOL,
  number-theoretic transform, Montgomery reduction, post-quantum cryptography

## Artifact evaluation
TCHES/CHES runs an artifact-evaluation track, and this paper has a strong artifact (single-command
`make verify`, CI, pinned toolchain, Zenodo archive). Opt in. Confirm the current AE process and its
deadline on the TCHES site (it usually runs for accepted/conditionally-accepted papers, separate from
the main deadline).

## iacrtrans compile risks (not compiled here; check on first Overleaf build)
- We do NOT re-load inputenc/fontenc/microtype/geometry/hyperref; iacrtrans owns them. If a package
  clash appears, the cause is most likely a re-load, not a missing one.
- Bibliography is a manual `thebibliography`. iacrtrans expects BibTeX. Manual should compile, but if the
  class objects, convert the 35 entries to a `.bib` and use `\bibliographystyle` per the iacrtrans README.
- The status table uses `tabularx` at `\textwidth`, so it auto-fits the (narrower) iacrtrans text block;
  no manual width tuning needed. The two small timing tables are plain `tabular` (2 columns, fit).
- Check the TikZ pipeline figure fits the iacrtrans text width; shrink the `node distance` if it spills.
- `\keywords{... \and ...}` and `\institute{... \email{...}}` are iacrtrans macros; confirm they render.

## Pre-submission checklist
- [ ] Compile `paper-tches.tex` on Overleaf (iacrtrans). Resolve any class clash (see risks above).
- [ ] Confirm the exact next deadline and that the OJS portal is open.
- [ ] Verify the anonymity policy for the target issue; flip `anonymous` if required.
- [ ] Opt into artifact evaluation; confirm its process/deadline.
- [ ] Hard-check ref [35] (IACR ePrint 2026/1032) on its landing page.
- [ ] Re-archive v2.0 on Zenodo; put the DOI in the paper's reproducibility section.
