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

## Anonymity (TCHES submissions are anonymous)
Correction to an earlier note: TCHES submission is anonymous. The iacrtrans class makes this the
default: the `submission` option implies `anonymous` (iacrtrans.cls line 123; comment "[submission]
Anonymous submission"), so the compiled submission already prints "Anonymous Submission" and hides the
author block. (Both the TCHES editorial-policy and CHES call pages blocked automated fetch from here, so
confirm on the live call, but the IACR class default plus CHES double-blind practice are clear.)
- The `\author`/`\institute` block stays in the source; the class hides it in submission mode and shows
  it for camera-ready, so nothing to strip there.
- Body text that names the author is guarded by `\ifsubmissionanon` (set true at the top of
  `paper-tches.tex`): the reproducibility paragraph shows an "anonymized supplementary material" line
  instead of the GitHub/Zenodo links, and the saw-script discussion citation drops the author name.
- Camera-ready: set `\submissionanonfalse` (and switch the class option to `notanonymous`, or just drop
  `submission`) to restore author, repo URL, Zenodo DOI, and the discussion author names.

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

## Build status (compiled here with tectonic)
`paper-tches.tex` compiles clean to PDF with tectonic 0.16.9 (no errors, no overfull boxes). The
following were needed and are already applied:
- `iacrtrans.cls` v0.94 is vendored in `paper/` (from github.com/Cryptosaurus/iacrtrans). Tectonic's
  bundle does not ship it; Overleaf's "IACR Transactions" template does. Either keep the vendored cls or
  use that template.
- `\usepackage[htt]{hyphenat}` lets long `\texttt` tokens (cryptol-to-isabelle, montgomery\_reduce)
  break in the narrower iacrtrans column; without it they overflow the margin.
- `\keywords{...}` is declared in the preamble (before `\maketitle`); iacrtrans ignores it after the
  abstract (it then prints "No keywords given").
- The status table uses `tabularx` at `\textwidth`, so it auto-fits the iacrtrans text block.
- Manual `thebibliography` (35 entries) compiles fine under iacrtrans; no BibTeX conversion needed.
- The TikZ pipeline figure fits.

To compile locally: `brew install tectonic` then `tectonic -X compile paper/paper-tches.tex` (first run
downloads the package bundle). PDFs are gitignored.

## Pre-submission checklist
- [ ] Confirm the exact next deadline (~15 Jul 2026) and that the OJS portal is open.
- [ ] Confirm TCHES anonymity on the live call (we kept it anonymous; both policy pages blocked fetch).
- [ ] Opt into artifact evaluation; confirm its process/deadline.
- [ ] Hard-check ref [35] (IACR ePrint 2026/1032) on its landing page.
- [ ] Re-archive v2.0 on Zenodo (for camera-ready: set `\submissionanonfalse` and add the DOI).
