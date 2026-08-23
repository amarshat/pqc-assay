# AFP submission: `MLDSA_Reduce`

An Archive of Formal Proofs entry for the modular-reduction layer of ML-DSA (FIPS 204), built as a
standalone development so it can be refereed on its own terms.

There is one AFP, not two. `isa-afp.org` shows the archive built against the current Isabelle release
and `devel.isa-afp.org` shows the same archive built against Isabelle-devel; submission is a single
step, by mail to `afp-submit@in.tum.de` with the entry.

## Why this is a separate development from `spec/isabelle/`

The existing development proves the same results, but its session is declared as

    session Assay in "." = "Cryptol" +

and `Cryptol` ships inside the SAW tarball. AFP entries build on the Isabelle distribution and other
AFP entries only, so that dependency is disqualifying no matter how good the proofs are. This entry
therefore defines the reduction routines directly over machine words (`Word_Lib`, itself an AFP entry)
and carries the proofs across. The Cryptol lift stays where it belongs, on the SAW side of the pipeline,
and is not part of what an AFP referee is asked to maintain.

## What it contains

| theorem | statement |
|---|---|
| `montgomery_reduce_correct` | on the half-open domain, the result satisfies `2^32 * r ≡ a (mod q)` and `-q < r < q` |
| `caddq_correct` | adds `q` exactly when the argument is negative, preserving the residue |
| `reduce32_correct` | residue preserved, output in the true reachable window `[-6283009, 6283008]` |
| `freeze_correct` | composition lands in `[0, q)` |

Plus `mont_core`, the integer-level heart: if `T ≡ A · QINV (mod 2^32)` and `T` is in signed 32-bit
range, then `(A - T·q) / 2^32` is a correct Montgomery reduction of `A`.

## Checklist against AFP's stated requirements

| requirement | status |
|---|---|
| builds on the current release | **verified**: Isabelle2025-2 with AFP 2026-06-05, 6 s |
| no `sorry`, no `back` | **verified**: zero occurrences |
| no `sledgehammer`, no `smt_oracle` | **verified**: zero occurrences |
| `nitpick`/`quickcheck` need `expect` | not applicable: none used |
| depends only on the distribution and AFP | **verified**: `Word_Lib` only |
| produces a PDF document | **verified**: `isabelle build -o document=pdf` exits 0 and produces the entry PDF (2 s). Needs `txfonts`, which `isabelle.sty` requires unconditionally for its blackboard math group; on a BasicTeX machine install it without root via `tlmgr init-usertree && tlmgr --usermode -repository https://mirror.ctan.org/systems/texlive/tlnet install txfonts`. |

The proofs were checked negatively as well as positively. Adding a false conjunct to
`montgomery_reduce_correct` fails the build, and so does replacing the `reduce32` output window with the
bound the reference implementation's comment documents, which is the independent re-confirmation of
finding OF-2 in `docs/ASSUMPTIONS.md`.

## What it does not claim

- **No link to any C.** The definitions mirror the reference implementation so a reader can compare them
  by eye. Establishing that a compiled binary computes them is what the SAW leg of this project does,
  and none of that is inside this entry or vouched for by it.
- **The reduction layer only.** Nothing here concerns the NTT. See `docs/FIPS204-correspondence.md` for
  what the wider development does and does not connect to FIPS 204.
- **The definitions are ours.** Isabelle certifies that the theorems follow from them. Whether they are
  FIPS 204 is a question for a reader, which is the argument for the specification audit described in
  the correspondence document.

## Before submitting

1. Decide the author and licence fields (AFP takes BSD or LGPL) and write the abstract for the AFP
   metadata form. The abstract in `document/root.tex` is a starting point.
2. Decide whether to include an AI-assistance note, following the precedent of the 2026 entry that
   discloses machine-generated theories checked and refactored by its authors.
3. Note the release calendar: Isabelle2026 is expected in October 2026, and an accepted entry commits
   the author to keeping it building across releases.

Everything mechanical is done: theories and document both build clean against the current release, with
no prohibited commands and no dependency outside the distribution and `Word_Lib`.
