# AFP submission: `MLDSA_Reduce`

An Isabelle/HOL development of the modular-reduction layer of ML-DSA (FIPS 204), built as a standalone
entry for the Archive of Formal Proofs.

**Status: submitted 2026-08-23, rejected 2026-09-12.** The editor's reason was scope, not soundness: the
four routines are a small subset of FIPS 204, and the AFP already has queued submissions covering
FIPS 202/203/204 and covering the modular algorithms generically rather than at the concrete
q = 8380417, which the editors prefer. Nothing was raised about the proofs, the style, the provenance or
the build, and the theories did build clean on AFP infrastructure (their log, on a Linux/polyml platform
this project never targeted). The development stays here because the results are still results and the
paper cites them; it is no longer a submission in progress.

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

## If this is ever revived

The rejection was about scope and duplication, so the routes that address it are contributing these
word-level proofs under a fuller FIPS 204 entry, or waiting to see what the queued entries cover and
whether an implementation-level layer on top of them is still wanted. Making this entry generic over
q would collide with the second queued submission, and extending it to more of FIPS 204 would collide
with the first.

What is still true and still useful, independent of the AFP: the four contracts are machine-checked
against fixed-width models of PQClean's routines, and two of them deliberately correct bounds the
reference implementation documents, with witnesses (`montgomery_upper_endpoint_returns_q`,
`reduce32_lower_endpoint_attained`). Both corrections are reported upstream in
pq-crystals/dilithium#114.
