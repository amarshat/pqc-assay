# Submitting `MLDSA_Reduce` to the AFP

Everything mechanical is done and verified locally. What follows is the submission itself.

## Where to submit

There is one archive. `isa-afp.org` shows it built against the current Isabelle release and
`devel.isa-afp.org` shows it against Isabelle-devel; both follow from one submission. Submit through
the form linked from <https://www.isa-afp.org/submission/>, or by mail to `afp-submit@in.tum.de` with
the entry attached.

## What to send

- The directory `afp/MLDSA_Reduce/` as a tarball: two theory files, `ROOT`, and
  `document/root.tex` + `document/root.bib`.
- The metadata in `afp/MLDSA_Reduce.toml`, which follows the format the AFP uses in
  `metadata/entries/`. The editors add the author key and email to `metadata/authors.toml`; the
  `akshat_email` reference in `[notify]` is the placeholder they resolve.

Author: Amar Akshat, amar.akshat@gmail.com. Licence: BSD 3-clause, chosen so anyone can reuse the
entry, including in commercial work, with attribution and nothing else.

## The build, as verified on 2026-08-23

```
Isabelle2025-2, AFP 2026-06-05, Apple M2 Max
isabelle build -o document=pdf -d afp/MLDSA_Reduce -d <afp>/thys -c MLDSA_Reduce
  -> exit 0, theories 6 s, document 2 s
```

| requirement | status |
|---|---|
| builds on the current release | verified |
| no `sorry`, no `back` | verified, zero occurrences |
| no `sledgehammer`, no `smt_oracle` | verified, zero occurrences |
| `nitpick`/`quickcheck` with `expect` | not applicable, none used |
| depends only on the distribution and AFP | verified, `Word_Lib` only |
| produces a PDF document | verified |

`txfonts` is required, because `isabelle.sty` declares its blackboard math group as `U/txmia`
regardless of whether an entry uses blackboard symbols. On a BasicTeX machine install it without root:

```
tlmgr init-usertree
tlmgr --usermode -repository https://mirror.ctan.org/systems/texlive/tlnet install txfonts
```

## What a referee should know, and what we should say up front

- The entry proves four contracts (Montgomery reduction, `caddq`, `reduce32`, `freeze`) plus the
  integer core they share. It concerns the reduction layer only; nothing here is about the NTT.
- The definitions mirror the reference implementation so a reader can compare them by eye. The entry
  makes **no** claim that a compiled binary computes them. That link is SAW's job in the wider project
  and is not vouched for here.
- Two specifications deliberately contradict the bounds in the reference implementation's comments,
  which are off by one at an endpoint. The abstract says so, and the entry's build is a witness:
  substituting the documented `reduce32` window makes it fail.
- Whether the definitions are FIPS 204 is a question for a reader, not for Isabelle. See
  `docs/FIPS204-correspondence.md` in the wider project.

## Open decision

Whether to include an AI-assistance note. There is precedent: a 2026 entry states that an initial
version of its theories was machine-generated and then checked and refactored by its authors. The
same is true here, and the honest framing is that the proofs were developed with AI assistance and
that the entry stands on the build, not on how it was written.
