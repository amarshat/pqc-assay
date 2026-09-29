# The same question, asked of production proofs

`../vacuity_probe.py` and `../pinning_probe.py` run the weakening probes against SAW's own shipped
example proofs. The fair objection is that those are teaching examples. This directory asks a
cheaper question of a production development instead.

## What was measured, and what was not

**Not measured:** we did not run `aws-lc-verification`'s proofs, and we did not weaken any of its
specifications. Doing that means matching its pinned SAW (0.9.0.99 / 1.1.0.99, against our 1.5.1)
and building AWS-LC, which is a container and hours. Nothing here is a claim that any of its proofs
is vacuous.

**Measured**, statically, needing no build:

> For each proof obligation, does the development contain a paired guard demonstrating that the
> obligation can fail at all?

```
$ python3 survey.py "aws-lc-verification @ main" <checkout>
  .saw files:                    83
  verify calls, all combinators: 214
  files with an isolable spec:   19
  obligations paired by parser:  169
  paired mutant guards:          0
  files mentioning fails:        0
  parser isolates 169 of 214 verify calls (79%).
```

Zero. Across the whole repository there is no `fails`, no mutation harness, no negative test, and no
documented non-vacuity strategy. The only occurrences of "admit" and "negative" are prose in
`README.md` and `SPEC.md`.

## What that does and does not support

A missing guard does not make a proof vacuous, and we are not saying these proofs are wrong.
`aws-lc-verification` is careful, widely cited production work. What the absence means is narrower
and still worth stating: **the artifact contains no witness that its obligations are falsifiable**,
so a reader cannot tell from it whether any given specification is load-bearing. That is precisely
the position our own artifact was in until we added guards, and the position in which the weakening
probes found 22 of 27 sites silent in the teaching corpus.

The honest shape of the combined evidence is therefore:

- On proofs we could run (SAW's examples), weakening a specification produced no signal at 22 of 27
  live sites.
- On proofs we could not run (AWS's production development), there is no mechanism present that
  would have produced a signal either way.

The second is weaker than the first. It is also about production code, which the first is not.

## Calibration

The survey is only meaningful if it can tell the two cases apart. Against this repository's own
`proof/` tree it reports 15 paired guards against 21 isolated obligations; the unguarded remainder
are the two `nsw` scripts that carry a declared `NO-MUTANT-GUARD` exemption. Against
`aws-lc-verification` it reports 0 of 169.

## A note on the parser's coverage

79%, and the shortfall is reported rather than rounded away. `saw_mutant_pairs.py` isolates
`llvm_verify`; the corpus also uses `llvm_verify_x86`, `crucible_llvm_verify` and three fixpoint
variants. Those 45 calls are counted neither as guarded nor as unguarded.

An earlier version of this script counted only `llvm_verify` and then printed "169/169 coverage",
which silently excluded those 45. That is the same defect this directory exists to measure, in the
tool doing the measuring, and it lasted about ten minutes.
