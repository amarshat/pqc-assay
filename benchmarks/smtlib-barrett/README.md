# Wide-domain Barrett reduction: a QF_BV tractability-boundary benchmark family

A parametric family of `QF_BV` benchmarks from a standardized, deployed cryptographic primitive: the
Barrett reduction in ML-DSA (FIPS 204). The identity is

```
rem = x - ((x * M) >> 46) * Q        Q = 8380417,  M = floor(2^46 / Q) = 8396807
```

over 128-bit bit-vectors. Each `barrett_bound_2pK.smt2` asserts `NOT (0 <= rem < 2*Q)` under the
precondition `x < 2^K`; an `unsat` answer means the Barrett bound `0 <= rem < 2*Q` holds over that input
domain (from which one conditional subtraction yields `x mod Q`). The formula is small (`M`, `Q` are
constants), but the SAT instance grows with the number of live input bits, so the family sweeps `K` and
exposes a sharp tractability cliff.

## The cliff (single thread, Apple M4, 16 GB, 300 s cap unless noted)

| benchmark | `x <` | z3 | cvc5 / yices / abc | bitwuzla 0.9.1 |
|---|---|---|---|---|
| `barrett_bound_2p28` | 2^28 | 4.1 s | fast | fast |
| `barrett_bound_2p32` | 2^32 | 27.9 s | | |
| `barrett_bound_2p34` | 2^34 | 183.6 s | | |
| `barrett_bound_2p36` | 2^36 | > 300 s | | |
| `barrett_bound_2p44` | 2^44 | > 300 s | > 300 s | |
| `barrett_bound_2p46` | 2^46 | > 300 s | > 300 s (none complete) | **unsat, 551 s** |

Eager bit-blasting back-ends (z3, cvc5, yices, and abc on the AIG) stall between 2^34 and 2^36 and do not
complete at 2^46; bitwuzla's CEGAR multiplier abstraction proves the full 2^46 instance `unsat`. The same
identity in unbounded-integer arithmetic (`NIA`) discharges in 0.04 s, so the wall is the eager bit-vector
encoding of `(x*M) >> 46`, not the relation. In the source project this goal blocks an end-to-end SAW
`mir_verify` of the deployed Rust `barrett_reduce` until the solver is switched to bitwuzla (which then
closes it in 1402 s over the full function).

## Non-vacuity

`barrett_nonvacuity_qplus1_2p46.smt2` mutates `Q` to `Q+1` (8380418); the bound is then violated and the
instance is `sat` (witness `x = 16760835`), returned instantly. This confirms the `unsat` results are
meaningful, not a modeling artifact.

## Provenance and license

Generated from the escape-2 study in <https://github.com/amarshat/pqc-assay> (archived at
<https://doi.org/10.5281/zenodo.21178811>). Reproducible harness and the SAW/Isabelle proofs that use the
same identity are in that repository. Licensed CC-BY 4.0 (`:license` in each file).

## Submitting to SMT-LIB / SMT-COMP

Channel: a pull request to <https://github.com/SMT-LIB/benchmark-submission> (fork, add files, open a
PR). That is the single submission channel; SMT-LIB and SMT-COMP both draw from it. The GitLab/Zenodo
SMT-LIB repos are the distribution of accepted benchmarks, not the submission point.

At submission, place these under `non-incremental/QF_BV/<YYYYMMDD>-mldsa-barrett-<submitter>/` and run the
repo's `quick-check.sh` plus the Dolmen type-checker (`dolmen -i smt2 --check-headers=true
--header-lang-version=2.6`) before opening the PR. The headers here already match the required block
(`:smt-lib-version 2.6`, `set-logic`, `:source`, `:license` CC-BY-4.0, `:category`, `:status`, one
`check-sat`, `exit`).

Timing: the 2026 release deadline (June 25, 2026) has passed. The next window is the 2027 release,
expected ~June 2027 (date not yet published). SMT Workshop 2027 (co-located with CAV/IJCAR) is the venue
for an accompanying extended abstract or presentation-only paper; SMT 2026's deadlines have also passed.
So this family is packaged and parked for the 2027 cycle.

Category note: files are tagged `:category "crafted"` (hand-authored SMT2). A companion `"industrial"`
instance, the exact goal SAW emits for the deployed `barrett_reduce` (dumped via
`offline_w4_unint_bitwuzla`), can be added before submission if a real-workload instance is wanted
alongside the clean parametric family.

## Status verification

`:status` in each file is tool-checked: `unsat` for the bound instances (z3 for small `K`, bitwuzla for
`K = 46`), `sat` for the mutant. Reproduce, e.g.:

```
bitwuzla barrett_bound_2p46.smt2                 # unsat (~9 min)
z3 barrett_bound_2p28.smt2                       # unsat (fast)
bitwuzla barrett_nonvacuity_qplus1_2p46.smt2     # sat (instant)
```
