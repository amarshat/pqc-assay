# The same checks, on proofs we did not write

Every measurement elsewhere in this repository is on our own artifact: our C, our Cryptol, our
properties, our mutation list. That is one data point, and it is the fair criticism of the method
paper. This directory runs two of the paper's checks against a corpus nobody here wrote: the 19
worked LLVM proofs that ship inside SAW 1.5.1, written by SAW's own authors.

Nothing here reports a defect in those proofs. They are correct as written. The question is
different: if one of them were silently weakened, would anything notice?

## The two probes

`vacuity_probe.py` rewrites one `llvm_verify` call at a time so the spec it uses becomes
`(do { llvm_precond {{ False }}; S; })`. The precondition cannot be satisfied, so the obligation is
empty. Only the one call site changes, leaving overrides and guards elsewhere in the script intact.

`pinning_probe.py` injects `llvm_precond {{ v == zero }}` on the spec's first symbolic input
instead, just before `llvm_execute_func`. The path condition stays satisfiable, so the tool has
nothing to object to, and the proof now covers a single input where it covered all of them.

The second probe is the one that matches how this fails in practice. The precondition that defeated
us was satisfiable too.

## Results

Unsatisfiable precondition, 54 call sites across 18 scripts: **rejected at all 54**. SAW stops with
`Symbolic execution failed. Infeasible branch`. The crude form of the failure is caught by the tool,
without any help from the proof author. We had assumed otherwise before running it.

Satisfiable precondition that pins the input, 27 live spec sites across 15 scripts:

|                            | signal | silent |
| -------------------------- | -----: | -----: |
| consumed as an override    |      5 |      1 |
| terminal, not consumed     |      0 |     21 |

**22 of 27 reported success with no signal.** More to the point, not one of the five signals came
from the proof of the weakened spec itself. All five came from a *different* proof downstream that
consumed the result as an override and could no longer discharge the precondition at the call site.
A spec whose result is the deliverable, which is what a verification effort usually ships, got
nothing.

Being consumed is not reliable either. `partial-spec.saw` pins `counter == zero` and stays silent,
because `use_inc` calls `inc` on a struct initialised to `{ .counter = 0 }`. The override still
applies. Downstream use only catches a weakening the caller happens to exercise.

## The liveness control

A site the run never reaches would look silent too, and would be indistinguishable from a real
result. So every site is also probed with `llvm_precond {{ False }}` at the same place, and counted
only if that is rejected. One site failed the control and is excluded: `set_bad_spec` appears only
inside `fails (llvm_verify ...)`, so emptying it makes the inner verification fail, makes the guard
succeed, and makes the script pass. Silence there means nothing. That is 27 live sites out of 28.

## What this does and does not support

It is evidence that the pinning failure is not specific to our artifact, and that the tool gives no
signal for it. It is not evidence about production proofs: these are worked examples shipped for
teaching, chosen here because they are third-party, complete and runnable, not because they stand in
for what a verification team ships. Running the same probes against `aws-lc-verification` would
answer that and has not been done.

The corpus is also small, and the scripts that do not run under this toolchain were dropped rather
than fixed: 10 of the 29 scripts containing `llvm_verify` need bitcode or Cryptol that the release
tarball does not carry. `corpus.txt` lists the 19 that run. Specs dropped by the parser are recorded
with a reason in `pinning_results.json` rather than omitted silently.

## Reproducing

```
make external-corpus
```

Both probes work on a scratch copy of the SAW example tree. Neither writes to `.tools/`.
