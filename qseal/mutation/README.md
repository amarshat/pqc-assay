# Mutation adequacy for the Q-SEAL C references

Each per-property SAW proof carries one hand-injected mutant (checked with `fails`), which shows the
proof is sensitive to that one clause. That is sensitivity, not adequacy. `mutate.py` measures adequacy:
it applies a defined operator set to each C reference systematically, one mutation per occurrence,
reruns the matching SAW proof against the mutated code, and reports how many mutants the proofs kill.

Operators (the class CVE-2026-24850 lived in, plus logical):

    relational   >= <-> >    <= <-> <    > <-> >=    < <-> <=    == <-> !=    != <-> ==
    logical      && <-> ||    || <-> &&

A mutant is **killed** if the SAW proof no longer discharges (the C stops matching the Cryptol model),
**survived** if the proof still passes, or **stillborn** if it does not compile (excluded from the
ratio). The injected-bug demo functions (`*_noconsume`, `*_downgrade`, `*_nosuitecheck`, `*_nocomplete`)
are skipped: they are test fixtures, not the verified artifact. Comments and preprocessor lines are
skipped. The run works on a copy of `qseal/`, so tracked files are never modified.

## Run

    make qseal-mutants                     # all reference files (~1 min)
    python3 qseal/mutation/mutate.py nonce.c   # one file

## Result (2026-07-06)

41 valid relational/logical mutants across the six C references, **39 killed, 2 survived** (95%). Both
survivors are the same shape and are semantically equivalent mutants, not adequacy gaps:

- `nonce.c:23` and `evidence.c:20`, a loop upper bound `i < CAP` changed to `i <= CAP`. The extra
  iteration is a no-op: a downstream guard (`if (i == count)` / `if (frags[i].seq == j)`) is false for
  the out-of-range index, so nothing is written and no out-of-bounds access happens. No behavior
  changes, so no proof or test could kill it.

So the proofs kill every non-equivalent relational/logical mutant in this operator set. A survivor that
is *not* an equivalent mutant would be an adequacy gap in the corresponding SAW spec, to fix by
tightening the spec; classification of survivors is by hand (the tool cannot decide equivalence).

## Scope

This covers relational and logical operator mutations. It does not cover arithmetic-operator, constant,
or statement-deletion mutants (the hand-injected demo mutants are the statement-deletion cases). It is a
report, not a CI gate, because equivalent mutants legitimately survive and need human classification.
