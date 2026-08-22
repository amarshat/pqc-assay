# GSMA SGP.29 EID validation

Rules this project did not write, verified with the same machinery as everything else.

Every Q-SEAL property checks a rule from a specification this project authored, against a C reference
this project wrote to be verifiable. That is a fair objection to the whole exercise, and the answer is
to point the machinery at somebody else's rules. This directory does that with the GSMA eUICC
identifier, and `../cve-anchor/` does it with a FIPS 204 clause.

## The source

GSM Association Official Document **SGP.29, "EID Definition and Assignment Process", version 1.1**
(22 March 2024). Three clauses are mechanized, quoted in `model/EID.cry` next to their transcription:

- **EID.R01** (section 8): the EID is 32 digits. Discharged by the type, since the model works on a
  32-element array.
- **AE.R02** (section 9): EIDs must not start with `89`, which is reserved for the ITU-T E.118 scheme.
- **Section 10**: the check digits. Verification is "using the 32 digits as a decimal integer, compute
  the remainder of that number on division by 97 ... if the remainder is 1, the verification is
  successful".

## What is proved

`make eid-anchor`, about 45 seconds:

- `gsma_eid_valid` in `ref/eid.c` computes exactly `eidValid` in `model/EID.cry`, for every 32-byte
  input, memory-safe, with no assumed specifications (SAW).
- Three mutants fail that obligation: dropping AE.R02, dropping the digit-range check, and following
  the standard's wording literally in a 32-bit word.
- Five clause-directed vectors, one conformant EID and one near-miss per clause. The reserved-prefix
  vector has correct check digits, so only AE.R02 rejects it; that isolates the clause rather than
  relying on an aggregate kill rate.

## What the standard's wording costs

Section 10 says to treat the 32 digits as a decimal integer. That number needs about 107 bits, so no
implementation can do it in a machine word, and every real one folds the remainder through the digits
instead. Two things follow, and both are in the model.

**The bridge lemma.** Reducing early equals reducing at the end, one digit at a time, provided the
accumulator is already below 97 (`step_reduce_early`, with `fold_acc_bounded` establishing the
invariant). Both discharge in about 12 seconds.

**The side condition the standard does not state.** The same identity without an accumulator bound, at
the width that actually holds the standard's "decimal integer", is false: `a * 10` wraps.
`step_wide_is_false` is a satisfiability obligation whose witness is that failure. Carrying a standard's
unbounded arithmetic into fixed-width machine arithmetic acquires a precondition that appears nowhere in
the standard, and a transcription that omits it is wrong in a way no test vector in the document would
catch.

**What did not discharge.** The direct equivalence, "the fold equals the standard's single remainder
over the 32-digit value", does not complete. Measured on an Apple M2 Max with SAW 1.5.1 and z3:

| formulation | result |
|---|---|
| 128-bit bitvector value, one remainder at the end, versus the fold | no result within 10 minutes |
| the same over Cryptol `Integer` instead of a bitvector | no result within 10 minutes |
| the one-digit bridge lemma with the accumulator bound | Q.E.D., about 12 s |

So the composition from the bridge lemma to all 32 digits is an argument, not a mechanized proof. It is
the same wall the ML-DSA work in this repository hit on wide-domain Barrett reduction, reached here from
a completely different direction: a telecoms identifier scheme with no cryptography in it at all.

## The experiment that matters: mutating the specification and the code together

Code mutation, the usual kind, edits the implementation and leaves the specification alone. An equality
proof then necessarily fails, so a high kill rate measures nothing about whether the specification is
right. The failure that actually happens in the field is the other one: somebody misreads the standard
and writes the same mistake into the model and the code, the proof still passes because the two sides
still agree, and nothing internal notices.

`make eid-spec-mutation` applies three paired mutations, each dropping or weakening one SGP.29 clause in
the Cryptol model and in the C reference at once:

| paired mutation | C == spec proof | clause-directed vectors |
|---|---|---|
| drop AE.R02, the reserved `89` prefix | passes, blind to it | catches it |
| drop the decimal-digit range check | passes, blind to it | catches it |
| accept remainder 0 as well as 1 | passes, blind to it | catches it |

Three of three are invisible to the proof, and three of three are caught by vectors tied to the
standard's text. That is the argument for clause-directed vectors stated as a measurement rather than as
an opinion, and it is why they belong on the properties an author wrote and not only where an external
standard already pins the answer.

It also caught a defect in this directory's own vectors. The first version had four, and two of them did
not isolate their clause: the non-digit vector also had a failing checksum, so dropping the digit rule
left it rejected for the other reason, and no vector had remainder 0, so widening the check to accept 0
changed nothing. Both are fixed by `vNonDigitValidSum` (a byte of 100, checksum still verifying, since
adding 97 to a digit leaves the remainder unchanged) and `vRemainderZero`. A negative witness is only
worth having when every other clause passes on it, and that is easy to get wrong by hand.
