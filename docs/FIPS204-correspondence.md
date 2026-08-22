# FIPS 204 correspondence: what an external audit would have to rule on

Isabelle certifies that our theorems follow from our definitions. It cannot certify that our definitions
are FIPS 204. That gap is the reason for this file, and the reason an external specification audit is
worth commissioning: the auditor's job is the left-hand column, not the proof tactics.

This table is built from the development as it stands (`spec/isabelle/`, checked 2026-08-22), not from
what we intended to build. Four rows are empty, and that is the first finding.

| FIPS 204 item | our Isabelle definition | status |
|---|---|---|
| `q = 8380417` | `q` (`MLDSA_NTT_Spec.thy:17`) | present, literal, needs auditor confirmation only |
| Montgomery reduction contract | `is_montgomery_reduction` (`:29`): `2^32 * r ≡ a (mod q) ∧ -q < r < q` | present; the domain is **half-open** by our choice, see below |
| Montgomery input domain | `mont_input_ok` (`:24`): `-(2^31*q) ≤ a < 2^31*q` | present; **differs from the reference comment**, deliberately (OF-1) |
| `reduce32` contract | `is_reduce32` (`:48`): `r ≡ a (mod q) ∧ -6283009 ≤ r ≤ 6283008` | present; window is the true reachable one, **not** the documented one (OF-2) |
| `caddq` contract | `is_caddq` (`:35`) | present |
| `freeze` contract | `is_freeze` (`:52`) | present |
| NTT coefficient domain | `ntt_bounded` (`Assay_Equivalence.thy:501`) | present, as a bound predicate |
| **ζ = 1753, the primitive root** | none in the spec. `zeta` appears only in the machine-generated lift and in bound lemmas | **ABSENT** |
| **BitRev / bit-reversal convention** | none anywhere: zero occurrences in all three theory files | **ABSENT** |
| **The NTT transform equation (Alg. 41)** | none. We prove a bound on the transform, not the transform | **ABSENT** |
| **InvNTT scaling (Alg. 42)** | `invntt` appears only in the generated lift; no correctness theorem | **ABSENT** |

## What the two headline theorems actually say

```
montgomery_reduce_correct   the lifted montgomery_reduce satisfies is_montgomery_reduction
                            on the half-open input domain
ntt_overflow_free           inputs bounded by 2^31-2^27 keep every coefficient within
                            +/-2080309256 through all eight levels
```

The second is an **overflow-freedom** result. It is not transform correctness. Nothing in this
development states that our NTT computes the negacyclic transform FIPS 204 Algorithm 41 defines, so an
audit asking "does `fips_ntt` match the standard" would find no `fips_ntt` to look at. The C-versus-model
equivalence for the transform is discharged by SAW against the Cryptol model, which is a different leg
and a different kind of claim.

## Two places where we deliberately differ from the reference implementation's comments

Both are recorded in `ASSUMPTIONS.md` as findings OF-1 and OF-2, and both were disclosed upstream. An
auditor must rule on whether our specification or the reference comment is the right reading of FIPS 204:

- `montgomery_reduce(2^31*q) = q` violates the documented strict `-q < r < q`, so we specify the
  half-open domain rather than the inclusive one the comment gives.
- `reduce32` returns `-6283009` for an input admissible under the documented one-sided precondition,
  one below the documented window, so we specify the true reachable window.

## Scope of an audit worth commissioning

Rows one to seven, plus the two deliberate differences. That is a real piece of work and it is the part
neither Isabelle nor SAW nor CI can do for us. The four absent rows are not audit material; they are
missing development, and the honest sequence is to close them first or to state plainly that the NTT
result is a bound and not a refinement.
