# FIPS 204 correspondence: what an external audit would have to rule on

Isabelle certifies that our theorems follow from our definitions. It cannot certify that our
definitions are FIPS 204. That gap is why this file exists, and why an external specification audit is
worth commissioning: the auditor's job is the left-hand column, not the proof tactics.

Nothing downstream removes this gap. SAW checks C against Cryptol, `cryptol-to-isabelle` checks that
the Isabelle model is the Cryptol model, and Isabelle checks that the model meets the specification on
the right. Every one of those links is mechanical. The link from the right-hand column to the printed
standard is a human reading, and it is ours.

Rebuilt 2026-09-23 against `spec/isabelle/` as it stands. The previous version of this file audited
only the v1 `Assay` session, predated everything in `tier2/` and `kem/`, and therefore recorded four
rows as ABSENT that have since been proven. That was wrong for about three months, in a public
repository, and it understated the development rather than overstating it.

## The reduce layer (session `Assay`, and `afp/MLDSA_Reduce` standalone)

| FIPS 204 item | our Isabelle definition | status |
|---|---|---|
| `q = 8380417` | `q` (`MLDSA_NTT_Spec.thy:17`) | present, literal, auditor confirmation only |
| Montgomery reduction contract | `is_montgomery_reduction`: `2^32 * r ≡ a (mod q) ∧ -q < r < q` | present; domain **half-open** by our choice, see below |
| Montgomery input domain | `mont_input_ok`: `-(2^31*q) ≤ a < 2^31*q` | present; **differs from the reference comment**, deliberately (OF-1) |
| `reduce32` contract | `is_reduce32`: `r ≡ a (mod q) ∧ -6283009 ≤ r ≤ 6283008` | present; the true reachable window, **not** the documented one (OF-2) |
| `caddq` contract | `is_caddq` | present |
| `freeze` contract | `is_freeze` | present |

## The transform (sessions `Tier2`, `Tier2_InvWork`, `Tier2_Signed`, `Tier2_InvSigned`)

| FIPS 204 item | our Isabelle statement | status |
|---|---|---|
| ζ = 1753, the primitive root | literal in `ntt_bridge` (`tier2/work/Mont_Bridge.thy:1498`) | present |
| bit-reversal convention | `brv` (`tier2/Bitrev.thy`), with `brv_brv` and `brv_bij` proven | present |
| forward transform (Alg. 41) | `ntt_bridge`: `sint_seq (nth_seq (ntt w) k) mod q = (∑ j<256. cf w j * 1753^((2*brv 8 k + 1)*j)) mod q`, for `bounded w`, `k < 256` | present |
| forward transform, signed window | `ntt_signed_correct` (`tier2/signwork/Signed_Bridge.thy:248`), same equation for `ntt_bounded 8380416 w` | present |
| inverse transform (Alg. 42) incl. scaling | `invntt_bridge` (`tier2/invwork/Inv_Mont_Bridge.thy:3676`): `(2^32 * sint_seq (nth_seq (invntt w) k)) mod q = (sint_seq invf * (∑ m<256. cf w m * zpw (-(2*brv 8 m + 1)*k))) mod q` | present |
| inverse transform, signed window | `invntt_signed_correct` (`tier2/invsignwork/Inv_Signed_Bridge.thy:238`) | present |
| NTT coefficient domain | `ntt_bounded` | present, as a bound predicate |
| overflow-freedom | `ntt_overflow_free`, `invntt_overflow_free` | present; a **safety** property, not transform correctness |

FIPS 203, for comparison: `ntt_residue` (`kem/work/Kyber_Residue.thy:698`) states the degree-2 residue
form rather than a full split, because only `2^8` divides 3329 - 1. Different statement, same shape.

## What is still not proven, and it is the important row

**There is no theorem that the transform computes a product.** Nothing here states

    invntt(ntt a ⊙ ntt b) = a ⋆ b   in Z_q[X]/(X^256+1)

and there is no pointwise multiplication anywhere in the tree: no Cryptol function, no SAW spec, no
Isabelle theorem, and `poly.c` is not vendored. What is proven is that one butterfly network evaluates
a polynomial at the 256 odd powers of 1753 mod q, and that a second inverts that evaluation up to a
scale. Neither says the pair multiplies, which is the only reason the NTT is in ML-DSA at all.

This is scoped as v4 in `docs/ROADMAP.md`, with the obligations broken out. Until it lands, a reader
should take the transform results as Cooley-Tukey at one modulus, which is what they are.

## Two places where we deliberately differ from the reference implementation's comments

Both are recorded in `ASSUMPTIONS.md` as OF-1 and OF-2 and disclosed upstream as
pq-crystals/dilithium#114. An auditor must rule on whether our specification or the reference comment
is the right reading:

- `montgomery_reduce(2^31*q) = q` violates the documented strict `-q < r < q`, so we specify the
  half-open domain rather than the inclusive one the comment gives.
- `reduce32` returns `-6283009` for an input admissible under the documented one-sided precondition,
  one below the documented window, so we specify the true reachable window.

## Scope of an audit worth commissioning

Every row in both tables, plus the two deliberate differences. The transform rows are the ones that
matter most and the ones least amenable to a quick read: an auditor has to decide whether
`(∑ j<256. cf w j * 1753^((2*brv 8 k + 1)*j)) mod q` at bit-reversed index is the transform FIPS 204
§7.5 Algorithm 41 defines, including the output ordering convention. That is a real piece of work and
it is the part neither Isabelle nor SAW nor CI can do for us.
