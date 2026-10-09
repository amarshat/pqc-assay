# The ML-DSA reference NTT multiplies polynomials, checked from the C

*Amar Akshat &middot; [github.com/amarshat](https://github.com/amarshat)*

ML-DSA spends most of its arithmetic multiplying polynomials in Z_q[X]/(X^256+1), with q = 8380417.
It does this the standard way: transform both operands with the NTT, multiply coefficient by
coefficient, transform back. Earlier work in this repository proved that PQClean's reference C
computes the FIPS 204 forward and inverse NTT. That says the transform is the transform. It does not
say that transform, pointwise multiply and inverse, as the C actually composes them, give you the
product. This post is about closing that gap, and about where in the scheme the result applies.

Everything here is in the [repository](https://github.com/amarshat/pqc-assay) and reproduces from a
`make` target. The target is PQClean's ML-DSA-44 `clean` implementation at commit `202a8f9`,
vendored unmodified with SHA-256 pinned.

## What is proved

For polynomials a and b whose coefficients all satisfy |c| < q:

    invntt_tomont(poly_pointwise_montgomery(ntt(a), ntt(b))) = a * b   in Z_q[X]/(X^256+1)

Here `*` and the reduction mod X^256+1 are the polynomial multiplication and remainder from
Isabelle's standard library, at a type of integers mod 8380417. They are not a convolution formula
written for this project, so the right-hand side is not something the proof could have been tuned to.
The theorem is `ntt_mult_ring` in
[`Conv_Bridge.thy`](https://github.com/amarshat/pqc-assay/blob/main/spec/isabelle/tier2/convwork/Conv_Bridge.thy).

The matrix products need a second form, because ML-DSA samples the matrix A directly in NTT form.
Its rows are never the output of `ntt`, so the theorem above does not apply to them. Each row of
A*y is computed as four pointwise products summed with `poly_add`, then `poly_reduce`, then the
inverse. The theorem `acc_mult_ring` in
[`Acc_Bridge.thy`](https://github.com/amarshat/pqc-assay/blob/main/spec/isabelle/tier2/accwork/Acc_Bridge.thy)
says: for any polynomials A_i whose transforms are the sampled rows, the C's output for that row is
A_1*y_1 + A_2*y_2 + A_3*y_3 + A_4*y_4 mod X^256+1. Every row has such A_i, because the transform is
onto mod q, and that is proved too (`ntt_int_surj`). This is FIPS 204's NTT^-1(A_hat o NTT(y)) read as
polynomials.

The Montgomery bookkeeping is proved rather than assumed. `poly_pointwise_montgomery` leaves a
factor 2^-32. `invntt_tomont` multiplies by 41978 and leaves another 2^-32. The unnormalised inverse
leaves a factor 256. Since 41978 * 256 = 2^64 mod q, these cancel exactly, and the theorem has no
leftover scale. The intermediate bounds are proved as well: forward outputs are not reduced and can
reach 9q, and the proof checks that the products of two such values still fit
`montgomery_reduce`'s input range, that four pointwise outputs added together cannot overflow a
32-bit int, and that the sum is inside `reduce32`'s precondition.

## Where it applies in ML-DSA

| Operation | Where | Covered |
|---|---|---|
| A*s1 | key generation | yes |
| A*y | signing | yes |
| c*s1, c*s2, c*t0 | signing | yes |
| A*z - c*t1*2^d | verification | no |

Covered means every function on the path, from the vector and matrix loops in `polyvec.c` down to
`montgomery_reduce`, is proved equal to a Cryptol model, and the Isabelle theorems apply to the
composition. The order in which `sign.c` calls those functions is read from the source, not proved.

Verification is not covered yet. It subtracts c*t1*2^d before the inverse and calls the pointwise
loop with its output overlapping an input, and neither case is proved.

## How the chain is put together

1. SAW proves each C function equal to a Cryptol model: `ntt`, `invntt_tomont`,
   `poly_pointwise_montgomery`, `poly_add`, `poly_reduce`, `polyvecl_pointwise_acc_montgomery`, the
   `poly_ntt` and `poly_invntt_tomont` wrappers, and the loops over vector entries and matrix rows.
   Each proof has a mutant (the claimed result with 1 added to one coefficient) that SAW rejects with
   a counterexample. `make saw`.
2. cryptol-to-isabelle lifts the Cryptol model into Isabelle. A check regenerates the lift and diffs
   it against the committed theory, so the Isabelle proofs are about the same model SAW checked.
   `make lift-check`.
3. Isabelle proves the lifted models compose to the ring product, using the transform theorems from
   the earlier work, the convolution theorem instantiated at q = 8380417, and a lemma that the
   negacyclic convolution formula is polynomial multiplication mod X^n+1. `make convolution`.

`make verify` runs all of it. The pinned checkers are SAW 1.5.1 (with its bundled z3),
cryptol-to-isabelle from the same release, Isabelle2025-2 and the AFP snapshot of 2026-06-05. The
results are claimed for those versions.

## What it does not cover

- Signature verification, as above.
- The C side is proved on bitcode compiled with `-O0 -fwrapv`. That no signed overflow happens on a
  normal build is mechanized for the forward NTT and argued from the proved bounds for the rest.
  The compiler is trusted.
- Isabelle's code generator is trusted for some facts about the constant twiddle tables (the
  `by eval` method). A check in the build fails if the headline theorems pick up any other oracle.
- The bound on A's coefficients (at most 9q) is read from `poly_uniform`, which masks every candidate
  to 23 bits. `poly_uniform` itself is not verified, and neither is the sampling against FIPS 204.
- ML-DSA-44 only. The vector length 4 is fixed in the models.
- Reference C only. Not the AVX2 code, and not constant-time properties.

The full list, with file references, is in
[`docs/ASSUMPTIONS.md`](https://github.com/amarshat/pqc-assay/blob/main/docs/ASSUMPTIONS.md) under
A-ROW, A-POINTWISE and OF-4.

## Prior art

The AFP entry CRYSTALS-Kyber proves the convolution theorem for the NTT generically, over a quotient
ring. The mathematics here is the same; the part that is new is connecting it to a C implementation,
including the Montgomery factors and the bounds, and to the places the scheme calls it.

## How the claims were checked

Before publishing, each milestone went to an adversarial review that re-ran the tools and checked
every claim against the output. The first round found that an early draft overstated where the
result applied, that a "no `by eval`" claim was true of the new files but not of the theorem, and
that three of four Isabelle mutation tests only showed the proof script breaking when its statement
changed. The second found unverified loops between `sign.c` and the proved functions. Those loops
are now proved, and the rest is corrected in the text above.

## Reproducing

    git clone https://github.com/amarshat/pqc-assay && cd pqc-assay
    ./scripts/setup.sh           # pinned toolchain into .tools/ (macOS arm64 tested)
    make saw                     # C == Cryptol
    make lift-check              # Isabelle model == lift of the Cryptol SAW checked
    make convolution             # the Isabelle theorems in this post
    make verify                  # everything

The first Isabelle build compiles its library dependencies and takes a while; later builds take
seconds.
