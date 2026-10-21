# Where the proofs stop

The C proofs stop at function boundaries. SAW proves each C function equal to its Cryptol model.
Isabelle proves that a particular composition of those models computes a product in
`R_q = Z_q[X]/(X^256+1)`. For verification, that `sign.c` composes the C functions that way, on
those buffers, is proved (`proof/saw/sign_verify.saw`), with the callees no proof covers replaced by
assumed specs (A-SIGN in `docs/ASSUMPTIONS.md`). For key generation and signing it is read from the
C. The input ranges are read from the C, except the unpack functions' output ranges, which are
proved (the split rows below). `sign.c` is vendored (2026-10-21); `packing.c`, `rounding.c` and
`fips202.c` are not.

This file lists every hypothesis of the three product theorems and says how each one is
discharged:

- PROVED: by a named theorem or SAW spec;
- split: the row's claim has parts with different labels, given in the row;
- SOURCE: by reading a named line of the C, not proven;
- ASSUMED: taken on trust;
- ARGUED: a reasoned step that is not mechanized.

Line numbers refer to PQClean commit `202a8f9`:
[`sign.c`](https://github.com/PQClean/PQClean/blob/202a8f96315f9ed219387a50f7e40d04af037ea8/crypto_sign/ml-dsa-44/clean/sign.c),
[`packing.c`](https://github.com/PQClean/PQClean/blob/202a8f96315f9ed219387a50f7e40d04af037ea8/crypto_sign/ml-dsa-44/clean/packing.c),
and `target/pqclean/poly.c`, which is that commit's file unchanged.

## The two sides

On the C side, every function called on the product paths below is proved equal to its Cryptol
model on the `-fwrapv` build (`proof/saw/mldsa_ntt.saw`), in the aliasing form its call site uses:
`polyvecl_ntt`, `polyveck_ntt`, `poly_ntt`, `polyvec_matrix_pointwise_montgomery`,
`polyvec{l,k}_pointwise_poly_montgomery`, `polyveck_shiftl`, `polyveck_sub`, `polyveck_reduce`,
`polyvec{l,k}_invntt_tomont`, and everything they call. The loop specs also state that the call
leaves its input buffers unchanged, and mutants claiming a changed input are rejected.

On the model side, the Isabelle theorems are:

- `ntt_mult_ring` (`tier2/convwork/Conv_Bridge.thy`): `invntt(pointwise(ntt a, ntt b)) = a*b`.
- `acc_mult_ring` (`tier2/accwork/Acc_Bridge.thy`): `invntt(preduce(acc u v)) = sum_i f_i * y_i`
  when `v = ntt y`.
- `ver_row_ring` (`tier2/verwork/Ver_Bridge.thy`):
  `invntt(preduce(psub(acc u v, pointwise ch th))) = sum_i f_i * z_i - c * (2^13 * t1)`.

The boundary is between them: whether the C program evaluates those expressions, on those
arguments.

## Key generation: `A*s1` (`acc_mult_ring`)

| Hypothesis | Discharged by |
|---|---|
| `s1hat` is a copy of `s1`, then `v = ntt s1` | SOURCE: `sign.c:48-49` |
| the C computes `invntt(preduce(acc u v))` per row | SOURCE: call order at `sign.c:50-52`; each call PROVED (SAW) |
| `\|s1\| < q` | SOURCE: `rej_eta` writes `2 - t` with `t < 5`, `poly.c:402,406`; sampling not verified |
| `\|A\| < 9q` (the bound is `75423752` = 9q − 1) | SOURCE: `rej_uniform` masks to 23 bits, `poly.c:324` |
| a polynomial `f_i` exists whose NTT is row entry `i` | PROVED: `acc_mult_ring_ex` (via `ntt_int_surj`) |

## Signing: `A*y` (`acc_mult_ring`)

| Hypothesis | Discharged by |
|---|---|
| `z` is a copy of `y`, then `v = ntt z` | SOURCE: `sign.c:138-139` |
| the C computes `invntt(preduce(acc u v))` per row | SOURCE: call order at `sign.c:140-142`; each call PROVED (SAW) |
| `\|y\| < q` | split: PROVED that `polyz_unpack` outputs lie in `[-(2^17 - 1), 2^17]` for any input bytes (`poly_ranges.saw`); SOURCE that `poly_uniform_gamma1` fills `y` by calling it on SHAKE output (`poly.c:467`) |
| `\|A\| < 9q` | SOURCE: `poly.c:324` |
| `mat` still holds the expanded A on every rejection iteration | split: PROVED that the matrix loop leaves it unchanged; SOURCE that no other call between `sign.c:128` and `:140` receives `mat`; ASSUMED that the unverified calls in between (sampling, `decompose`, packing, hashing, `chknorm`) do not write out of bounds |
| `f_i` exists | PROVED: `acc_mult_ring_ex` |

## Signing: `c*s1`, `c*s2`, `c*t0` (`ntt_mult_ring`)

| Hypothesis | Discharged by |
|---|---|
| the vector argument is `ntt s` | SOURCE: `sign.c:129-131` |
| the challenge argument is `ntt c` | SOURCE: `sign.c:155-156` (recomputed on every iteration) |
| the C computes `invntt(pointwise(.,.))` | SOURCE: call order at `sign.c:159-160`, `169-170`, `178-179`; each call PROVED (SAW) |
| `\|c\| < q` | SOURCE: `poly_challenge` writes `1 - 2*(signs & 1)` or copies an earlier coefficient, `poly.c:510-511` |
| `\|s1\|, \|s2\| < q` | split: PROVED that `polyeta_unpack` outputs lie in `[-5, 2]` (`poly_ranges.saw`); SOURCE that `unpack_sk` calls it for `s1` and `s2` (`packing.c:145,150`) |
| `\|t0\| < q` | split: PROVED that `polyt0_unpack` outputs lie in `[-4095, 4096]` (`poly_ranges.saw`); SOURCE that `unpack_sk` calls it (`packing.c:155`) |
| `cp` unchanged across the three calls at `sign.c:159`, `169`, `178` | split: PROVED that each pointwise loop leaves it unchanged; SOURCE that the calls in between do not receive it; ASSUMED that they do not write out of bounds |
| `s1`, `s2`, `t0` (in NTT form) unchanged across rejection iterations | split: PROVED that the pointwise loops leave them unchanged; SOURCE that no other call after `sign.c:131` receives them; ASSUMED as above |

## Verification: `A*z - c*t1*2^13` (`ver_row_ring`)

`sign_verify.saw` proves that `crypto_sign_verify` (messages of 32 bytes, empty context) returns
`MLDSA_Sign::verify` (`model/cryptol/MLDSA_Sign.cry`). In that model the buffer handed to
`polyveck_use_hint` is `caddq(invntt(preduce(psub(acc A v, pointwise ch th))))` with `A` the
output of `polyvec_matrix_expand` on `unpack_pk`'s `rho`, `v = ntt z` for `unpack_sig`'s `z`,
`ch = ntt (poly_challenge c)` for `unpack_sig`'s `c`, and `th = ntt(pshiftl t1)` for `unpack_pk`'s
`t1`. The callees that no proof covers are assumed specs whose outputs are uninterpreted functions
of their inputs (A-SIGN). Seven wrong compositions must fail and do.

| Hypothesis | Discharged by |
|---|---|
| `v = ntt z` | PROVED: `sign_verify.saw` |
| `ch = ntt c` | PROVED: `sign_verify.saw` |
| `th = ntt(pshiftl t1)` | PROVED: `sign_verify.saw` |
| the C computes `invntt(preduce(psub(acc u v, pointwise ch th)))` | PROVED: `sign_verify.saw`, with each call's own spec PROVED (SAW), including the aliasing forms at `sign.c:301` and `303`; ASSUMED that the unverified callees write only their outputs (A-SIGN) |
| `\|z\| < q` | split: PROVED that `polyz_unpack` outputs lie in `[-(2^17 - 1), 2^17]` (`poly_ranges.saw`); SOURCE that `unpack_sig` calls it (`packing.c:227`); `chknorm` at `sign.c:274` narrows it further |
| `\|c\| < q` | SOURCE: `poly.c:510-511` |
| `0 <= t1 <= 1023` | split: PROVED that `polyt1_unpack` outputs lie in `[0, 1023]` (`poly_ranges.saw`); SOURCE that `unpack_pk` calls it (`packing.c:51`) |
| `\|A\| < 9q` | SOURCE: `poly.c:324` |
| `f_i` exists | PROVED for the same `u` by `acc_mult_ring_ex`; not restated as an existential form of `ver_row_ring` |

## Trusted links under every row

- The Cryptol-to-Isabelle step: `cryptol-to-isabelle` is trusted. `make lift-check` regenerates the
  lifted theory and diffs it against the committed one, which is a check, not a proof.
- The code generator: `ntt_mult_ring`, `acc_mult_ring` and `ver_row_ring` depend on Isabelle's
  `by eval` oracle (OF-4 in `docs/ASSUMPTIONS.md`). The oracle gates in `Acc_Bridge.thy` and
  `Ver_Bridge.thy` fail the build if they pick up any other oracle. `acc_mult_ring_ex` is not in
  that gate; it is proved from `acc_mult_ring` and `ntt_int_surj`, so it carries the same oracle.

## Across the build boundary

The rows above are about the `-fwrapv` build. Carrying them to a normal build has these parts:

- No signed overflow on the default bitcode, polynomial layer: PROVED (`poly_nsw.saw`, in
  `make verify`), given pointwise operands within 9q. That bound is PROVED for transform outputs
  (`ntt_out_bounded`, about the models) and SOURCE for A (`poly.c:324`).
- No signed overflow on the default bitcode, forward NTT: PROVED once (`ntt_nsw.saw`, 12.5 h,
  2026-07-10, out of band, no paired mutant).
- No signed overflow in `invntt_tomont` and the `poly_ntt` / `poly_invntt_tomont` wrappers: ARGUED
  from the `-fwrapv` proofs and the Isabelle bounds.
- `poly_shiftl` has no signed-shift UB: ARGUED from the `t1` range above. Clang emits a plain `shl`,
  so SAW cannot see this kind of UB on either build.
- The two builds are the same program apart from `nsw` and `inbounds` flags: CHECKED by a script
  (`scripts/check_wrapv_diff.sh`), not proved.
- The compiler is correct: ASSUMED.

## Making the boundary smaller

The SOURCE rows are of two kinds:

- Call order and argument flow (`v = ntt y`, which buffer goes where, nothing else touches `mat`):
  done for verification (`sign_verify.saw`, SAW on the vendored `sign.c` with the existing specs
  as overrides). Key generation is straight-line and could be done the same way. Signing has the
  `goto rej` loop, which SAW cannot unroll when the exit depends on opaque checks; it needs either
  a loop invariant or a spec of one iteration.
- Input ranges: the unpack functions are done (`proof/saw/poly_ranges.saw`, in `make saw`, on
  the default bitcode, with mutants one tighter at each end that must fail). The samplers are not:
  `rej_uniform` (A) and `rej_eta` (keygen `s1`, `s2`) write at a data-dependent index, and a
  one-call spec did not finish in z3 or yices within 5 to 9 minutes (measurements in the script
  header); `poly_challenge` has a rejection loop with no fixed bound.

The call-order proof for key generation and signing has not been done.
