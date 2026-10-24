<p align="center">
  <img src="assay-logo.png" alt="PQC-Assay, C = spec" width="260">
</p>

<h1 align="center">PQC-Assay</h1>

<p align="center">
  <a href="https://github.com/amarshat/pqc-assay/actions/workflows/verify.yml"><img src="https://github.com/amarshat/pqc-assay/actions/workflows/verify.yml/badge.svg" alt="verify"></a>
  <a href="https://github.com/amarshat/pqc-assay/actions/workflows/saw.yml"><img src="https://github.com/amarshat/pqc-assay/actions/workflows/saw.yml/badge.svg" alt="saw"></a>
  <a href="https://github.com/amarshat/pqc-assay/actions/workflows/rust.yml"><img src="https://github.com/amarshat/pqc-assay/actions/workflows/rust.yml/badge.svg" alt="rust"></a>
  <a href="https://github.com/amarshat/pqc-assay/actions/workflows/cap.yml"><img src="https://github.com/amarshat/pqc-assay/actions/workflows/cap.yml/badge.svg" alt="cap"></a>
  <a href="LICENSE"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="MIT"></a>
  <img src="https://img.shields.io/badge/Isabelle-2025--2-9cf.svg" alt="Isabelle2025-2">
  <img src="https://img.shields.io/badge/SAW-1.5.1-orange.svg" alt="SAW 1.5.1">
  <a href="https://doi.org/10.5281/zenodo.21178811"><img src="https://zenodo.org/badge/DOI/10.5281/zenodo.21178811.svg" alt="DOI"></a>
</p>

PQC-Assay machine-checks unmodified post-quantum reference C against specifications written from
the standards. SAW proves the C equal to a Cryptol model, Galois's `cryptol-to-isabelle` lifts that
model into Isabelle, and Isabelle proves the lifted model equal to the mathematics. It is the
toolchain Apple used for its 2026 `corecrypto` work; none of Apple's code or theories are used here.

There are two targets. The first is ML-DSA-44 (FIPS 204) in PQClean's reference C. The chain reaches
from the C functions to ring arithmetic in `R_q = Z_q[X]/(X^256+1)`, and `sign.c` is proved to
compose those functions. Apple's `corecrypto` proofs already cover ML-DSA signing end to end on
Apple's code: their loop proof covers every iteration up to a counter bound, and they verify Keccak
and the samplers, which are assumed here. So this repo's ML-DSA work is an independent check of a
different code base, not a first. The second target, and the current main line, is HQC (selected by
NIST in 2025), starting with its reference polynomial multiplication. Writeup on the ML-DSA side:
[The ML-DSA reference NTT multiplies polynomials: C functions to models, models to the ring](https://amarshat.github.io/pqc-assay/writeup/ml-dsa-ntt-multiplies.html).

> **Where the proofs stop.** Each C function is proved equal to its model, and Isabelle proves that
> a composition of those models computes the product. That `sign.c` composes the functions that
> way, on those buffers, is proved for key generation, verification, and signing up to one rejected
> pass of the `goto rej` loop, with hashing, unpacking, sampling, packing and hints taken as assumed
> specs. The input ranges the theorems assume are read from the C. Every hypothesis of the product theorems, and whether a proof or a
> source line discharges it, is listed in [`docs/COMPOSITION.md`](docs/COMPOSITION.md).

## Proved (ML-DSA-44)

Each row means a pinned tool exited 0 on the stated property, in `make verify` unless noted.

| Property | Checked by |
|---|---|
| `reduce.c` (`montgomery_reduce`, `reduce32`, `caddq`, `freeze`) ≡ Cryptol, no signed overflow in range | SAW + z3 |
| `reduce.c` models meet their contracts (residue mod q, output windows) | Isabelle |
| `reduce.c` under a second C semantics: the AutoCorres2 (C-parser) abstraction of each function takes no undefined-behaviour guard on the contract windows and returns the value of the same Cryptol model | Isabelle + AutoCorres2, `make ac2`; separate setup, not in `make verify` |
| each C function on the product paths ≡ its Cryptol model (`-fwrapv` build): `ntt`, `invntt_tomont`, pointwise, add, sub, shift, reduce, the accumulator, the wrappers and the vector and matrix loops; loops leave their inputs unchanged | SAW |
| the Cryptol models lift to the Isabelle models used below | `make lift-check` regenerates and diffs |
| forward NTT model ≡ FIPS 204 forward NTT mod q | Isabelle `ntt_bridge` on `[0,q)`, `ntt_signed_correct` on `\|coeff\| < q` |
| inverse NTT model ≡ FIPS 204 inverse NTT mod q, scaled by `mont/256` (`mont` = 2³² mod q) | Isabelle `invntt_bridge` on `[0,q)`, `invntt_signed_correct` on `\|coeff\| < q` |
| no int32 overflow in the NTT models (forward on `±(2³¹−2²⁷)`, inverse on `\|coeff\| < q`) | Isabelle `ntt_overflow_free`, `invntt_overflow_free` |
| model composition `invntt(pointwise(ntt a, ntt b))` = `a*b` in `R_q`, for `\|coeff\| < q` | Isabelle `ntt_mult_correct`, `ntt_mult_ring` |
| model composition `invntt(preduce(acc u v))` with `v = ntt y` = `sum_i f_i*y_i` in `R_q` (`f_i` any polynomial whose NTT is row entry i of `A_hat`, which exists) | Isabelle `acc_mult_fips`, `acc_mult_ring`, `acc_mult_ring_ex` |
| model composition for verification's row, `A*z - c*t1*2^13`, FIPS form and in `R_q` | Isabelle `ver_row_fips`, `ver_row_ring` |
| `negconv` is multiplication in `R_q`; the NTT locale has a model at the ML-DSA parameters | Isabelle `negconv_is_mult`, `mldsa_model` |
| default build, polynomial layer: no signed-overflow UB in pointwise, add, sub, reduce, accumulator and the loops on the product paths, given pointwise operands within 9q (= 75423752) | SAW + z3, `make poly-nsw`, 48 min on CI's clang 17 |
| output ranges of `polyt1_unpack` [0, 1023], `polyt0_unpack` [−4095, 4096], `polyeta_unpack` [−5, 2], `polyz_unpack` [−(2¹⁷−1), 2¹⁷], for any input bytes, default build | SAW + z3, `make saw` |
| `sign.c`, verification: `crypto_sign_verify` returns the composition in `MLDSA_Sign.cry`, so the buffer it hands to `use_hint` is `caddq(invntt(reduce(A*ntt(z) - ntt(c)*ntt(t1 << 13))))` on the unpacked `z`, `c`, `t1` and the expanded `A`; callees outside the proofs are assumed specs with opaque outputs (A-SIGN); 32-byte messages, empty context | SAW + z3, `make saw` |
| `sign.c`, key generation: `crypto_sign_keypair` writes the `pk`, `sk` of the composition in `MLDSA_Sign.cry` for whatever bytes `randombytes` returns, so `t1`, `t0` come from `power2round(caddq(invntt(reduce(A*ntt(s1))) + s2))`; same assumed-spec boundary | SAW + z3, `make saw` |
| `sign.c`, signing: `crypto_sign_signature` writes the signature of the accepted pass of the composition in `MLDSA_Sign.cry` (`z = reduce(invntt(ntt(c)*ntt(s1)) + y)`, `w0 - c*s2`, `c*t0`, hint, packing) when pass 0 is accepted, and when pass 0 is rejected at any of its four checks and pass 1 is accepted; same assumed-spec boundary, 32-byte messages, empty context | SAW + z3, `make saw` |

## Proved (HQC)

Target: `target/hqc/`, the official HQC v5.0.0 reference `gf2x.c`, unmodified, for hqc-1, hqc-3 and
hqc-5. Every SAW spec has a mutant that must fail; all 69 are rejected. `make hqc` took 19 min 18 s
before the Reed-Muller and concatenated-encoder steps were added (2026-10-22); those take 84 s,
134 s and 347 s for the three sets (2026-10-24); `make hqc-isabelle` about 20 s; Apple M2 Max.

| Property | Checked by |
|---|---|
| `schoolbook_mul(s)` = the Karatsuba model `km<s>` at each leaf size, and `km<s>` = Cryptol's `pmult` there (cross-check) | SAW + rme (algebraic normal form over GF(2)), `make hqc` |
| `karatsuba_mul(s)` = `km<s>` at every size it reaches, up to the full 277, 561 and 901 words, with every `tmp_buffer` access in bounds; `vect_mul`'s buffer of `16 * VEC_N_SIZE_64` words is enough | SAW + z3, children as proved overrides, `make hqc` |
| `vect_mul` = `vmul`, the model folded mod x^n − 1, for every input | SAW + z3, `make hqc` |
| the Cryptol models lift to the Isabelle models used below | `make lift-check` regenerates and diffs |
| `vmul a b` = `(a * b) mod (x^n − 1)` over GF(2), for inputs of degree below n (n = 17669, 35851, 57637) | Isabelle `HQC_P1/P3/P5.vmul_correct`, no oracle (`HQC_Gate`), `make hqc-isabelle` |
| `gf.c`: `gf_carryless_mul` = `pmult`, `gf_reduce` = `pmod` by 0x11D for every 16-bit input, `gf_mul`, `gf_square`, and `gf_inverse` = a^254 (the inverse of every nonzero a) in GF(2^8) | SAW + z3, `make hqc` |
| `reed_solomon_encode` writes a Reed-Solomon codeword: the message in the top k bytes, and the codeword polynomial vanishes at α^1 … α^2δ (α = 2), which fixes the parity bytes; [46,16], [56,24], [90,32] | SAW + rme, `make hqc` |
| `reed_muller_encode` writes the duplicated RM(1,7) code: for each of the n1 message bytes, n2/128 copies of the 128 values of the affine function the byte defines over F_2^7 (a property, not the C's generator masks); n2/128 = 3, 5, 5 | SAW + z3, `make hqc` |
| `code_encode` (the concatenated code) writes the Reed-Muller encoding of a Reed-Solomon codeword that carries the k message bytes, with the two encoders as proved overrides and the zeroizing `memset` executed | SAW + z3, `make hqc` |

Together: on inputs stored the way HQC stores them (no bit at or above n), the reference `vect_mul`
multiplies in GF(2)[x]/(x^n − 1). The GF(2^8) and Reed-Solomon rows use the field of v5.0.0 and of
the 2025-08-22 HQC specification (0x11D); the 2026-10-12 specification changes the field polynomial
to 0x11B, so those two rows will be regenerated when code for it is published. `vect_mul` does not
depend on it. The compiler (`-O0`), SAW, `cryptol-to-isabelle` and Isabelle are
trusted; see A-HQC in [`docs/ASSUMPTIONS.md`](docs/ASSUMPTIONS.md).

### The AVX2 implementation

Target: `target/hqc/avx2/`, the x86-64 `gf2x.c` of the same v5.0.0 commit (unmodified; the bitcode is
normalized in three documented places, A-HQC item 12), cross-compiled at `-O0` with Homebrew clang 22.
`make hqc-avx` runs SAW at `-v 3`; the three scripts took 377 s (hqc-1), 2666 s (hqc-3) and 2520 s
(hqc-5) on the same machine (2026-10-24, hqc-5 measured on its own after the full run passed); all
23 mutants are rejected.

| Property | Checked by |
|---|---|
| `karat_mult_1` (nine `pclmulqdq`, 4 words) = the reference leaf model `km4` | SAW + rme, `make hqc-avx` |
| `karat_mult_2/4/8` (and `_16` for hqc-3/5) = `km8` … `km64`, each with the level below as a proved override | SAW + z3, `make hqc-avx` |
| `karat_mult3` (hqc-1/3, three-way) = `k3step`, `karat_mult_5` (hqc-5, five-way, 35 static arrays allocated uninitialised) = `k5step` | SAW + z3, `make hqc-avx` |
| `toom_3_mult` = `toom3` (hqc-1/3, y = x^64) or `toom5` (hqc-5, y = x^256), its 13 static arrays starting with arbitrary contents; for hqc-1/3 two of them carry one vector of IR slack because of the over-read reported as OF-5 (A-HQC item 12), for hqc-5 none | SAW + z3, `make hqc-avx` |
| `vect_mul` writes the `VEC_N_SIZE_BYTES` bytes of `vmulA a b` = `fold` of the Toom product, for every input | SAW + z3, `make hqc-avx` |
| the AVX2 Cryptol models lift to the Isabelle models used below | `make lift-check` |
| `vmulA a b` = `(a * b) mod (x^n − 1)` over GF(2), for inputs of degree below n; `k3step`, `k5step`, `toom3` (any third size ≥ 4) and `toom5` are proved as generic lemmas | Isabelle `AVX_P1/P3/P5.vmulA_correct`, no oracle (`HQC_Gate`), `make hqc-isabelle` |

Together with the reference rows: on inputs of degree below n the reference and the AVX2 `vect_mul`
compute the same polynomial, so they agree on the `VEC_N_SIZE_BYTES` bytes the AVX2 function writes
(the reference writes `VEC_N_SIZE_64` whole words; the AVX2 one leaves the rest of its 284-, 572- or
936-word output buffer untouched). SAW's `pclmulqdq` semantics are trusted and three AVX intrinsics
(unaligned load, per-lane shifts) have assumed specs; A-HQC item 12 lists them with the IR
normalizations.

## Checked once, not gated

This row met the bar above once but is not re-run and has no mutant that must fail, so it does not
meet the mutant policy the Proved table holds to.

| Property | Checked by |
|---|---|
| default build, forward NTT: no signed-overflow UB, and ≡ model, on `±(2³¹−2²⁷)` | SAW + bitwuzla, `make ntt-nsw`; one run, 12.5 h, 2026-07-10, before `poly.c` was vendored |

## Not proved

| Item | Status |
|---|---|
| HQC: both decoders, sampling, the KEM | not started |
| signing in `sign.c` when the `goto rej` loop runs three or more passes | not proved (one and two passes are, above); [`docs/COMPOSITION.md`](docs/COMPOSITION.md) |
| input ranges the theorems take, at the call sites: that `packing.c` and `poly_uniform_gamma1` get `t1`, `t0`, `s1`, `s2`, `z`, `y` from the unpack functions above; `\|A\| < 9q` (23-bit mask in `rej_uniform`), keygen's `s1`, `s2` (`rej_eta`) and `\|c\| <= 1` (`poly_challenge`) | read from the source (the three samplers are not verified) |
| two builds are the same program apart from `nsw` / `inbounds` flags | checked by a script (`scripts/check_wrapv_diff.sh`), not proved |
| default build: inverse NTT and the `poly_ntt` / `poly_invntt_tomont` wrappers have no signed-overflow UB | argued from the `-fwrapv` proofs and the Isabelle bounds |
| default build: `poly_shiftl` has no signed-shift UB | argued from the `t1` range (clang emits a plain `shl`, so SAW cannot see it) |
| the compiler | trusted (`-O0`) |
| sampling, rounding, hints, packing (other than the unpack output ranges above), hashing; constant time | not claimed |

The 9q operand bound comes from Isabelle's `ntt_out_bounded` for transform outputs and from the
23-bit mask in `rej_uniform` for A (read from the source). The Isabelle theories contain no `sorry`,
`oops` or `smt`, and CI greps `spec/`, `afp/` and `proof/` for `sorry`/`oops`/`admit` on every push. They use `by eval`, which
trusts the code generator, 88 times (85 in `make verify`), for the twiddle tables and a few gcd
facts. Every NTT theorem in the Proved table depends on it (OF-4, measured with `Thm_Deps.all_oracles`);
`negconv_is_mult` does not. Results are claimed for the pinned checkers: SAW 1.5.1,
`cryptol-to-isabelle` from the same release, Isabelle2025-2, AFP 2026-06-05.

Along the way we found two off-by-one errors in the bounds documented in PQClean's `reduce.c`
(OF-1, `montgomery_reduce`; OF-2, `reduce32`). Neither causes a miscomputation. Both were reported
upstream as pq-crystals/dilithium#114.

## Other targets

ML-KEM-512 (FIPS 203) goes through the same pipeline on PQClean's `ml-kem-512/clean`:
`montgomery_reduce`, `barrett_reduce` and the forward and inverse `ntt` ≡ Cryptol (SAW, run in
`saw.yml`), and the forward NTT model ≡ the FIPS 203 degree-2 residue transform (Isabelle
`ntt_residue`, in `make verify`). The inverse's FIPS 203 correctness is not done, and the no-overflow
step is argued (int16 operands cannot overflow int32).

For the RustCrypto `ml-dsa` crate (Rust, via MIR), the crate's field arithmetic and NTT layers in SAW over
`mir-json`. Its hard step, Barrett reduction on products below `2^46`, stalls every bit-blaster SAW
ships; it is closed with bitwuzla (`make barrett-solver`) and separately in Isabelle with no oracle
(`make barrett`).

Q-SEAL ([`docs/qseal/QSEAL-v0.1.md`](docs/qseal/QSEAL-v0.1.md), [`qseal/`](qseal/)) is a hybrid
ECDSA P-256 + ML-DSA-44 secure-element attestation layer. Six of its seven spec targets are SAW
proofs of a C reference against Cryptol models, the other is a ProVerif safety property, and each
has a mutant that must fail. Target 7 covers field values, not lengths, and target 3 leaves both
signature verifiers uninterpreted, so none of the ML-DSA results above are composed into it. Cap-V1
([`cap/`](cap/)) is a capability token for agent delegation whose Rust verifier is checked with Kani
(55 harnesses). The CVE anchor ([`cve-anchor/`](cve-anchor/)) proves a reference decoder written here,
not the affected crate's, against the FIPS 204 hint-decode rule CVE-2026-24850 broke, and the buggy
variant is rejected. The motivation is in [`WHY.md`](WHY.md).

[`external-corpus/`](external-corpus/) runs the non-vacuity checks against the example proofs shipped inside SAW 1.5.1. A specification weakened so it still
admits a state went unflagged at 22 of 27 sites.

The reduce-layer theory was submitted to the Archive of Formal Proofs and rejected on scope; see
[`afp/README.md`](afp/README.md).

## Limits

The verified code is the portable reference C. What ships (AVX2/aarch64 code in OpenSSL, BoringSSL,
AWS-LC, `mldsa-native`) is different code. `mldsa-native` is verified with CBMC and HOL-Light. ePrint
2026/1032 reports a reduction-bound overflow in optimized code that passed test vectors. The C proofs are on `-O0` bitcode, so the compiler
is trusted. Everything is functional correctness; nothing here is about side channels.

## Reproduce

macOS on Apple Silicon; tool versions are pinned in `scripts/setup.sh`.

```bash
./scripts/setup.sh                   # pinned SAW, Cryptol, Isabelle, cryptol-to-isabelle
./scripts/setup_isabelle_cryptol.sh  # AFP + the SAW 'Cryptol' Isabelle session (slow, once)
make verify                          # every gated step; non-zero exit = a proof failed
make saw                             # SAW only, fast
make hqc hqc-avx hqc-isabelle        # HQC: reference and AVX2 vect_mul, field ops, encoders; three parameter sets
make claim-lint                      # SAW specs have paired mutants (exemptions printed); cited paths exist
```

The full `make verify` took 3 h 20 min in `verify.yml` run 38100891287 on 2026-10-11 (macos-15
runner, Apple clang 17.0.0, manual dispatch); the workflow caches Isabelle heaps, so warm runs are
shorter. `verify.yml` runs on every push that touches `spec/`, `afp/`, `proof/`, `model/`,
`target/`, `scripts/` or the Makefile, so the badge reflects the last such commit. `make ntt-nsw`, `make barrett-solver` and `make ac2` (after `scripts/setup_autocorres2.sh`, which needs a clang >= 15) are out of band, and `ntt-nsw` needs macOS 15 (the
pinned bitwuzla does not load on 13).

## Layout

| Path | What |
|------|------|
| `target/` | Vendored C, pinned (`target/README.md`): PQClean ML-DSA-44 and ML-KEM-512, HQC v5.0.0 |
| `model/` | Cryptol models |
| `proof/` | SAW scripts (`proof/hqc/` for HQC, generated by `gen_hqc.py`) |
| `spec/` | Isabelle specs and proofs |
| `implementations/` | RustCrypto `ml-dsa` (MIR) |
| `qseal/`, `cap/`, `cve-anchor/` | Protocol, capability and CVE work |
| `docs/` | [Roadmap](docs/ROADMAP.md), [assumptions](docs/ASSUMPTIONS.md), [pipeline](docs/PIPELINE.md), writeups |

## License

Project code: [MIT](LICENSE). The vendored C in `target/` is PQClean/pq-crystals reference code
(CC0) and the HQC reference code (public domain, `target/hqc/LICENSE`); see
[`target/README.md`](target/README.md).
