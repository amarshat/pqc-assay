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

PQC-Assay machine-checks the unmodified PQClean reference C for ML-DSA-44 (FIPS 204) against a
specification written from the standard. SAW proves the C equal to a Cryptol model, Galois's
`cryptol-to-isabelle` lifts that model into Isabelle, and Isabelle proves the lifted model equal to
the FIPS 204 mathematics. It is the toolchain Apple used for its 2026 `corecrypto` work; none of
Apple's code or theories are used here.

As of October 2026 the chain reaches from the C to ring arithmetic in `R_q = Z_q[X]/(X^256+1)`: the
forward and inverse NTT compute the FIPS 204 transforms, the NTT-based multiply computes the product
in `R_q`, and a row of the signer's `A*y` and of verification's `A*z - c*t1*2^13` computes the sum of
products FIPS 204 specifies. This is reference C, not the optimized code that ships, and it is the
arithmetic core of the scheme, not the scheme. Writeup:
[The ML-DSA reference NTT multiplies polynomials, checked from the C](https://amarshat.github.io/pqc-assay/writeup/ml-dsa-ntt-multiplies.html).

## What is proven (ML-DSA-44)

"Machine-checked" means a pinned tool exited 0 on the stated property, in `make verify` unless noted.
"Argued" means a sound step that is not mechanized. Details and every assumption are in
[`docs/ASSUMPTIONS.md`](docs/ASSUMPTIONS.md).

| Link | Status |
|---|---|
| `reduce.c` (`montgomery_reduce`, `reduce32`, `caddq`, `freeze`) ≡ Cryptol, no signed overflow in range | machine-checked (SAW + z3) |
| `reduce.c` models meet their contracts (residue mod q, output windows) | machine-checked (Isabelle) |
| C `ntt` and `invntt_tomont` ≡ Cryptol models (`-fwrapv` build, all inputs) | machine-checked (SAW) |
| Cryptol models lift to the Isabelle models used below | machine-checked (`make lift-check` regenerates and diffs) |
| forward NTT model ≡ FIPS 204 forward NTT mod q | machine-checked (Isabelle `ntt_bridge` on `[0,q)`, `ntt_signed_correct` on `\|coeff\| < q`) |
| inverse NTT model ≡ FIPS 204 inverse NTT mod q, scaled by `mont/256` (`mont` = 2³² mod q) | machine-checked (Isabelle `invntt_bridge` on `[0,q)`, `invntt_signed_correct` on `\|coeff\| < q`) |
| no int32 overflow in the NTT models (forward on `±(2³¹−2²⁷)`, inverse on `\|coeff\| < q`) | machine-checked (Isabelle `ntt_overflow_free`, `invntt_overflow_free`) |
| forward NTT on the default build: no signed-overflow UB, and ≡ model, on `±(2³¹−2²⁷)` | machine-checked once (SAW + bitwuzla, `make ntt-nsw`, 12.5 h, 2026-07-10, before `poly.c` was vendored; no paired mutant; out of band) |
| inverse NTT on the default build: no signed-overflow UB | argued (from the `-fwrapv` proof plus `invntt_overflow_free`) |
| `invntt(pointwise(ntt a, ntt b))` is `a*b` in `R_q`, for `\|coeff\| < q` inputs | machine-checked (SAW for `poly_pointwise_montgomery`, Isabelle `ntt_mult_correct`, `ntt_mult_ring`) |
| a row of `A*y` / `A*s1` is `sum_i f_i*y_i` in `R_q` (`f_i` any polynomial whose NTT is row entry i of `A_hat`; `\|y\| < q`) | machine-checked (SAW for the accumulator, `poly_add`, `poly_reduce`, the wrappers and loops; Isabelle `acc_mult_fips`, `acc_mult_ring`) |
| a row of verification's `A*z - c*t1*2^13`, FIPS form and in `R_q` | machine-checked (Isabelle `ver_row_fips`, `ver_row_ring`) |
| pointwise, add, sub, reduce, accumulator and the loops on the multiply paths: no signed-overflow UB on the default build, given pointwise operands within 9q (= 75423752) | machine-checked (SAW + z3, `make poly-nsw`, 48 min on CI's clang 17) |
| `poly_shiftl` on the default build: no signed-shift UB | argued (clang emits a plain `shl`, so SAW cannot see it; `poly_nsw.saw` checks the range fact only) |
| transform wrappers `poly_ntt` / `poly_invntt_tomont` on the default build | argued |
| `negconv` is multiplication in `R_q`; the NTT locale has a model at the ML-DSA parameters | machine-checked (Isabelle `negconv_is_mult`, `mldsa_model`) |
| hypotheses read from the source: the order `sign.c` / `verify` call these in; A's 23-bit coefficient bound; verification's `t1` (10-bit), `\|z\|` and `\|c\|` below q | not proven (A-ROW 2, 5 in `docs/ASSUMPTIONS.md`) |
| sampling, rounding, hints, packing, hashing; constant time | not claimed |

The 9q operand bound comes from Isabelle's `ntt_out_bounded` for transform outputs and from the
23-bit mask in `poly_uniform` for A (read from the source). The Isabelle theories contain no `sorry`,
`oops` or `smt`, and CI greps for `sorry`/`oops`/`admit` on every push. They use `by eval`, which
trusts the code generator, 88 times (85 in `make verify`), for the twiddle tables and a few gcd
facts. Every NTT theorem in the table depends on it (OF-4, measured with `Thm_Deps.all_oracles`);
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
make claim-lint                      # SAW specs have paired mutants (exemptions printed); cited paths exist
```

The full `make verify` took 3 h 20 min in `verify.yml` run 38100891287 on 2026-10-11 (macos-15
runner, Apple clang 17.0.0, manual dispatch); the workflow caches Isabelle heaps, so warm runs are
shorter. `make ntt-nsw` and `make barrett-solver` are out of band, and `ntt-nsw` needs macOS 15 (the
pinned bitwuzla does not load on 13).

## Layout

| Path | What |
|------|------|
| `target/` | Vendored C, pinned (`target/README.md`) |
| `model/` | Cryptol models |
| `proof/` | SAW scripts |
| `spec/` | Isabelle specs and proofs |
| `implementations/` | RustCrypto `ml-dsa` (MIR) |
| `qseal/`, `cap/`, `cve-anchor/` | Protocol, capability and CVE work |
| `docs/` | [Roadmap](docs/ROADMAP.md), [assumptions](docs/ASSUMPTIONS.md), [pipeline](docs/PIPELINE.md), writeups |

## License

Project code: [MIT](LICENSE). The vendored C in `target/` is PQClean/pq-crystals reference code
(CC0; see [`target/README.md`](target/README.md)).
