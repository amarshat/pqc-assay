# Why this project exists

Post-quantum cryptography is being deployed now, while the implementations are still young. The
security argument for every scheme assumes the code computes the function the standard defines. Test
vectors check that on a fixed set of inputs. They do not check it for all inputs, and that gap is where
real bugs live.

The gap is not hypothetical. A one-character regression in a deployed ML-DSA crate's hint decoder (`<`
became `<=`) accepted non-canonical signatures and passed test vectors; it was assigned CVE-2026-24850.
Reduction-placement and overflow defects of the same "passes test vectors" kind have been reported in
production ML-DSA (eprint 2026/1032). These are the failures a proof of conformance to the
specification catches and a test suite does not.

## Why HQC

NIST selected HQC in March 2025 as a second key-encapsulation standard beside ML-KEM. The two rest on
different problems (decoding random quasi-cyclic codes, and module lattices), and the stated reason for
the second is that a KEM stays standardized if lattice cryptanalysis advances. HQC is the fallback for
everything that deploys ML-KEM.

A fallback is used after the primary has failed, possibly at short notice, with no time to audit it
then. Its implementations have to be trusted before that day, not on it. Verification effort so far has
gone almost entirely to the primary: corecrypto, mlkem-native, libcrux and the CryptoLine and Jasmin
work all verify lattice arithmetic. For HQC the closest work verifies assembly for the additive FFT
in its decoder (Liu et al., 2026); we found no proof of its polynomial multiplication.

We start with polynomial multiplication in GF(2)[x]/(x^n - 1) because it is the right first target on
three counts. Key generation, encapsulation and decapsulation all perform it, and it takes much of their
time. It is the part implementations rewrite for speed: the reference uses recursive Karatsuba, the AVX2
code Toom-Cook-3 over multi-way Karatsuba over `pclmulqdq`, and the newest proposal an additive FFT over
GF(2^64). And all of those have one short specification, the ring product, which does not depend on the
rest of the scheme, so one Isabelle statement covers every implementation.

The optimized versions are also the ones that are hard to check by reading, and the proof attempts bore
that out: SAW found an out-of-bounds read in the shipped AVX2 multiplier (OF-5, confirmed by the
maintainers) and out-of-bounds pointer arithmetic in the additive-FFT decoder (A-HQC-FFT item 7),
neither of which the known-answer tests or AddressSanitizer report. The three multipliers are now
proved to compute (a * b) mod (x^n - 1) at all three parameter sets (README, "Proved (HQC)").

## Where it started

The project began with ML-DSA (FIPS 204): the unmodified PQClean / pq-crystals reference C and the
RustCrypto `ml-dsa` crate, through a SAW -> Cryptol -> Isabelle refinement, up to an Isabelle
transcription of FIPS 204 written from the standard, with no vendor verification artifacts used. The
motivation there is applied: these implementations are the trust base for hardware-rooted, quantum-safe
proof of possession (secure-element and eSIM attestation, credential enrollment, key binding), and a
relying party that trusts such an assertion trusts, transitively, that the ML-DSA code computes the
specified function. The HQC work uses the same method and the same rule: a result counts only when the
tool that checks it exits 0.

See the [README](README.md) for scope, the claim tables, and how to reproduce the proofs.
