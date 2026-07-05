# Why this project exists

Post-quantum signatures are being deployed now. ML-DSA (FIPS 204) is going into TLS stacks, secure
elements, and credential systems while the reference and library implementations are still young. The
security argument for these schemes assumes the code computes the function the standard defines. Test
vectors check that on a fixed set of inputs. They do not check it for all inputs, and that gap is where
real bugs live.

The gap is not hypothetical. A one-character regression in a deployed ML-DSA crate's hint decoder (`<`
became `<=`) accepted non-canonical signatures and passed test vectors; it was assigned CVE-2026-24850.
Reduction-placement and overflow defects of the same "passes test vectors" kind have been reported in
production ML-DSA (eprint 2026/1032). These are the failures a conformance-to-specification proof catches
and a test suite does not.

This project machine-checks that deployed ML-DSA implementations compute the FIPS 204 function: the
unmodified PQClean / pq-crystals reference C, and the RustCrypto `ml-dsa` crate, through a
SAW -> Cryptol -> Isabelle refinement, up to an Isabelle transcription of FIPS 204. No vendor
verification artifacts are used; the Isabelle specification is written from the standard.

The motivation is applied. These implementations are the trust base for hardware-rooted, quantum-safe
proof of possession: secure-element and eSIM attestation, credential enrollment, and key binding. A
relying party that trusts such an assertion is trusting, transitively, that the ML-DSA implementation
underneath computes the specified function. If it does not, the quantum-safe half of that assurance is a
false floor. Verifying the primitive is the floor everything else stands on.

See the [README](README.md) for scope, the claim table, and how to reproduce the proofs.
