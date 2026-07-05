# Verifying an eSIM attestation, from the ML-DSA arithmetic up

*Amar Akshat &middot; [github.com/amarshat](https://github.com/amarshat)*

Post-quantum signatures are going into secure elements before the implementations have settled. A
one-character change in a deployed ML-DSA crate's hint decoder, `<` to `<=`, made it accept non-canonical
signatures. It passed the test vectors and became CVE-2026-24850. That is the gap between "tested" and
"correct on all inputs", and it is why we check the code against the spec instead of trusting the
vectors.

We are building Q-SEAL, an eSIM attestation layer: a key inside the secure element signs a
challenge-bound statement, and the suite is hybrid, ECDSA P-256 and ML-DSA-44, both required. The point
of this post is that more of the path is checked than just the signature primitive. Everything below is
in the [repository](https://github.com/amarshat/pqc-assay) and reproduces from a `make` target.

## What is proved

The ML-DSA reference C (PQClean, unmodified) computes the FIPS 204 forward and inverse NTT. The proof
runs from the C through SAW to a Cryptol model, then cryptol-to-isabelle lifts that model into Isabelle,
and Isabelle shows the lifted model equals the FIPS 204 transform. No `sorry`, `oops`, or admit in the
transform theorems. It is the toolchain Apple used on corecrypto, pointed at the reference C that
everyone else derives their understanding from rather than at our own code.

On top of that, four Q-SEAL protocol properties, each verifying in about a second:

| Property | Command | Time |
|---|---|---|
| The 231-byte transcript serializer is a bijection | `make qseal-tbs` | 0.4 s |
| The C (de)serializer matches that model, field for field | `make qseal-ref` | 1.9 s |
| The assertion binds the verifier's challenge, and the applet fills its own identity fields | `make qseal-assert` | 0.7 s |
| Acceptance requires both signatures over the same bytes | `make qseal-hybrid` | 0.9 s |

Two of these are worth a sentence. The transcript is fixed-length with no optional fields, and the proof
is that its serializer is injective: two different transcripts can never produce the same bytes. That is
an analogous property, one layer up from where CVE-2026-24850 lived. For the hybrid check, the two
signature verifiers are left uninterpreted, and the accept logic is proved equal to "both verify, over
the same transcript". A variant that accepts on either signature fails the same proof, so the hybrid
cannot quietly degrade to classical-only. That last one, verbatim from `make qseal-hybrid`:

```
Proof succeeded! qseal_hybrid_accept
VERIFIED: qseal_hybrid_accept == vE(pk_c,tbs,sig_c) AND vM(pk_pq,tbs,sig_pq) -- both required, same transcript
MUTATION CAUGHT: the downgrade variant (accept on either signature) is REJECTED by the both-required spec
```

## What I am not claiming

The inverse NTT equivalence is proved under a non-negative input window, coefficients in `[0, Q)`, which
does not cover the signed, centered coefficients the reference actually feeds it. Extending that is open.
The hybrid proof abstracts the verifiers, so it is about the acceptance logic, not whether ECDSA or
ML-DSA verification is itself correct; and "the applet fills its own identity" is a data-flow property
that assumes the runtime hands the applet an identity the host cannot set. The Rust crate's hint decoder,
where the CVE lived, is outside the verified set because of a tool limit on how it slices memory; that
path is covered by tests, not a proof, and the repo says so. One step in the ML-DSA chain, that the
`-fwrapv` build has no signed-overflow undefined behavior, is argued from a machine-checked bound rather
than mechanized as one theorem.

Everything above reproduces from a `make` target. The transcript proofs are kept honest by their
injectivity and binding properties; the hybrid proof carries an injected downgrade variant that it
rejects. The primitive chain has 341 Isabelle lemmas (most are supporting lemmas), 12 SAW proofs on the
C, and 37 on the Rust.

## Try it

The runnable demo needs only Rust, no proof toolchain. It signs the verified transcript with real ECDSA
P-256 and ML-DSA-44 and shows a valid attestation accept, a tampered one reject, and a downgrade (valid
classical signature, no valid post-quantum one) reject:

    git clone https://github.com/amarshat/pqc-assay
    cd pqc-assay/qseal/demo
    cargo run

The proofs reproduce from make targets (`make qseal-tbs qseal-ref qseal-assert qseal-hybrid`, a few
seconds each, need cryptol and SAW). The ML-DSA primitive chain (`make verify`) needs the pinned
SAW + Isabelle toolchain; see the repo's setup script.
