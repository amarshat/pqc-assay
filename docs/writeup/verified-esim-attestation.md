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

On top of that, six of the seven protocol properties in the spec's verification-targets list. Each is a
Cryptol model of a spec rule, a C reference written to be verifiable, and a SAW proof that the C equals
the model. Each also carries an injected mutant that the proof rejects, a sensitivity check that the
proof depends on the clause it is meant to check. Each runs in a second or two:

| Property | Command | Time |
|---|---|---|
| The 231-byte transcript serializer is a bijection (no malleability) | `make qseal-tbs` | 0.4 s |
| The C (de)serializer matches that model, field for field | `make qseal-ref` | 1.6 s |
| The assertion binds the verifier's challenge; the applet fills its own identity | `make qseal-assert` | 0.5 s |
| Acceptance requires both signatures over the same bytes (no downgrade) | `make qseal-hybrid` | 0.7 s |
| A consumed request_id is not accepted twice, in the sequential case | `make qseal-nonce` | 1.6 s |
| Field values outside the spec enumerations are rejected before signing | `make qseal-validate` | 1.0 s |
| Fragmented evidence reassembles to the exact bytes or fails closed | `make qseal-evidence` | 2.0 s |

A few are worth a sentence. The transcript is fixed-length with no optional fields, and the proof is
that its serializer is injective: two different transcripts can never produce the same bytes. That is an
analogous property, one layer up from where CVE-2026-24850 lived. The hybrid check leaves the two
signature verifiers uninterpreted and proves the accept logic equal to "both verify, over the same
transcript"; a variant that accepts on either signature fails the same proof, so the hybrid cannot
quietly degrade to classical-only. The single-use proof is the first stateful one: a request whose
request_id was already consumed is rejected, and a verifier that drops the consume step is shown to
accept the same request twice. The evidence proof is a round-trip: splitting a blob into response
fragments and reassembling recovers exactly the original bytes, while a dropped fragment fails closed
rather than being silently zero-filled. The hybrid one, verbatim from `make qseal-hybrid`:

```
Proof succeeded! qseal_hybrid_accept
VERIFIED: qseal_hybrid_accept == vE(pk_c,tbs,sig_c) AND vM(pk_pq,tbs,sig_pq) -- both required, same transcript
MUTATION CAUGHT: the downgrade variant (accept on either signature) is REJECTED by the both-required spec
```

## What I am not claiming

These are scoped results, and the scope matters more than the count.

The inverse NTT equivalence is proved under a non-negative input window, coefficients in `[0, Q)`, which
does not cover the signed, centered coefficients the reference actually feeds it. Extending that is open.
The hybrid proof abstracts the verifiers, so it is about the acceptance logic, not whether ECDSA or
ML-DSA verification is itself correct. One step in the ML-DSA chain, that the `-fwrapv` build has no
signed-overflow undefined behavior, is argued from a machine-checked bound rather than mechanized as one
theorem.

On the protocol side: the single-use proof is safety only (no double-accept), on a fixed, small store
that fails closed when full and has no expiry-based eviction, and it is the sequential case, so the
check-and-consume race under concurrency is assumed away, not verified. The validation proof rejects
out-of-enumeration field *values*; it does not cover length parsing of the incoming APDU (that is
upstream of the typed request it starts from), cross-field constraints, or authorization, so a
profile-observed assertion type under a host-asserted origin still passes it (which path can reach which
type is the one property still open). The evidence proof is the byte-level reassembly identity, not the
APDU transport state machine and not the evidence content (that the reassembled transcript and
signatures are the ones the applet signed is the binding and hybrid properties, not re-checked there).
The mutants above are hand-injected, not bugs found in the wild, so catching them shows sensitivity to
one clause, not adequacy. To measure adequacy I ran a systematic pass (`make qseal-mutants`): apply the
CVE's operator class (`<` vs `<=`, `==` vs `!=`, `&&` vs `||`, and so on) to each C reference, one
mutation at a time, and rerun the matching proof. The proofs kill 38 of 40 such mutants; the two
survivors are equivalent mutants (a loop bound whose extra iteration a downstream guard makes a no-op),
so no proof or test could kill them. And the C references are written to be verifiable; the shipped Rust
deserializer, where the CVE lived, is outside the verified set because of a tool limit on how it slices
memory, so that path is covered by tests, not a proof, and the repo says so.

Everything above reproduces from a `make` target. The primitive chain has 341 Isabelle lemmas (most are
supporting lemmas), 12 SAW proofs on the C, and 37 on the Rust.

## Try it

The runnable demo needs only Rust, no proof toolchain. It signs the verified transcript with real ECDSA
P-256 and ML-DSA-44 and walks six outcomes: a valid attestation accepts; a tampered transcript rejects;
a downgrade (valid classical signature, no valid post-quantum one) rejects; a replayed request rejects;
a malformed request is refused before signing; and fragmented evidence reassembles exactly, while a
dropped fragment is rejected. The demo binary is not itself verified; each piece is a Rust twin of a
rule proved in the SAW scripts.

    git clone https://github.com/amarshat/pqc-assay
    cd pqc-assay/qseal/demo
    cargo run

The proofs reproduce from make targets
(`make qseal-tbs qseal-ref qseal-assert qseal-hybrid qseal-nonce qseal-validate qseal-evidence`, a second
or two each, need cryptol and SAW). The ML-DSA primitive chain (`make verify`) needs the pinned
SAW + Isabelle toolchain; see the repo's setup script.
