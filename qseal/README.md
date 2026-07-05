# Q-SEAL protocol verification

Q-SEAL is a hybrid, quantum-safe secure-element attestation layer: a non-exportable key inside an eUICC
or secure element signs a canonical, challenge-bound statement, giving hardware-rooted proof of
possession. Its mandatory suite HYB-1 pairs ECDSA P-256 with ML-DSA-44 and requires both signatures.
Full spec: [`../docs/qseal/QSEAL-v0.1.md`](../docs/qseal/QSEAL-v0.1.md).

The rest of PQC-Assay verifies the ML-DSA-44 *primitive* Q-SEAL relies on (see the repo README). This
directory verifies Q-SEAL *protocol* properties, starting with the ones that do not depend on the
signature primitive at all. The target list is section 16 of the spec.

## Verified so far

**TBS-V1 transcript is a bijection (property 1 of section 16).** The signed transcript is fixed-length
(231 bytes) with no optional fields or variable encodings. `model/QSEAL_TBS.cry` models the layout and
proves, with `cryptol` and z3:

- `roundtrip_parse_serialize`: `parse (serialize t) == t` for every transcript `t`.
- `roundtrip_serialize_parse`: every well-formed byte string equals `serialize (parse b)`.
- `serialize_injective`: distinct transcripts never serialize to the same bytes.

Injectivity is the property the hint decoder in CVE-2026-24850 lacked: there, a non-fixed,
validation-dependent decode admitted non-canonical inputs (repeated hint indices), which is malleability.
A fixed-length, no-optional-fields transcript removes that class of bug by construction, and the proof
here is the machine-checked statement of it. A mutation check (a deliberately wrong field offset) is
rejected with a counterexample, so the proofs are not vacuous.

**C reference (de)serializer matches the model.** `ref/tbs_v1.c` is a reference implementation written
to be verifiable (fixed offsets, constant-size copies, no slicing). SAW proves, on its LLVM bitcode:

- `qseal_tbs_serialize` equals the Cryptol `serialize` (every field lands at its FIPS-spec offset).
- `qseal_tbs_parse` equals the Cryptol `parse` on well-formed input (returns 1, fills the struct).

Composed with the model bijectivity above, the C pair round-trips. This is the first rung toward a
verifiable Q-SEAL applet: real code checked against the transcript spec, not a test suite.

**CREATE_ASSERTION binds the validated challenge (property 2 of section 16).** The applet builds TBS-V1
internally from the host's request fields plus its own identity fields, then serializes (section 11.2:
"the handset MUST NOT supply an already-encoded transcript"). `model/QSEAL_Assertion.cry` models this as
`create r a = serialize (build r a)` and proves:

- `binds_challenge`: what the verifier parses back for verifier_id, nonce, request_id, suite_id,
  policy_id, assertion_type, expiry, and the object digests is exactly the request. The applet cannot
  emit a transcript that differs on these.
- `applet_controls_identity`: the issuer_id, ak_id, and version come from the applet, not the request,
  so a malicious host cannot forge the claimed issuer, attestation key, or protocol version.

`ref/assertion.c` is the C reference, and `proof/assertion.saw` proves `qseal_create_assertion` equals
the Cryptol `create`. A mutation (mis-wiring verifier_id from the applet's issuer_id) is rejected with a
counterexample. So the code-level statement of "the signed transcript binds the request" holds.

**Hybrid acceptance requires both signatures, no downgrade (property 3 of section 16).** HYB-1 pairs
ECDSA P-256 with ML-DSA-44 and the verifier must require both; accepting on either alone is a silent
downgrade to classical-only, i.e. quantum-vulnerable. With the two signature verifiers kept
*uninterpreted* (`model/QSEAL_Verify.cry` `vE`, `vM`), SAW proves `ref/hybrid.c`'s `qseal_hybrid_accept`
equals `vE(pk_c, tbs, sig_c) AND vM(pk_pq, tbs, sig_pq)` over the *same* transcript, so acceptance
requires both signatures over identical bytes for *any* real verifiers. Then a downgrade variant
(`qseal_hybrid_accept_downgrade`, accept-on-either) is shown to *fail* that spec, so the proof catches
the downgrade. Scope: verifiers are abstract, so this is a statement about the acceptance *structure*
(both required, same bytes), not about ECDSA/ML-DSA correctness.

## Reproduce

    ./verify_tbs.sh        # cryptol + z3: the model is bijective/injective (3 properties Q.E.D.)
    ./verify_ref.sh        # clang + SAW: the C reference (de)serializer == the Cryptol model
    ./verify_assertion.sh  # cryptol + SAW: CREATE_ASSERTION binds the validated challenge
    ./verify_hybrid.sh     # SAW: hybrid accept requires BOTH signatures; downgrade variant caught

All exit non-zero on failure. `verify_tbs.sh` needs `cryptol`; the others need `clang` + `saw` (or the
pinned `../.tools/bin`). Also wired as `make qseal-tbs`, `make qseal-ref`, `make qseal-assert`,
`make qseal-hybrid`.

## Not yet done (section 16 remainder)

Properties 2-7 (transcript binding to the validated request, hybrid acceptance over identical bytes,
challenge single-use, `PROFILE_ACTION_OBSERVED` reachability, evidence reassembly fail-closed, malformed
input rejected before signing) are protocol-logic and state-machine properties, not fixed-format
identities. They need a protocol model, and some are a better fit for a protocol prover (Tamarin,
ProVerif) than for the SAW/Cryptol/Isabelle pipeline. Verifying a shipped Rust (de)serializer directly is
known to hit a crucible-mir limitation on slice access, which is why the transcript work is done at the
model level here.
