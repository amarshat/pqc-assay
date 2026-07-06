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

**A consumed request_id is not accepted twice, in the sequential case (property 4 of section 16).**
This is the first *stateful* property: acceptance depends on what the verifier has already consumed, not
just on one transcript. The spec's accept rule ends with `consume_nonce_once(request_id)` and the
verifier MUST reject "a request whose ... request ID has already been consumed". `model/QSEAL_Nonce.cry`
models the signature/policy checks as one abstract bit `ok` (that is property 3, kept opaque) and models
`consume_nonce_once` as a bounded single-use store. The result with content is `no_replay`: if a
validated request is accepted and consumed, replaying the exact same request against the resulting store
is rejected. It reduces to `consume_marks_seen` (appending at index `count` and scanning `i < count`
actually records the id, with the `>= CAP` boundary keeping the index in range), so the proof exercises
the store's index arithmetic and would catch an off-by-one there. (`consumed_never_accepts` is also
proved but is a restatement of the accept definition, not independent content.)

`ref/nonce.c` is the C reference store, and `proof/nonce.saw` proves `qseal_nonce_accept` equals the
Cryptol model (it returns the accept bit and advances the store to the model's next state), memory-safe,
with no uninterpreted functions or assumed overrides. An injected mutant `qseal_nonce_accept_noconsume`
(returns the same bit but never records the id) is shown to *fail* that spec: a non-vacuity check that
the proof depends on the consume step, not a bug found in the wild. The demo (`demo/`) carries an
illustrative in-memory store and rejects a replayed valid attestation.

Scope, and what this does NOT prove:
- **Safety only.** The theorem is "no double-accept." Liveness is not modeled: `accept` requires
  `~full`, and there is no eviction, so the verified store accepts the first `CAP` (=8, fixed) distinct
  ids and then rejects everything. That is fail-closed but also a denial-of-service footgun; the spec's
  real retention mechanism is expiry (section 10), which is out of scope here. "Independent of CAP"
  applies to safety only.
- **Sequential/atomic only.** `step` does seen-check-then-consume in one step. The real replay risk is
  the TOCTOU window between verifying and consuming under concurrency; two simultaneous submissions of
  the same id both seeing `fresh` is not expressible in this model. Atomic check-and-consume is assumed.
- **Keyed on `verifier_id ‖ request_id`** (32 bytes), so the store is per-verifier as the spec requires
  (`request_id` is unique per verifier). An earlier request_id-only key would let one verifier's request
  block another's, a cross-verifier denial of service; that is fixed. The nonce is still not part of the
  key (the spec's full key is `(request_id, nonce)`).
- Signature/policy correctness is the abstract `ok` bit (that is property 3).

**Field values outside the spec enumerations fail before signing (part of property 7 of section 16).**
Section 11.2 requires the applet to validate the requested suite and assertion type and reject
unsupported origins before it builds and signs a transcript. `model/QSEAL_Validate.cry` models a
well-formedness gate `valid` over the spec enumerations (version `0x01`, suite `0x0001` = HYB-1,
assertion_type `0x01..0x06`, assertion_origin `0x01..0x03`, object_hash_algorithm `0x01` = SHA-256), and
`create_checked` = validate-then-sign-else-zero.

The real result here is the SAW one: `proof/validate.saw` proves `qseal_validate_request` equals `valid`
and `qseal_create_assertion_checked` equals `create_checked` (on a valid request the C signs and returns
1; on an invalid one it zeroes the buffer and returns 0), memory-safe, no assumed overrides. An injected
mutant `qseal_create_assertion_checked_nosuitecheck` (drops the suite check) is shown to *fail* that
spec: a non-vacuity check, not bug discovery. (The two model-level lemmas `malformed_never_signs` and
`signed_is_validated` are proved but are definitional consequences of how `create_checked` is written,
so they carry no content beyond the SAW equivalence; do not read them as substantive theorems.) The demo
(`demo/`) refuses a bad-suite request before signing.

Scope, and what this does NOT prove. This is a field-*value* gate only. It does not cover:
- **Length.** Property 7 and 11.2 step 1 ("validate all field lengths") are about the incoming
  APDU/wire encoding, upstream of the typed `qseal_request_t` this gate starts from. That parse is not
  modeled or verified. The fixed-format transcript (property 1) is downstream of a struct we already
  hold; it is not the length validation the spec means.
- **Cross-field and semantic constraints**, e.g. an object_length that disagrees with the digest, or an
  expiry in the past.

The gate does now enforce one authorization rule: it rejects assertion_type `0x04`
(`PROFILE_ACTION_OBSERVED`), which section 8.4 says must not be host-callable. `proof/validate.saw`
carries a second mutant, `qseal_create_assertion_checked_allowobserved`, that drops that rejection and is
shown to *fail* the spec. This is the code-level counterpart of the ProVerif guard in property 5 (the
host path refuses `0x04`); the two meet at that guard, though there is no shared model linking them. The
rest of the reachability question (which command paths can reach which types) is property 5's model.

**Evidence reassembly recovers the exact bytes or fails closed (property 6 of section 16).**
`READ_EVIDENCE` (section 11.3) returns the evidence blob as response fragments (APDU chaining) that the
host reassembles. `model/QSEAL_Evidence.cry` models the split into fragments (each tagged with its index
and the total count) and the reassembly, and proves with `cryptol` and z3:

- `reassemble_round_trip`: splitting a blob and reassembling recovers exactly the blob. This is the
  substantive result, a structural identity over the split/placement index arithmetic (chunk `i` lands
  back at output index `i`), in the same style as the property-1 transcript bijection.
- `dropped_fragment_rejected`: if two received fragments carry the same index then, by pigeonhole, some
  index is missing, and reassembly rejects rather than zero-filling the gap.
- `wrong_total_rejected`: any fragment reporting the wrong total count is rejected.

`ref/evidence.c` is the C reference, and `proof/evidence.saw` proves `qseal_evidence_reassemble` equals
the model (return bit plus the reassembled bytes; zeroed and rejected when the set is not well formed),
memory-safe, no assumed overrides. An injected mutant `qseal_evidence_reassemble_nocomplete` (drops the
completeness check and zero-fills a missing fragment) is shown to *fail* that spec, so the proof catches
a reassembler that would emit corrupted bytes under an "ok" result. The demo (`demo/`) recovers a
complete set and rejects a dropped fragment.

Scope: fragment size and count are fixed and small (32 bytes x 4 = 128) so the goals stay bounded; the
reassembly logic (index permutation plus placement) is independent of them. This is the byte-level
reassembly identity, not the APDU chaining/transport state machine, and not the evidence *content*: that
the reassembled `tbs`/signatures are the ones the applet signed is properties 2 and 3, not re-checked
here.

**PROFILE_ACTION_OBSERVED is not reachable through a host-exposed APDU path (property 5 of section 16).**
This is a reachability question over the command surface, not a fixed-format identity, so it is checked
in ProVerif (symbolic / Dolev-Yao) rather than the SAW/Cryptol pipeline. `proof/proverif/property5.pv`
models the host APDU channel as attacker-controlled and the internal eUICC event callback as a private
channel, and proves the correspondence `event(Signed(OBSERVED)) ==> event(InternalFired())`: any signing
of a `PROFILE_ACTION_OBSERVED` (type `0x04`) assertion is preceded by the trusted internal callback. The
host-callable path signs only `if t <> OBSERVED` (spec 8.4). `property5_mutant.pv` drops that guard, and
ProVerif reports the same query *false*, finding a trace where the attacker obtains an OBSERVED assertion
through the host path. `verify_reachability.sh` runs both and exits 0 only if the good model proves the
query and the mutant refutes it.

Scope: this is a symbolic model of the command surface, with no C == model link (unlike the SAW
properties). "Host-exposed" is a public channel and the trusted callback a private one; the model
abstracts the applet to the assertion-type dispatch. The guard it proves necessary (the host path must
refuse type `0x04`) is now also enforced in the verified C: property 7's `qseal_validate_request` rejects
`0x04`, with a mutant that allows it caught in `proof/validate.saw`. So the reachability argument and the
code-level check meet at that guard (there is no shared model tying them together). Details in
[`proof/proverif/README.md`](proof/proverif/README.md).

## Mutation adequacy

Each proof above carries one hand-injected mutant, which shows the proof is sensitive to that one
clause. To measure adequacy rather than sensitivity, `mutation/mutate.py` applies a relational/logical
operator set (the class CVE-2026-24850 lived in: `<`/`<=`, `==`/`!=`, `&&`/`||`, and so on) to each C
reference systematically, one mutation per occurrence, and reruns the matching SAW proof. Across the six
references, the proofs kill **39 of 41** such mutants. The two survivors are the same shape, a loop bound
`i < CAP` weakened to `i <= CAP`, and are semantically equivalent mutants: a downstream guard makes the
extra iteration a no-op, so no proof or test could kill them. There are no adequacy gaps in this operator
set. Details in [`mutation/README.md`](mutation/README.md); run with `make qseal-mutants`.

## Reproduce

    ./verify_tbs.sh        # cryptol + z3: the model is bijective/injective (3 properties Q.E.D.)
    ./verify_ref.sh        # clang + SAW: the C reference (de)serializer == the Cryptol model
    ./verify_assertion.sh  # cryptol + SAW: CREATE_ASSERTION binds the validated challenge
    ./verify_hybrid.sh     # SAW: hybrid accept requires BOTH signatures; downgrade variant caught
    ./verify_nonce.sh      # cryptol + SAW: consumed request_id can't be accepted twice; no-consume bug caught
    ./verify_validate.sh   # cryptol + SAW: a malformed request fails before signing; no-suite-check bug caught
    ./verify_evidence.sh     # cryptol + SAW: evidence reassembly round-trips or fails closed; no-completeness bug caught
    ./verify_reachability.sh # ProVerif: OBSERVED reachable only via the internal callback; host-path mutant refuted

All exit non-zero on failure. `verify_tbs.sh` needs `cryptol`; the SAW ones need `clang` + `saw`;
`verify_reachability.sh` needs `proverif` (all findable in `../.tools/bin`). Also wired as `make qseal-tbs`,
`make qseal-ref`, `make qseal-assert`, `make qseal-hybrid`, `make qseal-nonce`, `make qseal-validate`,
`make qseal-evidence`, `make qseal-reachability`.

## Section 16 coverage

All seven verification targets are now machine-checked: 1-4, 6, 7 as SAW proofs that a C reference equals
a Cryptol model of the spec rule (each with an injected-mutant non-vacuity check and a 39/41
mutation-adequacy pass, see above), and 5 as a ProVerif reachability result. Properties 1-4/6/7 are
code-level (a C reference is verified); property 5 is a symbolic protocol model with no C link, and the
scope note under each property states what it does and does not establish. A shipped Rust
(de)serializer cannot be verified directly here (a crucible-mir limitation on slice access), which is why
the code-level work is done against C references written to be verifiable.
