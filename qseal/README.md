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

**TBS-V2 (v0.2 draft): hybrid pair binding, same properties plus commitment signedness.** From public
review of v0.1 (hybrid non-separability: neither component signature commits to the other key's
material, pair binding rests on the certificate layer). `model/QSEAL_TBS_V2.cry` models TBS-V2 (263
bytes: V1 plus a 32-byte `pair_commitment`, SHA-256 over a domain prefix and both encoded public keys,
directly after `ak_id`) and proves the same three properties plus: `commitment_is_signed` (transcripts
differing only in the commitment never share bytes, so each component signature commits to the exact
pair) and `omitting_commitment_breaks_binding` (a serializer that dropped the field is witnessed to
collide them). The hash itself and the verifier's recompute-and-compare check are out of scope of the
format proofs. All eight properties run in `make qseal-tbs`. Spec section 7.1. The V2 C reference is
verified below; the demo signs V2 with the reserved `ctx` and recomputes the commitment (scenario 7).
Still open on the verified-C side: the V2 validate/create path and the single-signing-call-site
statement (spec 6.1/7.1 key-usage rules are policy obligations, not format properties).

**C reference (de)serializers match the models.** `ref/tbs_v1.c` and `ref/tbs_v2.c` are reference
implementations written to be verifiable (fixed offsets, constant-size copies, no slicing). SAW
proves, on their LLVM bitcode (`proof/tbs_v1.saw`, `proof/tbs_v2.saw`):

- `qseal_tbs_serialize` equals the Cryptol `serialize` (every field lands at its FIPS-spec offset),
  and `qseal_tbs_v2_serialize` equals `serialize2` (including the signed `pair_commitment` at its
  spec offset).
- `qseal_tbs_parse` equals the Cryptol `parse` on well-formed input (returns 1, fills the struct);
  likewise `qseal_tbs_v2_parse` against `parse2`.
- both parsers **fail closed**: on input that does not carry the magic prefix they return 0 and leave
  the caller's struct exactly as they found it, with no partial decode of an unauthenticated buffer.
  This is the direction the attacker controls, and the accept obligation above says nothing about it: a
  parser that decoded first and checked the prefix afterwards would satisfy it. Mutants that drop the
  prefix check (`qseal_tbs_parse_nomagic`, `qseal_tbs_v2_parse_nomagic`) are rejected by the reject
  obligation.

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
the downgrade. A second mutant answers the fair objection that this is only `return ok_c && ok_pq`
restated: `qseal_hybrid_accept_othertbs` is also a conjunction requiring both signatures, but hands the
post-quantum verifier a different transcript, and it fails the spec too. The content beyond the C is
that both verifier calls are pinned to the *same* transcript term. That result depends on the tactic:
under plain `z3` the placeholder verifier bodies (constantly `False`) unfold and every acceptance term
collapses, so the obligation would hold for anything. `w4_unint_z3 ["vE","vM"]` is what makes it a
statement about structure. Scope: verifiers are abstract, so this is a statement about the acceptance *structure*
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

A second store fixes the availability half. `ref/nonce_exp.c` with `model/QSEAL_NonceExp.cry` records
each consumed key with the expiry of the transcript it came from and reuses slots whose expiry has
passed, which is the retention mechanism the spec names in section 10. Five model properties are proved
(`verify_nonce.sh`): windowed single use, that consuming marks the key live for the rest of its window,
that expiry restores room, that an expired transcript is never accepted, and that acceptance is
reachable. SAW proves `qseal_nonce_exp_accept` equals the model, and an evict-live variant that throws
out a slot still inside its window is rejected. The theorem is weaker on purpose: a key can be accepted
again after its own transcript expires, which is sound only because an expired transcript must be
rejected anyway, and that check is in the model as `now < req_exp`.

Scope, and what this does NOT prove:
- **The v0.1 store trades availability for safety.** Its theorem is "no double-accept". There is no
  eviction, so it accepts the first `CAP` (=8, fixed) distinct keys and then rejects everything. Since
  the key is host-supplied that is a denial of service anyone can trigger, and the safety proof says
  nothing about it. The expiring store above is the answer; the original is kept because the paper's
  results refer to it.
- **Nonce freshness is not established** by either store. Nothing ties the request's nonce to a
  challenge a verifier actually issued: the store answers "have I consumed this key", not "did I issue
  this nonce".
- **A power cycle resets both stores.** They are in RAM, the host is untrusted and the card is in the
  adversary's hands, so this is an adversary-triggerable replay window, not an unmodelled convenience.
  Persistent storage or a monotonic counter would be needed, and neither is modelled.
- **Sequential/atomic only.** `step` does seen-check-then-consume in one step. The real replay risk is
  the TOCTOU window between verifying and consuming under concurrency; two simultaneous submissions of
  the same id both seeing `fresh` is not expressible in this model. Atomic check-and-consume is assumed.
- **Keyed on `verifier_id ‖ request_id ‖ nonce`** (64 bytes), the exact challenge key the spec's
  `consume_challenge_once` rule is defined over (section 4). A `request_id` is unique per verifier, so the
  key is per-verifier and covers the request_id and the nonce together; model, C, and demo all use this
  key.
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


Arity, measured rather than asserted. The checked-in instance is 4 fragments of 32 bytes, and the same
C reference compiles at other sizes (`QSEAL_FRAG_SIZE` / `QSEAL_NUM_FRAGS` are overridable) with a
matching model and proof script generated by `proof/gen_evidence_instance.py`. Run one with
`make qseal-evidence-scale EVIDENCE_SCALE=255x4`. What the numbers say, on an Apple M2 Max with SAW
1.5.1 and z3:

| instance | total | result |
|----------|-------|--------|
| 4 fragments x 32 bytes | 128 B | discharges, about 2 s |
| 4 fragments x 255 bytes | 1020 B | discharges, 86 s |
| 8 fragments x 64 bytes | 512 B | no result within 600 s |
| 11 fragments x 224 bytes | 2464 B | no result within 900 s |

The wall is the fragment *count*, not the payload size: a 1020-byte blob in 4 fragments is fine while a
512-byte blob in 8 fragments is not. Restructuring the completeness check from a per-index count to a
one-pass bitmask (equivalent for a fixed NF-slot array) did not change that, so the cost is in the
placement reasoning over symbolic indices rather than in the counting. A deployed READ_EVIDENCE response
needs roughly ten fragments for a 2420-byte ML-DSA-44 signature alone, so **property 6 is a fixed-arity
result at four fragments**, and generalising it needs a different proof structure, not a bigger machine.

**PROFILE_ACTION_OBSERVED is not obtainable through a host-exposed APDU path (property 5 of section
16).** A safety property over the command surface, not a fixed-format identity, so it is checked in
ProVerif (Dolev-Yao) rather than the SAW/Cryptol pipeline. The model in `proof/proverif/property5.pv`
has a signing key, two transcript shapes so the assertion type is inside the signed bytes, a host
command handler that refuses type `0x04` (spec 8.4), a profile-event source, and a separate assertion
builder reachable only over a private callback channel. Three queries, all discharged:

1. every observed-action assertion the applet signs follows an internal event carrying the same data;
2. every observed-typed signature the **attacker** can hold followed such an event;
3. the applet signing key never reaches the attacker.

Two mutants and a witness gate it. Dropping the host-path guard breaks queries 1 and 2. A builder that
is correctly gated on the private channel but signs a handset-supplied subject leaves query 1 **true**
and breaks query 2, which is why query 2 exists. `property5_reachable.pv` checks the observed-action
event is reachable at all: without it every positive result above would hold vacuously, which is how an
earlier version of this model came to prove nothing (`docs/ASSUMPTIONS.md` OF-3). `verify_reachability.sh`
runs all four and gates on each outcome.

Scope, and it is worth reading before quoting this result. There is no C == model link for property 5,
unlike the SAW properties. The **injective** form of query 1 is not proved: once the two events are
emitted by separate processes, ProVerif's abstraction permits one private-channel message to be consumed
twice, so replay of one internal transition into several assertions is not ruled out. The earlier model
did prove injectivity, but only because both events were statements in the same process. A version with
real mutable profile state does not terminate (still generating rules after 10 minutes), so "a transition
occurred" is an assumption of the model rather than something it checks. The guard the model needs is
separately enforced in the verified C by property 7's `qseal_validate_request`, with a mutant that allows
`0x04` caught in `proof/validate.saw`; the two meet at that guard with no shared model tying them
together. Details in [`proof/proverif/README.md`](proof/proverif/README.md).

## Mutation adequacy

Each proof above carries at least one hand-injected mutant, which shows the proof is sensitive to that
one clause: an aliased serializer, an off-by-one parser and a not-fail-closed parser for TBS-V1, a
commitment-zeroing serializer and a not-fail-closed parser for TBS-V2, an unbound-nonce builder for the
assertion, and the downgrade, no-consume, no-complete, no-suite-check and allow-observed variants for
the rest. Every function named in a `fails (llvm_verify
...)` guard is automatically excluded from the adequacy run below, so a hand-injected mutant cannot
enter the denominator. To measure adequacy rather than sensitivity, `mutation/mutate.py` applies a relational/logical
operator set (the class CVE-2026-24850 lived in: `<`/`<=`, `==`/`!=`, `&&`/`||`, and so on) to each C
reference systematically, one mutation per occurrence, and reruns the matching SAW proof. Across the
eight references, the proofs kill **55 of 58** such mutants (measured 2026-08-22 on an Apple M2 Max). The three survivors are the same shape, a loop bound `i < CAP`
weakened to `i <= CAP`, and each is a semantically equivalent mutant: at `nonce.c:24` the extra index 8
can never equal `s->count`, which is at most 7 when the append runs; at `evidence.c:20` the extra output
index can never match a `seq`, since completeness already forced a permutation; at `nonce_exp.c:26` the
extra index can never equal `first_free`, which is at most 7 whenever `has_room` made the write happen.
None writes out of bounds, so no proof or test that constrains only the input/output relation could
kill them. A specification that also constrained the loop bound would. There are no adequacy gaps in this operator
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
a Cryptol model of the spec rule (each with an injected-mutant non-vacuity check and a 42/44
mutation-adequacy pass, see above), and 5 as a ProVerif reachability result. Properties 1-4/6/7 are
code-level (a C reference is verified); property 5 is a symbolic protocol model with no C link, and the
scope note under each property states what it does and does not establish. A shipped Rust
(de)serializer cannot be verified directly here (a crucible-mir limitation on slice access), which is why
the code-level work is done against C references written to be verifiable.
