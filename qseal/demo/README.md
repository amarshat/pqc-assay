# Q-SEAL hybrid attestation demo

A runnable demonstration of the Q-SEAL hybrid attestation, no proof toolchain required. It uses real
ECDSA P-256 and real ML-DSA-44 (the RustCrypto `ml-dsa` crate this project also formally verifies) to
sign the verified TBS-V1 transcript, and shows two rules the proofs machine-check: both signatures over
the same transcript (`qseal/proof/hybrid.saw`), and a single-use challenge (`qseal/proof/nonce.saw`).

## Run

    cd qseal/demo
    cargo run

Output:

    1. valid attestation           classical=true   pq=true   ->  ACCEPT
    2. tampered transcript         classical=false  pq=false  ->  REJECT
    3. downgrade (classical only)  classical=true   pq=false  ->  REJECT
       a buggy "accept on either" verifier would have returned ACCEPT here.
    4. first submission            sigs_ok=true   fresh=true   ->  ACCEPT
       replay (same request_id)    sigs_ok=true   fresh=false  ->  REJECT
       a verifier that skips consume_nonce_once would have returned ACCEPT on the replay.
    5. valid request               validated=true   ->  SIGN
       malformed (bad suite_id)    validated=false  ->  REFUSE
       a verifier that skipped the suite check would have signed the malformed request.
    6. complete fragment set       exact=true       ->  RECOVER
       dropped fragment            recovered=false  ->  REJECT
       a reassembler that skipped the completeness check would have returned zero-filled bytes.

Case 3 is the downgrade point: a valid classical signature with no valid post-quantum one (the situation
once the classical scheme is broken). HYB-1 rejects it because it requires both. A verifier that accepted
on either signature would have taken it, the "hybrid is decorative" failure the proof rules out.

Case 4 is replay: the exact same valid attestation, resubmitted. A stateful verifier consumes the
request_id on first accept, so the replay is rejected even though both signatures still verify. A
verifier that skipped the consume step would accept it.

Case 5 is malformed input: a request under an unsupported suite. The applet validates before signing, so
it produces no transcript at all. A gate that skipped the suite check would have signed it.

Case 6 is evidence read-back: the applet returns the evidence blob as fragments (APDU chaining). A
complete set reassembles to exactly the original bytes; a dropped fragment (which shows up as a
duplicated index) is rejected rather than zero-filled. A reassembler that skipped the completeness check
would have returned corrupted bytes under an "ok" result.

## What ties to the verification

- `src/tbs.rs` builds the transcript with the same field layout proved bijective in
  `qseal/model/QSEAL_TBS.cry`, via a `create_assertion` that mirrors `QSEAL_Assertion.cry` (challenge
  fields from the request, identity fields from the applet).
- `verify_both` in `src/main.rs` is the accept logic proved in `qseal/proof/hybrid.saw`
  (`accept == classical_ok AND pq_ok` over the same bytes).
- `NonceStore` in `src/main.rs` is the single-use logic proved in `qseal/proof/nonce.saw`: accept iff
  validated and the request_id is fresh, consume it on accept. It is an in-memory `HashSet` twin of the
  append-only store in `qseal/ref/nonce.c`.
- `validate_request` / `create_assertion_checked` in `src/tbs.rs` are the twins of
  `qseal/model/QSEAL_Validate.cry` (`valid` / `create_checked`), proved equal to the C
  `qseal_validate_request` / `qseal_create_assertion_checked` in `qseal/proof/validate.saw`: a malformed
  request is refused before signing.
- `reassemble_evidence` in `src/main.rs` is the twin of `qseal/ref/evidence.c`, proved equal to
  `qseal/model/QSEAL_Evidence.cry` in `qseal/proof/evidence.saw`: a complete fragment set recovers the
  exact bytes, a dropped or mis-sized one fails closed.

The demo binary is NOT itself verified. Each piece above is a Rust twin of a rule proved in
`qseal/proof/*.saw`; the proofs are about the Cryptol model and the C reference, not this code. The twins
also diverge where it matters: `NonceStore` is an unbounded `HashSet`, whereas the verified C store is
fixed-capacity (CAP=8) and fail-closed when full, so the demo never exercises the full-store behavior.

This is a reference demo, not a secure-element applet: keys are generated in process, the nonce store is
in-memory (no persistence, no secure element, no concurrency), and check-and-consume is sequential.
Those are the next layer (see the repo roadmap).
