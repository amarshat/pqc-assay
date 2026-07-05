# Q-SEAL hybrid attestation demo

A runnable demonstration of the Q-SEAL hybrid attestation, no proof toolchain required. It uses real
ECDSA P-256 and real ML-DSA-44 (the RustCrypto `ml-dsa` crate this project also formally verifies) to
sign the verified TBS-V1 transcript, and shows the acceptance rule that `qseal/proof/hybrid.saw`
machine-checks: both signatures, over the same transcript.

## Run

    cd qseal/demo
    cargo run

Output:

    1. valid attestation           classical=true   pq=true   ->  ACCEPT
    2. tampered transcript         classical=false  pq=false  ->  REJECT
    3. downgrade (classical only)  classical=true   pq=false  ->  REJECT
       a buggy "accept on either" verifier would have returned ACCEPT here.

The third case is the point. A downgrade attack presents a valid classical signature with no valid
post-quantum one (the situation once the classical scheme is broken). HYB-1 rejects it because it
requires both. A verifier that accepted on either signature would have taken it, which is the "hybrid is
decorative" failure the proof rules out.

## What ties to the verification

- `src/tbs.rs` builds the transcript with the same field layout proved bijective in
  `qseal/model/QSEAL_TBS.cry`, via a `create_assertion` that mirrors `QSEAL_Assertion.cry` (challenge
  fields from the request, identity fields from the applet).
- `verify_both` in `src/main.rs` is the accept logic proved in `qseal/proof/hybrid.saw`
  (`accept == classical_ok AND pq_ok` over the same bytes).

This is a reference demo, not a secure-element applet: keys are generated in process and there is no
nonce store or replay protection. Those are the next layer (see the repo roadmap).
