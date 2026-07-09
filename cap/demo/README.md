# Cap-V1 agent-delegation demo

A runnable demonstration of the Cap-V1 capability layer, no proof toolchain required. Unlike the
Q-SEAL demo (which mirrors a Cryptol model in Rust), this binary calls into the verified library
itself: every accept/reject decision is made by `accept_chain_full`, the deployment gate whose
composition and rules the Kani harnesses cover. The key commitments come from the library's
deployment definition (`hyb1::hyb1_key_id`, KAT-pinned; the SHA-256 inside it is not
harness-covered, it is out of Kani's reach). The signatures are real ECDSA P-256 + ML-DSA-44 (the
RustCrypto crate this project also formally verifies) over the canonical 191-byte capability
bytes.

## Run

    cd cap/demo
    cargo run

or `make cap-demo` from the repo root. Output:

    1. valid delegation chain      sigs=[true ,true ]  ->  ACCEPT
    2. replay, same leaf           sigs unchanged     ->  REJECT
       a gate without the single-use store would have returned ACCEPT again.
    3. tampered leaf               sigs=[true ,false]  ->  REJECT
    4. escalated leaf, valid sig   sigs=[true ,true ]  ->  REJECT
       the signature IS valid; the link check rejects the action bit the root never granted.
    5. foreign signer, valid sig   sigs=[true ,true ]  ->  REJECT
       the foreign key really signed the leaf; the key commitment pins the named issuer.
    6. downgrade (classical only)  sigs=[true ,false]  ->  REJECT
       an accept-on-either verifier would have returned ACCEPT here.
    7. re-delegated terminal leaf  sigs=[true ,true ,true ]  ->  REJECT
       the leaf was minted terminal (FLAG_DELEGATE cleared), so it spawns no children.
    8. fresh leaf, root revoked    sigs=[true ,true ]  ->  REJECT
       a gate that checked revocation on the leaf alone would have returned ACCEPT.

The story: an orchestrator grants an agent a read|write capability on a resource, re-delegable
with depth budget 2. The agent re-delegates a read-only, terminal, narrower-window leaf to a
worker, which presents the two-link chain to a tool server. Case 1 is the working path; every
other case is an attack, and in cases 4, 5, and 7 the presented signatures are genuinely valid.
Those three are the point of a capability layer: the crypto is fine, the authority is not, and
the rejection comes from the verified link and binding rules, not from a signature failure.

The demo self-checks: if any case produces the wrong verdict it prints the mismatch and exits
nonzero, so CI can run it. Which rule rejects each case, and the Kani harness that pins that
rule, is commented per case in `src/main.rs`.

Limits: the demo, like the layer, treats revocation-list distribution as out of band (case 8
revokes directly on the verifier's list), and the single-use store is the bounded (capacity 8)
fail-closed store from the spec. See docs/cap/CAP-V1.md for everything assumed, bounded, or out
of scope.
