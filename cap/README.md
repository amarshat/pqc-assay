# Cap-V1 capability layer (Rust verifier, Kani-proved)

Cap-V1 is the to-be-signed core of an agent-delegation capability token: a fixed-length (191 byte)
record where one agent delegates a specific action over a specific resource to another, bounded by
validity window, audience, and re-delegation depth. It is signed under the HYB-1 hybrid suite (ECDSA
P-256 + ML-DSA-44, the primitive this repo verifies). Kani proves the glue (the signature covers
exactly `serialize(cap)`, both signatures are required, and the signer's key is the one the token
names); the hybrid verify itself is an assumed spec in Kani (too large for CBMC) and runs for real in
`cap/tests/hybrid.rs` (`make cap-hybrid`) with live ECDSA + ML-DSA-44 keys. So a post-quantum
signature runs end to end; only unforgeability stays assumed. Format spec:
[`../docs/cap/CAP-V1.md`](../docs/cap/CAP-V1.md).

This directory is the Rust verifier and its first machine-checked property. The rest of the repo
proves ML-DSA-44 arithmetic (SAW/Isabelle) and Q-SEAL protocol properties (Cryptol/SAW/ProVerif);
Cap-V1 is the "verified Rust" track, so the proof tool is Kani (CBMC), not SMT over a Cryptol model.

## Verified so far (Kani 0.67, this repo)

`make cap-kani` (or `cargo kani` in this directory) checks thirty-three harnesses in `src/lib.rs`,
all verified with 0 failures. Read the count honestly: the independent-content harnesses are the
format bijection/injectivity, the multi-hop attenuation results (`chain_attenuates`,
`chain3_attenuates`, `chain4_attenuates`), `omitting_audience_breaks_binding`, the key-binding
results (`chain_signing_key_is_delegate`, `confused_deputy_rejected`, and their three-link
counterparts), and the stateful replay results (`no_replay`, `accept_consumes`). Many
of the rest are *definition checks* (they assert one clause of the predicate they assume) or
`kani::cover!` non-vacuity pings; the `signed_message_*` pair restates the format lemmas under the
`signed_message == serialize` alias. The spec's "Machine-checked properties" section tags each. And
see the spec's Scope: no signature scheme runs in the verified path, so nothing "post-quantum" is
proved here yet.

Format (bijection, no malleability):

- `roundtrip_parse_serialize`: `parse(serialize(c)) == c` for every capability `c`.
- `roundtrip_serialize_parse`: `well_formed(b) => serialize(parse(b)) == b` for every well-formed
  191-byte string.
- `serialize_injective`: `serialize(c1) == serialize(c2) => c1 == c2`.

Together the serializer is a bijection between `CapV1` and well-formed 191-byte strings, hence
injective: two distinct capabilities can never produce the same signed bytes, so there is no
token-level malleability. Same shape as Q-SEAL's TBS-V1 property 1, but proved in Rust over real
slice access (the parser reads fixed-offset slices; Kani also clears the bounds/panic checks). Kani
unrolls the fixed-offset copies fully over the 191-byte buffer, so this is a complete proof for the
format, not a bounded-depth approximation.

Delegation (attenuation, chains terminate):

- `link_reachable`: the `valid_delegation` link check is satisfiable (`kani::cover!`, SATISFIED), so
  the properties below are not vacuous.
- `link_no_escalation`: a valid re-delegation grants no action bit the parent lacks.
- `link_depth_decreases`: a valid re-delegation strictly decreases depth, so chains terminate.
- `chain_attenuates`: over two hops (`a -> b -> c`), authority only narrows: `c`'s actions are a
  subset of `a`'s, depth strictly decreases, the validity window is contained, and resource and
  audience are unchanged. The local link check composes into the global chain invariant.

Accept gate (`accept_leaf`, signature check abstract):

- `accept_reachable`: the gate is satisfiable (`kani::cover!`, SATISFIED).
- `accept_requires_signature`: nothing is accepted without a valid signature (no bypass).
- `accept_binds_audience`: a capability accepted by verifier `v` names `v` as its audience.
- `accept_within_window`: an accepted capability is inside its validity window at `now`.

Chain accept (`accept_chain2`, composes the link check and the leaf gate):

- `chain_accept_reachable`: satisfiable (`kani::cover!`, SATISFIED).
- `chain_accept_requires_all_sigs`: acceptance requires every link's signature; none can be stripped.
- `chain_accept_attenuates`: an accepted re-delegation grants no more than the root (action subset,
  lower depth, `now` inside the root window, same audience and resource). End-to-end statement.

N-link chain accept (`accept_chain<N>` / `accept_chain_signed<N>`; the two-link functions are the
`N = 2` instance, and the deployed gate is now the general one):

- `chain_n_agrees_with_chain2`: `accept_chain::<2>` equals `accept_chain2` (and the signed variants
  agree) on all inputs, so the two-link theorems transfer and nothing changed at length 2.
- `chain3_reachable`: a three-link accept is satisfiable (`kani::cover!`, SATISFIED).
- `chain3_requires_all_sigs`: a three-link accept requires all three signatures.
- `chain3_attenuates` / `chain4_attenuates`: an accepted 3-link (resp. 4-link) chain's leaf grants
  no more than the root, and depth shrinks by at least one per hop
  (`root.max_depth >= leaf.max_depth + N-1`, at these lengths; the for-all-N "length bounded by
  budget" corollary would need the induction we do not run).
- `chain3_signing_keys_are_delegates`: each non-root link is signed by exactly the key its parent
  delegated to, at both hops.
- `chain3_confused_deputy_rejected`: a wrong key at either hop rejects the whole chain.

These are bounded results at concrete lengths (2, 3, 4), not an induction over all N; see the
spec's scope section.

Single-use leaf presentation (`accept_leaf_once` = the leaf gate plus a bounded used-token store
keyed on `cap_id || nonce`; Q-SEAL property 4's analogue in Rust. Leaf gate only: chains via
`accept_chain` have no replay protection yet):

- `once_reachable`: the single-use gate is satisfiable (`kani::cover!`, SATISFIED).
- `no_replay`: an accepted token presented again to the successor store rejects, for any second
  presentation time. The substantive stateful result.
- `consumed_never_accepts`: a key already in the store never accepts.
- `accept_consumes`: acceptance appends the key; rejection leaves the store unchanged.
- `once_implies_leaf_gate`: single-use acceptance still requires the plain leaf gate (signature,
  audience, window), and a full store fails closed.
- `noconsume_mutant_replays`: under a no-consume mutant the same token accepts twice
  (`kani::cover!` finds the double accept), so `no_replay` has content.

Store capacity is fixed at 8 (`STORE_CAP`, same device as Q-SEAL's CAP=8): the theorems are proved
at that capacity, not for all capacities. Only *accepted* tokens consume a slot (junk cannot fill
the store), but with no eviction the verifier accepts at most 8 tokens for its lifetime, then
rejects all further valid traffic. The analysis is sequential (no concurrent presentation modeled),
and the no-replay theorem is per-store: it assumes each `audience_id` maps to exactly one store, so
replicated verifier instances must share it (see the spec).

Signature binding (`signed_message` = the canonical bytes the signature covers):

- `signed_message_covers_all_fields`: `parse(signed_message(cap)) == cap`; no field is left unsigned.
- `signed_message_injective`: distinct capabilities never share signed bytes.
- `omitting_audience_breaks_binding`: non-vacuity witness. A signer that omitted `audience_id` would
  give two differing-audience capabilities identical bytes; the correct one does not. Catches the
  unsigned-field bug class. The reduction to ML-DSA unforgeability is an argument (see the spec), not
  a Kani result.

Key binding (`accept_*_signed` thread a `PublicKey`; `key_id(pk)` is the id a key commits to):

- `signed_chain_reachable`: the key-bound chain accept is satisfiable (`kani::cover!`, SATISFIED).
- `chain_signing_key_is_delegate`: if a chain is accepted, the key that signed the leaf is the key the
  root delegated to (`key_id(leaf_pk) == root.subject_id`). Composes binding with the link check.
- `confused_deputy_rejected`: a signature under a non-delegated key does not accept, even if valid.
  Closes the key-substitution / confused-deputy hole.

## Real crypto (integration test)

`make cap-hybrid` (or `cargo test --test hybrid`) runs `cap/tests/hybrid.rs`: live ECDSA P-256 +
ML-DSA-44 keys sign `serialize(cap)`, both are verified, and the outcomes plus real key commitments
drive the *same* verified `accept_chain2_signed`. Valid accepts; tampered, downgrade (only the
classical signature valid), confused-deputy (valid signature under a non-delegated key), and expired
all reject. This discharges the assumed `sig_ok` bit with actual post-quantum crypto; only
unforgeability stays assumed. The crypto crates are dev-dependencies, so they do not enter the
Kani-verified core.

## Layout

Byte-exact layout is in the spec. `src/lib.rs` is the single source: `CapV1`, `serialize`, `parse`,
`well_formed`, the accept/delegation/key-binding functions, plus the `#[cfg(kani)]` harnesses. The
library has no runtime dependencies, so the Kani-verified core pulls in no unverified third-party
code; the crypto crates are dev-dependencies used only by the integration test.

## Scope

Proved (Kani): the format bijection, `valid_delegation` attenuation, the leaf accept gate, an
N-link chain accept (verified at lengths 2, 3, 4) that requires every link's signature and never
exceeds the root grant, that the signed message is the canonical/complete/injective encoding, that
each link's signing key is bound to the key its parent delegated to (confused-deputy rejected at
any hop), and single-use acceptance (no replay, on a bounded store). Real ECDSA + ML-DSA-44 runs in
the integration test over `serialize(cap)`. Assumed: ML-DSA-44/ECDSA unforgeability (no test can
prove it), and `key_id` is a placeholder truncated-hash commitment in the model. Bounded: chain
lengths beyond 4 rest on the link-local argument (no induction is machine-checked), and the replay
store is fixed at capacity 8, sequential, fail-closed when full, with no expiry or eviction. Not
yet: revocation, field-value validation in the accept path, and single-use composed into the chain
gate (it is stated on the leaf gate). See the spec's scope section.

## Run

    make cap-kani        # from repo root: 33 Kani harnesses
    make cap-hybrid      # from repo root: real ECDSA + ML-DSA-44 integration test
    cargo kani           # from this directory
    cargo test           # concrete tests incl. the hybrid crypto test
