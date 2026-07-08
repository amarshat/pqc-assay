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

`make cap-kani` (or `cargo kani` in this directory) checks fifty-five harnesses in `src/lib.rs`,
all verified with 0 failures. Read the count honestly: the independent-content harnesses are the
format bijection/injectivity, the multi-hop attenuation results (`chain_attenuates`,
`chain_attenuates_flags_and_bindings`,
`chain3_attenuates`, `chain4_attenuates`), `omitting_audience_breaks_binding`, the key-binding
results (`chain_signing_key_is_delegate`, `confused_deputy_rejected`, and their three-link
counterparts), the stateful replay results (`no_replay`, with `chain_once_no_replay` extending the same
mechanism to the chain gate; `accept_consumes` and `chain_once_consumes` are mixed, their reject
halves being definition checks), and the revocation composition
(`revoke_root_then_chain_rejects`; its leaf-only mutant is a non-vacuity cover). Many
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
- `link_requires_delegation_flag`: a parent without `FLAG_DELEGATE` (flags bit 0) has no valid
  re-delegation; terminal capabilities spawn no children.
- `link_flags_no_escalation`: a valid re-delegation grants no flag bit the parent lacks (clearing
  is allowed, minting is not).
- `chain_attenuates_flags_and_bindings`: over two hops, flags only shrink and `cap_type` /
  `constraints_digest` stay the root's (re-checked at lengths 3 and 4 by `chain3_attenuates` /
  `chain4_attenuates`). Pinning the digest is byte equality only: the verifier never resolves or
  enforces the referenced policy, and a zero-digest root pins no constraint set (see the spec).
- `two_hop_link_reachable`: two consecutive valid links are jointly satisfiable
  (`kani::cover!`, SATISFIED), the non-vacuity guard for the two-hop composition harnesses.
- `terminal_leaf_accepted`: a chain whose leaf cleared `FLAG_DELEGATE` still accepts
  (`kani::cover!`, SATISFIED); the rules forbid setting flags, not clearing them.

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

Field-value validation (`valid_field_values` pins `version == 1` and `suite_id == HYB-1`, the only
defined value sets in v0.1; `accept_leaf_checked` / `accept_chain_checked<N>` run it before the
plain gates):

- `checked_rejects_unknown_values`: an unknown version or suite never accepts, at the leaf gate and
  at every position of a 3-link chain.
- `checked_implies_gate_and_pins_values`: the checked gates do not weaken the plain ones, and an
  accepted token provably carries version 1 and HYB-1.
- `unchecked_gate_accepts_unknown_values`: the plain gate really is over-permissive
  (`kani::cover!` finds it accepting an unknown version and suite), so the validation is not
  vacuous. `cap_type` and `flags` value sets are not validated by `valid_field_values` (which
  values are legal is provisional); their cross-link relations ARE enforced by `valid_delegation`
  (type pinned, flags subset, `FLAG_DELEGATE` consulted, see Delegation above).
- `checked_reachable`: both checked gates satisfiable (`kani::cover!`, SATISFIED).

Single-use presentation (`accept_leaf_once` for a bare leaf, `accept_chain_once<N>` for a chain;
both = their stateless gate plus one shared bounded used-token store keyed on the presented leaf's
`cap_id || nonce`; Q-SEAL property 4's analogue in Rust):

- `once_reachable`: the single-use gate is satisfiable (`kani::cover!`, SATISFIED).
- `no_replay`: an accepted token presented again to the successor store rejects, for any second
  presentation time. The substantive stateful result.
- `consumed_never_accepts`: a key already in the store never accepts.
- `accept_consumes`: acceptance appends the key; rejection leaves the store unchanged.
- `once_implies_leaf_gate`: single-use acceptance still requires the plain leaf gate (signature,
  audience, window), and a full store fails closed.
- `noconsume_mutant_replays`: under a no-consume mutant the same token accepts twice
  (`kani::cover!` finds the double accept), so `no_replay` has content.
- `chain_once_no_replay`: after a 3-link chain is accepted, any 2- or 3-link chain whose leaf
  carries the same replay key rejects against the successor store (re-presenting the identical
  chain is the special case).
- `chain_once_implies_chain_gate` / `chain_once_reachable`: the stateful chain gate does not weaken
  `accept_chain`, fails closed when full, and is satisfiable.
- `chain_once_consumes`: chain acceptance consumes the leaf's key, and because the leaf and chain
  gates share one store, a chain-consumed leaf cannot re-enter through `accept_leaf_once`;
  rejection leaves the store unchanged.

Revocation (`RevocationStore` = a bounded append-only list of revoked `cap_id`s; `revoke` adds,
`is_revoked` scans, and the composed gates below check it on EVERY link):

- `revoked_any_link_kills_chain`: if any link of a 3-link chain (root, intermediate, or leaf) is
  revoked, the composed chain gate rejects. Cutting one delegation cuts all authority presented
  through it.
- `revoke_root_then_chain_rejects`: the stateful composition; a chain the gate accepts is rejected
  after `revoke(root.cap_id)`.
- `revoked_leaf_never_accepts` / `revoke_marks_revoked_or_fails_open`: the leaf gate rejects a
  revoked leaf; a successful revoke marks and is idempotent, a refused revoke (full list) changes
  nothing.
- `leafonly_revocation_mutant_accepts_revoked_root`: under a leaf-only-revocation mutant a chain
  with a revoked ROOT still accepts (`kani::cover!` finds it), so per-link checking is exactly what
  the ancestor-revocation theorem needs.

Read the limits carefully. Revocation keys on `cap_id` alone and assumes issuers keep cap_ids
globally unique (two caps sharing an id are revoked together, even across unrelated delegation
trees at one verifier). It cuts a specific cap, not an agent: sibling caps and the delegate's key
survive, so like single-use it does not contain a compromised delegate. And the list FAILS OPEN
when full: `revoke` is refused and the capability stays live, the opposite direction from the
nonce store; capacity 8 means at most 8 distinct revoked cap_ids, no eviction. Revocation-list
distribution (issuer to verifier) is out of scope entirely.

Composed deployment gates (`accept_leaf_full` / `accept_chain_full<N>`; the individual gates do
not compose themselves, and hand-stacking `_checked` + `_once` on a chain would drop key binding,
since `accept_chain_once` wraps the unsigned `accept_chain`):

- `full_implies_all_conjuncts`: `accept_chain_full` acceptance implies field validation and
  non-revocation on every link, the key-bound `accept_chain_signed` (key binding kept on the
  single-use path), and consumption of the leaf's key.
- `full_no_replay`: after `accept_chain_full` accepts, the same leaf rejects on the successor store
  through both composed gates (one shared store).
- `full_reachable`: both composed gates satisfiable (`kani::cover!`, SATISFIED).

What single-use means for a chain, honestly: it is per-presentation anti-replay (a captured
presentation cannot be re-run). It is not a cap on authority exercise: a delegate with remaining
depth can mint unlimited distinct single-use leaves, each accepted once, so no `_once` or `_full`
gate rate-limits or contains a compromised intermediate.

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
- `committing_to_commits` (definition check): `key_id(PublicKey::committing_to(id)) == id` for every
  id. The round trip is what's machine-checked; the wiring that feeds `hyb1::hyb1_key_id` output
  (below) through `committing_to` is convention, exercised in the integration test, not a harness.

## Real crypto (integration test)

`make cap-hybrid` (or `cargo test --features hyb1-keyid --test hybrid`) runs `cap/tests/hybrid.rs`:
live ECDSA P-256 + ML-DSA-44 keys sign `serialize(cap)`, both are verified, and the outcomes plus
real key commitments drive the *same* verified `accept_chain2_signed`. Valid accepts; tampered,
downgrade (only the classical signature valid), confused-deputy (valid signature under a
non-delegated key), and expired all reject. This discharges the assumed `sig_ok` bit with actual
post-quantum crypto; only unforgeability stays assumed. The crypto crates are dev-dependencies, so
they do not enter the Kani-verified core.

The key commitment is the library's deployment definition, not a test-local copy: `hyb1::hyb1_key_id`
(feature `hyb1-keyid`) is the first 16 bytes of SHA-256 over `"CAPV1-KEYID-HYB1" || ec_compressed ||
mldsa_pk` (both inputs fixed length, so no length prefixes needed), and a KAT pins it against silent
change (the KAT runs under `make cap-hybrid`, which runs the full feature-on test suite). The 128-bit
truncation means ~2^128 against substituting a key for a given id (second preimage, single-target;
hitting any of N ids gains a factor N) but only ~2^64 against a party colliding two of its own keys
(birthday); the spec discloses both. The feature is off by default so the Kani build stays
dependency-free; the hash itself is the `sha2` crate's, not verified here.

## Layout

Byte-exact layout is in the spec. `src/lib.rs` is the single source: `CapV1`, `serialize`, `parse`,
`well_formed`, the accept/delegation/key-binding functions, plus the `#[cfg(kani)]` harnesses. The
library has no default dependencies, so the Kani-verified core pulls in no unverified third-party
code; `sha2` compiles only under the `hyb1-keyid` feature (deployment key commitment, outside every
harness), and the crypto crates are dev-dependencies used only by the integration test.

## Scope

Proved (Kani): the format bijection, `valid_delegation` attenuation (action, depth, window, and
flags narrow; `FLAG_DELEGATE` required on every parent, so terminal capabilities spawn no
children; `cap_type` and `constraints_digest` pinned to the root's), the leaf accept gate, an
N-link chain accept (verified at lengths 2, 3, 4) that requires every link's signature and never
exceeds the root grant, that the signed message is the canonical/complete/injective encoding, that
each link's signing key is bound to the key its parent delegated to (confused-deputy rejected at
any hop), and single-use acceptance (no replay, on a bounded store). Real ECDSA + ML-DSA-44 runs in
the integration test over `serialize(cap)`. Assumed: ML-DSA-44/ECDSA unforgeability (no test can
prove it), and collision resistance of the deployed key commitment (`hyb1_key_id`, truncated
SHA-256: ~2^128 second preimage, ~2^64 birthday; the model's `key_id` stays an abstract commitment
inside Kani, bridged by the machine-checked `committing_to`). Bounded: chain
lengths beyond 4 rest on the link-local argument (no induction is machine-checked), and the replay
store is fixed at capacity 8, sequential, fail-closed when full, with no expiry or eviction. Not
yet: absolute value sets for `cap_type` / flag bits beyond bit 0 (still provisional, so
`valid_field_values` pins only `version` and `suite_id`; cross-link relations for those fields ARE
enforced), structured constraint tightening (the digest is opaque, so links require equality),
revocation-list distribution, and expiry/eviction for either bounded store. See the spec's scope
section.

## Run

    make cap-kani        # from repo root: 55 Kani harnesses
    make cap-hybrid      # from repo root: real ECDSA + ML-DSA-44 integration test
    cargo kani           # from this directory
    cargo test --features hyb1-keyid   # concrete tests incl. the hybrid crypto test
                                       # (plain `cargo test` skips the hybrid test: it
                                       # needs the feature, declared via required-features)

CI: `.github/workflows/cap.yml` runs both (the full harness set via `cap/verify_cap.sh`, then the
feature-on test suite) on every push touching `cap/` or `docs/cap/`, with Kani pinned to the
version the spec's results were produced with. This leg is separate from `make verify` (the
SAW/Isabelle pipeline); the two share no toolchain.
