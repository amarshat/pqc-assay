# Cap-V1: fixed-format agent-delegation capability token

Status: draft v0.1. Layout frozen for the machine-checked bijection; field semantics may still change.

## What this is

Cap-V1 is the to-be-signed (TBS) core of a capability token one software agent hands another to
delegate authority. It says, in canonical bytes: agent `issuer_id` grants `action` over
`resource_id` to agent `subject_id`, valid from `not_before` to `not_after`, usable only against
`audience_id`, re-delegatable at most `max_depth` more times. The token on the wire is the 191-byte
TBS followed by its signature(s); the signature covers exactly these bytes.

The design rule is the same one Q-SEAL uses for its TBS-V1 transcript: fixed length, no optional
fields, no variable-length encodings. That makes the serializer a bijection on its byte encoding,
so it is injective: two distinct capabilities can never produce the same signed bytes. There is no
token-level malleability to exploit. This is the structural opposite of a non-fixed,
validation-dependent decoder (the shape of CVE-2026-24850, where the ML-DSA hint decoder admitted
non-canonical inputs because acceptance depended on runtime checks rather than on the format).

The difference from Q-SEAL's transcript work is the verifier and the proof tool. Here the verifier
is Rust (`cap/src/lib.rs`) and the properties are discharged with Kani (CBMC backend) by bounded
symbolic execution over the full 191-byte buffer, not by an SMT proof over a Cryptol model. That is
deliberate: the product is a verified Rust capability layer, and this is its first proved property.

## Wire layout (191 bytes)

`magic` is a fixed 5-byte prefix (`"CAPV1"`), not part of the variable record. Every other field is
fixed length; offsets are cumulative from the start of the buffer.

| Offset | Len | Field                | Meaning                                                        |
|-------:|----:|----------------------|----------------------------------------------------------------|
| 0      | 5   | magic                | `"CAPV1"`, format tag                                          |
| 5      | 1   | version              | 1 for this layout                                             |
| 6      | 2   | suite_id             | crypto suite (e.g. HYB-1 = ECDSA P-256 + ML-DSA-44)           |
| 8      | 1   | cap_type             | capability kind / token type                                 |
| 9      | 1   | flags                | flag bits (bit0 = further delegation permitted)              |
| 10     | 16  | issuer_id            | delegator: key id of the granting agent                      |
| 26     | 16  | subject_id           | delegate: key id of the bearer that may exercise the cap     |
| 42     | 16  | parent_id            | parent capability id in the chain; all-zero for a root cap   |
| 58     | 16  | cap_id               | unique id of this capability                                 |
| 74     | 32  | resource_id          | digest of the resource / object the capability is over       |
| 106    | 4   | action               | permitted actions, bitmask (independent bits; attenuation is bitwise subset) |
| 110    | 1   | max_depth            | remaining re-delegation depth; 0 = may not re-delegate       |
| 111    | 32  | constraints_digest   | digest binding out-of-band policy constraints                |
| 143    | 8   | not_before           | validity start, unix seconds, big-endian                     |
| 151    | 8   | not_after            | validity end / expiry, unix seconds, big-endian              |
| 159    | 16  | nonce                | freshness / anti-replay                                      |
| 175    | 16  | audience_id          | intended verifier / service; blocks cross-service replay     |
| 191    |     | (end)                |                                                              |

## Signature envelope

Cap-V1 is signature-agnostic at the format level. The full token is `serialize(cap) || sig`, where
`sig` is produced over the exact 191 TBS bytes. The intended suite is HYB-1: ECDSA P-256 and
ML-DSA-44, both required (same hybrid, no-downgrade stance as Q-SEAL HYB-1), reusing the ML-DSA-44
primitive this repo verifies. Signature verification itself is not exercised by the proofs below: the
`sig_ok` bit is an abstract input (see Scope). See Domain separation for the shared-key caveat with
Q-SEAL.

## Delegation model (intended, not all machine-checked yet)

- A root capability has `parent_id = 0` and is signed by the resource owner's key.
- A re-delegation sets `parent_id` to the parent's `cap_id`, `issuer_id` to the re-delegating
  agent's key (which must equal the parent's `subject_id`), and `max_depth` strictly below the
  parent's. What the current `valid_delegation` check actually enforces: `issuer_id ==
  parent.subject_id`, `parent_id == parent.cap_id`, `resource_id`/`audience_id`/`suite_id` **equal**
  the parent's (not "subset"; `resource_id` is a digest with no subset order), `action` bits a subset
  of the parent's, `max_depth` strictly decreasing with the parent still having budget, and the
  validity window nested and non-empty.
- Known gaps in that check (see Scope): it does **not** yet constrain `flags`, `cap_type`,
  `constraints_digest`, or `version`. So the documented `flags` bit0 ("further delegation permitted")
  is not consulted (re-delegation is gated only by `max_depth > 0`), and a child may point at a
  different `constraints_digest` than its parent. "Authority only narrows" holds for `action`, depth,
  and window; it does not yet hold for those fields.
- A verifier accepts a chain if every link's signature verifies, windows are current, the audience
  matches, depth decreases down the chain, and each link attenuates the previous.

The chain-link check `valid_delegation(parent, child)` (`cap/src/lib.rs`) is the non-signature part
of this rule. Crucially it checks `issuer_id`/`subject_id` as **byte equality of opaque ids**, not
that the key which produced the signature is the key named by `issuer_id`. Binding ids to keys is out
of scope here (see Scope); without it the chain guarantees are conditional on that binding holding.

## Machine-checked properties (this session, Kani)

`cap/src/lib.rs`, harnesses under `#[cfg(kani)] mod verification`, run with `cargo kani` (or
`make cap-kani`). Kani 0.67.0, CBMC backend. All forty-nine verified, 0 failures. `any_cap()` is
`parse(kani::any::<[u8; 191]>())`, which ranges over all `CapV1` (each field is an independent slice
of a fully symbolic buffer).

Not all forty-nine carry equal weight, and the count should not be read as "forty-nine
independent theorems". The honest taxonomy:
- Independent content: the format bijection/injectivity (`roundtrip_*`, `serialize_injective`), the
  multi-hop attenuation results (`chain_attenuates`, `chain3_attenuates`, `chain4_attenuates`),
  `omitting_audience_breaks_binding` (a mutation witness that a plausible bug would be caught), the
  key-binding results (`chain_signing_key_is_delegate`, `confused_deputy_rejected` and their
  three-link counterparts), the stateful replay results (`no_replay`, with `chain_once_no_replay`
  extending the same mechanism to the chain gate; `accept_consumes` / `chain_once_consumes` are
  mixed, see their tags), and the revocation results (`revoke_root_then_chain_rejects` plus its
  leaf-only-mutant witness).
- Definition checks (marked below): each assumes a predicate `P` and asserts one conjunct of `P`, so
  it confirms the definition contains the clause but is not an independent theorem.
- `signed_message` is defined as `serialize`, so `signed_message_covers_all_fields` and
  `signed_message_injective` are the format lemmas under the signing alias, not new results.
- `*_reachable` are `kani::cover!` non-vacuity pings (SATISFIED), not properties.

Format (bijection / no malleability):

- `roundtrip_parse_serialize`: `parse(serialize(c)) == c` for every capability `c`.
- `roundtrip_serialize_parse`: `well_formed(b) => serialize(parse(b)) == b` for every well-formed
  191-byte string.
- `serialize_injective`: `serialize(c1) == serialize(c2) => c1 == c2`. No two distinct capabilities
  share signed bytes.

Together the serializer is a bijection between `CapV1` and well-formed 191-byte strings, hence
injective. The parser uses only fixed-offset, constant-size slice copies, so the harnesses also
exercise real slice access under Kani (no panics, no out-of-bounds), which is the "verified Rust"
claim made concrete.

Delegation (attenuation / chains terminate):

- `link_reachable`: `valid_delegation(p, c)` is satisfiable (a `kani::cover!`, reported SATISFIED),
  so the delegation properties below are not vacuous.
- `link_no_escalation` (definition check): `valid_delegation(p, c) => action_bits(c) &
  !action_bits(p) == 0`. This is a literal conjunct of `valid_delegation`.
- `link_depth_decreases` (definition check): `valid_delegation(p, c) => c.max_depth < p.max_depth`.
  Also a literal conjunct.
- `chain_attenuates` (two-hop composition, independent content): if `valid_delegation(a, b)` and
  `valid_delegation(b, c)` then `c`'s action bits are a subset of `a`'s, `c.max_depth < a.max_depth`,
  `c`'s validity window is inside `a`'s, and resource and audience are unchanged. This composes the
  local check across two links (subset, `<`, and interval-containment are transitive). No induction
  is run; the N-link accept gate below re-checks the composition at chain lengths 3 and 4, and
  lengths beyond those remain covered by the link-local argument only.

Accept gate (`accept_leaf(cap, verifier_id, now, sig_ok)`). `sig_ok` is the signature-check outcome,
kept as an input so the guarantees hold for any correct verifier (Q-SEAL's uninterpreted-verifier
device):

- `accept_reachable`: `accept_leaf` is satisfiable (`kani::cover!`, SATISFIED).
- `accept_requires_signature` (definition check): `!accept_leaf(cap, v, now, false)`. Short-circuits
  on the `sig_ok &&` conjunct.
- `accept_binds_audience` (definition check): `accept_leaf(cap, v, now, s) => cap.audience_id == v`.
  A conjunct of `accept_leaf`.
- `accept_within_window` (definition check): `accept_leaf(cap, v, now, s) => not_before <= now <=
  not_after`. A conjunct of `accept_leaf`.

These three confirm the accept predicate has the clauses we intend (audience, window, signature-gated)
and nothing weaker slipped in. They are not independent theorems.

Chain accept (`accept_chain2(root, leaf, verifier_id, now, root_sig_ok, leaf_sig_ok)`) composes the
link check and the leaf gate: accept iff `root` is a root, both signatures verify, `leaf` is a valid
re-delegation of `root`, and `leaf` passes the leaf gate.

- `chain_accept_reachable`: satisfiable (`kani::cover!`, SATISFIED).
- `chain_accept_requires_all_sigs` (definition check): `accept_chain2(..) => root_sig_ok &&
  leaf_sig_ok`. Both signature bits are conjuncts of `accept_chain2`; this confirms neither link's
  signature bit can be cleared and still accept. It says nothing about what makes a bit true.
- `chain_accept_attenuates` (independent content, composes the link check into the gate): if the
  chain is accepted then the leaf grants no more than the root:
  `action_bits(leaf) ⊆ action_bits(root)`, `leaf.max_depth < root.max_depth`, `now` is inside the
  root's window, both name the presenting verifier as audience, and the resource is the same. So
  accepting a re-delegation can never exceed the root grant. This is the end-to-end statement the
  earlier link/gate lemmas build up to.

N-link chain accept (`accept_chain<N>(caps, verifier_id, now, sigs_ok)` generalizes `accept_chain2`:
`caps[0]` must be a root, every link's signature must verify, every adjacent pair must pass
`valid_delegation`, and the leaf must pass the accept gate. `N` is a compile-time length, so the
loops fully unroll under Kani; the harnesses instantiate concrete lengths, they do not quantify over
`N`. Degenerate lengths: `N = 0` rejects, and `N = 1` is the intended root-presented-directly case
(is_root + signature + leaf gate); no harness instantiates either, so their behavior is by
inspection, not machine-checked):

- `chain_n_agrees_with_chain2` (definitional bridge): `accept_chain::<2>` equals `accept_chain2`
  and `accept_chain_signed::<2>` equals `accept_chain2_signed`, on all inputs. So the two-link
  theorems transfer to the generalized gate, and the generalization changed nothing at length 2.
- `chain3_reachable`: a three-link accept is satisfiable (`kani::cover!`, SATISFIED).
- `chain3_requires_all_sigs` (definition check): acceptance implies all three signature bits.
- `chain3_attenuates` / `chain4_attenuates` (independent content): if a 3-link (resp. 4-link) chain
  is accepted, the leaf grants no action bit the root lacks, `now` is inside the root's window,
  resource and audience are unchanged, and the depth budget shrank by at least one per hop
  (`root.max_depth >= leaf.max_depth + N-1`, at these lengths). The "chain length is bounded by the
  root's budget" corollary is a for-all-N statement, i.e. the induction disclaimed below; only the
  instantiated margins are machine-checked.
- `chain3_signing_keys_are_delegates` (independent content): in an accepted key-bound 3-link chain,
  each non-root link is signed by exactly the key its parent delegated to
  (`key_id(pks[i]) == caps[i-1].subject_id`), at both hops.
- `chain3_confused_deputy_rejected` (independent content, stated as the attack): a wrong key at
  *either* hop makes the chain reject, whatever else is set.

Read the length honestly: these are bounded results at N = 2, 3, 4 (each harness a fixed
instantiation). There is still no machine-checked induction giving all N at once; what changed is
that the verifier code itself is now the general gate, and the composition has been re-checked at
every length the harnesses instantiate rather than only at 2.

Single-use leaf presentation (`accept_leaf_once(cap, verifier_id, now, sig_ok, store)` = the leaf gate plus a bounded
used-token store. The replay key is `cap_id || nonce` (32 bytes), with no verifier component,
unlike Q-SEAL's challenge key. That is sound only under an assumption the harnesses do not check:
**each `audience_id` corresponds to exactly one store**. Audience binding stops presentation to a
different audience; it says nothing about two stores behind the same audience. A horizontally
replicated verifier (N instances sharing one `audience_id`, each with a private store) breaks
single-use: a token consumed at instance 1 replays cleanly at instance 2. Replicated instances must
share the store (or a verifier/instance component must be added to the key). `no_replay` below is a
per-store theorem. The store is an append-only log of `STORE_CAP = 8` keys; acceptance appends, and
a full store or an already-consumed key rejects):

- `once_reachable`: the gate is satisfiable (`kani::cover!`, SATISFIED).
- `no_replay` (independent content, the stateful result): if a token is accepted, presenting the
  same token to the successor store rejects, for any second presentation time and signature bit.
  The mutation of the store is what blocks the second accept.
- `consumed_never_accepts` (definition check): a key already in the store rejects.
- `accept_consumes` (mixed): the accept half has content (the appended key is visible to the
  membership scan, which is bounds reasoning); the reject half (store unchanged) is a definition
  check.
- `once_implies_leaf_gate` (definition check): the stateful gate does not weaken the stateless one;
  acceptance still implies `accept_leaf`, and `len >= STORE_CAP` fails closed.
- `noconsume_mutant_replays` (non-vacuity, mutation-style): a no-consume variant of the gate accepts
  the same token twice (`kani::cover!` finds the double accept), so `no_replay` is not vacuous and
  the consume step is exactly what it checks.

Field-value validation (`valid_field_values(cap)` = `version == VERSION_V1 && suite_id ==
SUITE_HYB1`, the only fields with defined value sets in v0.1; `accept_leaf_checked` /
`accept_chain_checked<N>` run it before the plain gates, on every link):

- `checked_reachable`: both checked gates satisfiable (`kani::cover!`, SATISFIED).
- `checked_rejects_unknown_values` (definition check at the leaf gate, loop coverage at the chain
  gate): a token with an unknown version or suite never accepts at the leaf gate (a short-circuit
  of the conjunction), and rejects a 3-link chain at whichever position it sits (the validation
  loop visits every link). Not an independent theorem.
- `checked_implies_gate_and_pins_values` (definition check): checked acceptance implies the plain
  gate and pins `version` / `suite_id` to the defined values.
- `unchecked_gate_accepts_unknown_values` (non-vacuity, the over-permissive-gate witness, Q-SEAL
  property 7's device): the plain `accept_leaf` accepts a token whose version and suite are both
  unknown, which the checked gate provably rejects. So the validation is what stands between the
  verifier and tokens it cannot interpret.

`cap_type` and `flags` are deliberately not constrained (semantics provisional, disclosed in
Scope). Q-SEAL's property 7 lesson carries over: this gate covers enumerated field values only;
byte-level parsing of a hostile wire input is the format bijection's job, and anything upstream of
the 191-byte buffer (transport framing) is out of scope.

Chain composition (`accept_chain_once<N>` = `accept_chain` plus the same store, consuming the
presented leaf's key; intermediates are not consumed, since the leaf pins its chain via `parent_id`
and per-link signatures, so re-presenting the chain means re-presenting the leaf key. Read the
security consequence precisely: this is per-presentation anti-replay, not a cap on authority
exercise. A delegate holding remaining depth can mint unlimited distinct single-use leaves (fresh
`cap_id`/`nonce`, signed under its own delegated key), each accepted exactly once, so this gate
does not rate-limit or contain a compromised intermediate):

- `chain_once_reachable`: satisfiable at three links (`kani::cover!`, SATISFIED).
- `chain_once_no_replay` (independent content): after any 3-link chain is accepted, any 2- or
  3-link chain whose leaf carries the same replay key rejects against the successor store, whatever
  its other links, time, or signature bits. Re-presenting the identical chain is the special case.
- `chain_once_implies_chain_gate` (definition check): acceptance implies `accept_chain`, and a full
  store fails closed.
- `chain_once_consumes` (mixed, like `accept_consumes`): acceptance puts the leaf's key in the
  successor store and, because both gates share the store, the consumed leaf also rejects through
  `accept_leaf_once`; rejection leaves the store unchanged.

Like the chain gate itself, these are instantiated at concrete lengths (3, with the cross-gate
check against 2), not for all N.

Revocation (`RevocationStore` = a bounded append-only list of revoked `cap_id`s, capacity
`STORE_CAP = 8`, one per verifier; `revoke(rs, cap_id)` returns the verdict and successor list;
`is_revoked` scans the live prefix. How a verifier learns what to revoke, i.e. list distribution,
is entirely out of scope; these theorems are about what an up-to-date list enforces):

- `revoked_leaf_never_accepts` (definition check): a revoked leaf rejects through
  `accept_leaf_full`, whatever key, time, or signature is presented, store unchanged.
- `revoked_any_link_kills_chain` (definition check at each position, the composed statement): if
  any link of a 3-link chain is revoked, `accept_chain_full` rejects. Revocation is checked per
  link, so revoking an ancestor kills every chain presented through it.
- `revoke_root_then_chain_rejects` (independent content, `no_replay`'s shape for revocation): a
  chain the gate accepts is rejected after its root's `cap_id` is revoked; `revoke`'s append is
  visible to `is_revoked`'s scan at the root position.
- `revoke_marks_revoked_or_fails_open` (mixed): a successful revoke marks the id (idempotently); a
  refused revoke (full list) leaves the list unchanged and the id unrevoked.
- `leafonly_revocation_mutant_accepts_revoked_root` (non-vacuity, mutation-style): a variant that
  checks revocation on the presented leaf only accepts a chain whose root is revoked
  (`kani::cover!` finds it), which the shipped per-link gate provably rejects. Per-link checking is
  exactly what the ancestor theorem needs.

The fail direction is the opposite of the nonce store's and is the key disclosed limit: a full
revocation list FAILS OPEN. `revoke` is refused and the capability stays live, so a capacity-8
list can only ever kill 8 delegations, and there is no eviction. The nonce store fails closed
(availability risk); the revocation list fails open (authority-containment risk). A deployment
sizing these stores is choosing between those two failure modes, and this model makes the choice
visible rather than solving it.

Composed deployment gates (`accept_leaf_full` = field validation + key binding + leaf gate +
single-use; `accept_chain_full<N>` = field validation and key binding on every link + chain gate +
single-use on the leaf. These exist because the individual gates do not compose themselves:
`accept_chain_once` wraps the unsigned `accept_chain`, so stacking `_checked` + `_once` by hand
would drop key binding on the chain path):

- `full_reachable`: both composed gates satisfiable (`kani::cover!`, SATISFIED).
- `full_implies_all_conjuncts` (definition check, but the one that makes the composition safe to
  rely on): `accept_chain_full` acceptance implies `valid_field_values` and non-revocation on all
  three links, the key-bound `accept_chain_signed`, and consumption of the leaf's key. Key binding
  is provably not lost on the single-use path.
- `full_no_replay` (independent content via `no_replay`'s mechanism): after `accept_chain_full`
  accepts, the same leaf rejects on the successor store through both `accept_chain_full` and
  `accept_leaf_full`, whatever key, time, or signature bits the second presentation uses.

Disclosed limits, mostly shared with Q-SEAL property 4: the capacity is fixed at 8 (the logic does
not depend on it, but the theorems are proved at that capacity, not for all capacities).
Fail-closed-when-full plus no eviction means the verifier accepts at most 8 tokens in its lifetime
and then rejects all further valid traffic; note the fill is *not* attacker-triggerable with junk
(a slot is consumed only on acceptance, so filling it takes 8 validly accepted tokens), unlike
Q-SEAL's store, but exhaustion by legitimate traffic is guaranteed. The analysis is sequential and
atomic (no concurrent presentation / TOCTOU window is modeled). Single-use is composed into the
chain gate via `accept_chain_once` (below), so both presentation paths consume from one store.

Signature binding (`signed_message(cap)` is the canonical byte string the signature covers, and in
`accept_leaf` the `sig_ok` bit is the verifier's verdict over exactly those bytes):

- `signed_message_covers_all_fields` (format lemma under the signing alias): `parse(signed_message(
  cap)) == cap`. Because `signed_message == serialize`, this is `roundtrip_parse_serialize` renamed.
  Every field sits inside the signed bytes; nothing authorized is left unsigned.
- `signed_message_injective` (format lemma under the signing alias): distinct capabilities never
  share signed bytes. This is `serialize_injective` renamed.
- `omitting_audience_breaks_binding` (independent content): the coverage property is not vacuous and
  is exactly what binds
  the audience. Two capabilities differing only in `audience_id` get different signed bytes under the
  correct serializer, but identical bytes under a signer that omitted `audience_id`. So the property
  catches the unsigned-field bug class (the Kani analogue of the repo's mutation checks). Concrete
  `cargo test` witnesses the same collision.

Reduction to unforgeability (argument, not machine-checked). The two facts above plus ML-DSA-44
unforgeability give the security statement we want: a signature that verifies over one capability's
`signed_message` is not valid over any other capability's bytes (the messages differ by injectivity),
so a captured signature cannot be re-bound to a different capability. The unforgeability step is an
assumption about the signature scheme, not a Kani result; the ML-DSA-44 primitive itself is verified
elsewhere in this repo (SAW/Isabelle). What Cap-V1 owns and proves here is that the signed message is
the canonical, complete, injective encoding, which is the precondition that reduction needs.

Key binding (`accept_leaf_signed` / `accept_chain2_signed` thread a `PublicKey` per link; `key_id(pk)`
is the id a key commits to; acceptance requires `key_id(issuer_pk) == cap.issuer_id`, so the token
names its signer). The `*_sig_ok` bits are the assumed outcome of the real hybrid verify over each
link's `signed_message`; that verify is run for real in the integration test (see below), not in
Kani.

- `signed_chain_reachable`: the key-bound chain accept is satisfiable (`kani::cover!`, SATISFIED).
- `chain_signing_key_is_delegate` (independent content): if a two-link chain is accepted, the key
  that signed the leaf is exactly the key the root delegated to: `key_id(leaf_pk) == root.subject_id`.
  This composes the binding (`key_id(leaf_pk) == leaf.issuer_id`) with the link check
  (`leaf.issuer_id == root.subject_id`) through the id; not a single-clause restatement.
- `confused_deputy_rejected` (independent content, stated as the attack): an intermediate that signs
  the leaf with a key it was not delegated to (`key_id(leaf_pk) != root.subject_id`) cannot get the
  chain accepted, whatever else it sets. This closes the key-substitution / confused-deputy hole: a
  valid signature under the wrong key does not accept, because the token pins the key.

Caveats on this layer: `key_id` here is the leading 16 bytes of the key (a stand-in for a truncated
hash); the theorems hold for any `key_id`, but a real deployment needs a collision-resistant hash so
`key_id(pk) == id` actually pins `pk`. And the hybrid verify is an assumed spec in Kani (ECDSA/ML-DSA
are too large for CBMC); its soundness is ML-DSA-44/ECDSA unforgeability, exercised for real (with
KATs) in the integration test, not proved here.

## Related work

Cap-V1's design is not novel as a capability model; it sits in a long line and should be read against
it. SPKI/SDSI (RFC 2693) is the closest: authorization certificates with issuer/subject/delegation/
authorization/validity tuples and *tuple reduction* down a chain, which is what `valid_delegation`
composition is. Macaroons (Birgisson et al., 2014) and Biscuit are attenuation-only delegation tokens
(Biscuit is public-key, offline-attenuable). UCAN and ZCAP-LD are capability chains with audience,
expiry, and delegation depth; Cap-V1 is close to a fixed-binary UCAN. On the verification side,
EverParse (Protzenko et al.) and Narcissus (Delaware et al.) already produce machine-checked
non-malleable parsers/serializers for far harder, length-dependent formats, of which a fixed-length
no-optional-field record is the easy subcase.

The only axis where Cap-V1 is potentially new is "hybrid PQ-signed capability token with a
machine-checked verifier in Rust". Per the scope below, that axis is not yet earned: no signature
scheme runs in the verified path. Until it does, the honest description is "a Kani-verified
fixed-format serializer plus a delegation-attenuation checker", which is a smaller and well-populated
claim.

## Domain separation

Cap-V1 and Q-SEAL TBS-V1 both target the HYB-1 suite (ECDSA P-256 + ML-DSA-44), plausibly signed by
the same secure-element key. That is a cross-protocol reuse risk. Separation currently rests only on
the messages differing: Cap-V1 is 191 bytes with a `"CAPV1"` magic, TBS-V1 is 231 bytes with
`"QSEAL"`, so no serialization of one can equal a serialization of the other (different length, and
different 5-byte prefix at the same offset). That argument should be stated explicitly and, for
ML-DSA-44, backed by a FIPS 204 context string (`ctx`, e.g. `"CAP-V1"`) so separation does not depend
on message content alone. ECDSA has no context notion, so its separation rests on the message
argument. None of this is specified in v0.1 yet; it is a required item before any shared-key
deployment.

## Scope and limitations

- **The signature scheme is an assumed spec inside Kani, run for real in an integration test.** In
  the harnesses `sig_ok` / `root_sig_ok` / `leaf_sig_ok` are boolean inputs; ECDSA/ML-DSA are far too
  large for CBMC, so Kani proves the glue (key commitment, message = `serialize(cap)`, both required)
  and treats the verify itself as assumed. `cap/tests/hybrid.rs` (`make cap-hybrid`) discharges that
  assumption with actual crypto: it generates real ECDSA P-256 and ML-DSA-44 keys, signs
  `serialize(cap)`, verifies both, and feeds the outcomes and real key commitments into the same
  verified `accept_chain2_signed`. Valid accepts; tampered, downgrade (only the classical signature
  valid), confused-deputy (valid signature under a non-delegated key), and expired all reject. So a
  real post-quantum signature runs end to end; what stays assumed is only ML-DSA-44/ECDSA
  unforgeability (the ML-DSA-44 primitive itself is verified elsewhere in this repo), which no test
  can establish.
- **Key binding: modeled, with a placeholder commitment.** `accept_leaf_signed` /
  `accept_chain2_signed` now require `key_id(issuer_pk) == cap.issuer_id`, and
  `confused_deputy_rejected` proves a foreign-key signature does not accept. What remains assumed:
  `key_id` is the leading 16 bytes of the key (a stand-in for a truncated collision-resistant hash),
  and the hybrid verify itself is an assumed spec in Kani (run for real in the integration test). So
  the confused-deputy hole is closed relative to those assumptions, not unconditionally.
- **Field-value validation covers `version` and `suite_id` only.** `accept_leaf_checked` /
  `accept_chain_checked` reject unknown versions and suites (machine-checked above), and the plain
  gates are proved over-permissive by a `kani::cover!` witness. `cap_type` and `flags` value sets
  are still provisional, so they remain unvalidated, and no gate calls `well_formed` (the magic is
  a serialization concern; the gates take a parsed `CapV1`). A deployment runs the composed
  `accept_leaf_full` / `accept_chain_full` gates, whose composition is itself machine-checked
  (`full_implies_all_conjuncts`, `full_no_replay`); hand-stacking the `_checked` and `_once`
  variants is not verified and, on the chain path, would drop key binding.
- **Replay is closed on the stateful gates only, and there is still no revocation.**
  `accept_leaf_once` and `accept_chain_once` consume the presented leaf's `cap_id || nonce` on one
  shared bounded (capacity 8), sequential, fail-closed store (limits disclosed above); the plain
  `accept_leaf` / `accept_chain` gates remain replayable, so a deployment must use the composed
  `_full` gates (verified composition; the bare `_once` gates lack field validation and, on the
  chain path, key binding). Single-use is per-presentation anti-replay only: it does not bound how
  many distinct single-use leaves a delegate with remaining depth can mint and have accepted. Nothing revokes a capability before `not_after`. For a capability layer revocation is a
  headline property, not a footnote.
- Chain results are bounded: `accept_chain<N>` is verified at N = 2, 3, 4 (concrete
  instantiations). No machine-checked induction covers all N; longer chains rest on the link-local
  argument.
- Attenuation is proved for `action`, depth, and window; `flags`, `cap_type`, and `constraints_digest`
  are not yet constrained across a link (so those fields can change or weaken).
- The layout is frozen (the bijection depends on it); field *meanings* are provisional.
- `parse` is total and does not check `magic`; `well_formed` is the separate magic check. The byte
  round-trip is stated under `well_formed`.
