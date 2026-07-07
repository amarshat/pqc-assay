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
`make cap-kani`). Kani 0.67.0, CBMC backend. All seventeen verified, 0 failures. `any_cap()` is
`parse(kani::any::<[u8; 191]>())`, which ranges over all `CapV1` (each field is an independent slice
of a fully symbolic buffer).

Not all seventeen carry equal weight, and the count should not be read as "seventeen independent
theorems". The honest taxonomy:
- Independent content: the format bijection/injectivity (`roundtrip_*`, `serialize_injective`), the
  two-hop `chain_attenuates` (a real transitivity result), and `omitting_audience_breaks_binding`
  (a mutation witness that a plausible bug would be caught).
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
  local check across two links (subset, `<`, and interval-containment are transitive). It is a
  two-hop lemma only: the general N-link invariant is **not** stated and no induction is run. The
  transitive step is sound, so the extension is conjectured, not machine-checked.

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

- **No signature scheme runs in the verified path.** `sig_ok` / `root_sig_ok` / `leaf_sig_ok` are
  free boolean inputs; no ECDSA or ML-DSA is executed in any harness, so nothing "post-quantum" is
  machine-checked here. The accept/chain theorems say "acceptance is gated on a signature bit plus
  audience, window, and attenuation", which holds for any scheme or none. The ML-DSA-44 primitive is
  verified elsewhere in this repo; wiring a real verify over `serialize(cap)` into the accept path is
  open, and until it is done the "post-quantum" framing is aspirational, not proved.
- **No key binding.** `issuer_id` / `subject_id` are opaque 16-byte ids compared by byte equality;
  nothing ties them to the public key that produced a signature. So the chain guarantees are
  conditional on an unmodeled `issuer_id -> key -> signature` binding. Without it, a malicious
  intermediate can set `issuer_id = parent.subject_id` (a public value) and sign with its own key.
  Closing this is the main prerequisite for the "delegation" claim to be sound.
- **The accept path validates no field values.** `accept_leaf` / `accept_chain2` / `valid_delegation`
  do not call `well_formed` and do not check `version`, `suite_id`, or `cap_type` ranges. The object
  the theorems are about is thus not a deployment verifier, which would reject unknown version/suite.
  Q-SEAL has a dedicated property for this; Cap-V1 does not yet.
- **No revocation, and replay within the window is allowed.** The `nonce` field is never consumed, so
  a valid token replays freely to its audience for the whole validity window; there is no revocation
  before `not_after`. For a capability layer these are headline properties, not footnotes.
- `accept_chain2` covers a two-link chain only; the general N-link result is conjectured (see
  `chain_attenuates`), not machine-checked.
- Attenuation is proved for `action`, depth, and window; `flags`, `cap_type`, and `constraints_digest`
  are not yet constrained across a link (so those fields can change or weaken).
- The layout is frozen (the bijection depends on it); field *meanings* are provisional.
- `parse` is total and does not check `magic`; `well_formed` is the separate magic check. The byte
  round-trip is stated under `well_formed`.
