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
| 106    | 4   | action               | permitted actions, bitmask / enum                            |
| 110    | 1   | max_depth            | remaining re-delegation depth; 0 = may not re-delegate       |
| 111    | 32  | constraints_digest   | digest binding out-of-band policy constraints                |
| 143    | 8   | not_before           | validity start, unix seconds, big-endian                     |
| 151    | 8   | not_after            | validity end / expiry, unix seconds, big-endian              |
| 159    | 16  | nonce                | freshness / anti-replay                                      |
| 175    | 16  | audience_id          | intended verifier / service; blocks cross-service replay     |
| 191    |     | (end)                |                                                              |

## Signature envelope

Cap-V1 is signature-agnostic. The full token is `serialize(cap) || sig`, where `sig` is produced
over the exact 191 TBS bytes. The intended suite is HYB-1: ECDSA P-256 and ML-DSA-44, both required
(same hybrid, no-downgrade stance as Q-SEAL HYB-1), reusing the ML-DSA-44 primitive this repo
verifies. Signature verification is out of scope for the property below, which is about the TBS
format itself.

## Delegation model (intended, not all machine-checked yet)

- A root capability has `parent_id = 0` and is signed by the resource owner's key.
- A re-delegation sets `parent_id` to the parent's `cap_id`, `issuer_id` to the re-delegating
  agent's key (which must equal the parent's `subject_id`), and `max_depth` to at most parent
  `max_depth - 1`. Its `action` and `resource_id` must not exceed the parent's (attenuation only).
- A verifier accepts a chain if every link's signature verifies, windows are current, the audience
  matches, depth is non-negative down the chain, and each link attenuates the previous.

The chain-link check `valid_delegation(parent, child)` (`cap/src/lib.rs`) is the non-signature part
of this rule, and its attenuation properties are proved below. Signature verification and freshness
enforcement are still separate, upcoming targets.

## Machine-checked properties (this session, Kani)

`cap/src/lib.rs`, harnesses under `#[cfg(kani)] mod verification`, run with `cargo kani` (or
`make cap-kani`). Kani 0.67.0, CBMC backend. All eleven verified, 0 failures. `any_cap()` is
`parse(kani::any::<[u8; 191]>())`, which ranges over all `CapV1` (each field is an independent slice
of a fully symbolic buffer).

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
- `link_no_escalation`: `valid_delegation(p, c) => action_bits(c) & !action_bits(p) == 0`. A valid
  re-delegation grants no action bit the parent lacks.
- `link_depth_decreases`: `valid_delegation(p, c) => c.max_depth < p.max_depth`. Depth strictly
  drops at every link, so any chain terminates.
- `chain_attenuates` (two-hop composition): if `valid_delegation(a, b)` and `valid_delegation(b, c)`
  then `c`'s action bits are a subset of `a`'s, `c.max_depth < a.max_depth`, `c`'s validity window
  is inside `a`'s, and resource and audience are unchanged. The local link check composes into the
  global invariant (authority only attenuates down the chain); two hops discharge the inductive step
  for any length.

Accept gate (`accept_leaf(cap, verifier_id, now, sig_ok)`). `sig_ok` is the signature-check outcome,
kept as an input so the guarantees hold for any correct verifier (Q-SEAL's uninterpreted-verifier
device):

- `accept_reachable`: `accept_leaf` is satisfiable (`kani::cover!`, SATISFIED).
- `accept_requires_signature`: `!accept_leaf(cap, v, now, false)`. Nothing is accepted without a
  valid signature; the check cannot be bypassed.
- `accept_binds_audience`: `accept_leaf(cap, v, now, s) => cap.audience_id == v`. A capability
  accepted by verifier `v` was issued for `v` (no cross-service replay).
- `accept_within_window`: `accept_leaf(cap, v, now, s) => not_before <= now <= not_after`. No
  expired or not-yet-valid capability is accepted.

## Scope and limitations

- The proved properties are the format bijection, the attenuation behavior of `valid_delegation`,
  and the structure of the single-capability accept gate. The signature check is abstract (`sig_ok`
  is an input), so nothing here proves ECDSA/ML-DSA correctness; it proves that acceptance is
  gated on the signature bit plus audience and window, for any correct verifier.
- Not yet connected: `valid_delegation` (chains) and `accept_leaf` (single capability with the
  signature bit) are not composed into one chain-accept decision that requires every link's
  signature to verify. That is the next target.
- Freshness/replay beyond the validity window (nonce single-use, like Q-SEAL property 4) is not
  modeled here.
- The layout is frozen (the bijection depends on it); field *meanings* above are provisional and may
  change without invalidating the proof technique.
- `parse` is total and does not check `magic`; `well_formed` is the separate magic check. A
  production verifier rejects a bad prefix before parsing. The byte round-trip is stated under
  `well_formed`.
