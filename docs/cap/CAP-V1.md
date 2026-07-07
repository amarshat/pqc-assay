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

Only the format-level property below is proved so far. The chain rules (attenuation, depth
monotonicity, audience binding) are the next Kani targets.

## Machine-checked property (this session, Kani)

`cap/src/lib.rs`, harnesses under `#[cfg(kani)] mod verification`, run with `cargo kani` (or
`make cap-kani`). Kani 0.67.0, CBMC backend. All three verified, 0 failures:

- `roundtrip_parse_serialize` (record round-trip): `parse(serialize(c)) == c` for every capability
  `c`. Quantified over all `CapV1` by letting `c = parse(b)` with `b` a fully symbolic 191-byte
  buffer, so each field ranges freely.
- `roundtrip_serialize_parse` (byte round-trip): `well_formed(b) => serialize(parse(b)) == b` for
  every well-formed 191-byte string.
- `serialize_injective`: `serialize(c1) == serialize(c2) => c1 == c2`. No two distinct capabilities
  share signed bytes.

Together: the serializer is a bijection between `CapV1` and well-formed 191-byte strings, hence
injective. The parser uses only fixed-offset, constant-size slice copies, so the harnesses also
exercise real slice access under Kani (no panics, no out-of-bounds), which is the "verified Rust"
claim made concrete.

## Scope and limitations

- Format only. This says nothing about signatures, freshness enforcement, chain attenuation, or
  authorization decisions. Those are separate properties.
- The layout is frozen (the bijection depends on it); field *meanings* above are provisional and may
  change without invalidating the proof technique.
- `parse` is total and does not check `magic`; `well_formed` is the separate magic check. A
  production verifier rejects a bad prefix before parsing. The byte round-trip is stated under
  `well_formed`.
