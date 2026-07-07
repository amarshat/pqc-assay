# Cap-V1 capability layer (Rust verifier, Kani-proved)

Cap-V1 is the to-be-signed core of a post-quantum agent-delegation capability token: a fixed-length
(191 byte) record where one agent delegates a specific action over a specific resource to another,
bounded by validity window, audience, and re-delegation depth. The full token is the TBS followed by
its signature(s), signed with the ML-DSA-44 primitive this repo verifies (hybrid HYB-1: ECDSA P-256
+ ML-DSA-44). Format spec: [`../docs/cap/CAP-V1.md`](../docs/cap/CAP-V1.md).

This directory is the Rust verifier and its first machine-checked property. The rest of the repo
proves ML-DSA-44 arithmetic (SAW/Isabelle) and Q-SEAL protocol properties (Cryptol/SAW/ProVerif);
Cap-V1 is the "verified Rust" track, so the proof tool is Kani (CBMC), not SMT over a Cryptol model.

## Verified so far (Kani 0.67, this repo)

`make cap-kani` (or `cargo kani` in this directory) checks seven harnesses in `src/lib.rs`, all
verified with 0 failures.

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

## Layout

Byte-exact layout is in the spec. `src/lib.rs` is the single source: `CapV1`, `serialize`, `parse`,
`well_formed`, plus the `#[cfg(kani)]` harnesses. No dependencies, so the trusted path pulls in no
unverified third-party code.

## Scope

Proved: the format bijection, `valid_delegation` attenuation, the leaf accept gate, and a two-link
chain accept that requires both signatures and never exceeds the root grant. The signature check is
abstract (a bool input), so a real ECDSA/ML-DSA verifier over `serialize(cap)` is not wired in yet;
N-link (N > 2) chain accept and nonce single-use replay are not stated. Next Kani targets. See the
spec's scope section.

## Run

    make cap-kani        # from repo root
    cargo kani           # from this directory
    cargo test           # concrete round-trip sanity, no proof toolchain needed
