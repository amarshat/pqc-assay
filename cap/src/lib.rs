//! Cap-V1: the to-be-signed (TBS) core of a post-quantum agent-delegation capability token.
//!
//! A Cap-V1 TBS is a fixed-length (191 byte) record with no optional fields and no variable
//! encodings. It states, in canonical bytes, that one agent (`issuer_id`) delegates a specific
//! `action` over a specific `resource_id` to another agent (`subject_id`), bounded by validity
//! window, audience, and a re-delegation depth. The full token on the wire is `serialize(cap)`
//! followed by the signature(s); the signature covers exactly these bytes.
//!
//! The property this module exists to establish, machine-checked with Kani, is that the
//! serializer is a bijection on its byte encoding, hence injective: two distinct capabilities can
//! never produce the same signed bytes. That removes token-level malleability by construction. It
//! is the structural opposite of a non-fixed, validation-dependent decode (the class of bug behind
//! CVE-2026-24850's hint decoder, where non-canonical inputs were admitted). Q-SEAL proves the same
//! shape of property for its TBS-V1 transcript in Cryptol/SAW; this is the Rust/Kani analogue, which
//! also exercises real slice access in the parser.
//!
//! `serialize`/`parse` are total and use only fixed-offset, constant-size slice copies (no loops,
//! no length-dependent branches), so Kani discharges the round-trip goals by bounded symbolic
//! execution over the 191-byte buffer.

/// Fixed 5-byte magic prefix. Not part of the variable record; it tags the wire format.
pub const MAGIC: [u8; 5] = *b"CAPV1";

/// Total serialized length of a Cap-V1 TBS, in bytes.
pub const WIRE_LEN: usize = 191;

/// The variable fields of a Cap-V1 capability (everything after the fixed magic prefix), each a
/// fixed-length byte array. Field order and length are the wire layout; see `serialize`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CapV1 {
    /// Format version. 1 for this layout.
    pub version: [u8; 1],
    /// Cryptographic suite id (e.g. HYB-1 = ECDSA P-256 + ML-DSA-44).
    pub suite_id: [u8; 2],
    /// Capability kind / token type.
    pub cap_type: [u8; 1],
    /// Flag bits (e.g. bit0 = further delegation permitted).
    pub flags: [u8; 1],
    /// Delegator: key id of the agent granting this capability.
    pub issuer_id: [u8; 16],
    /// Delegate: key id of the agent that bears / may exercise this capability.
    pub subject_id: [u8; 16],
    /// Id of the parent capability in the delegation chain. All-zero for a root capability.
    pub parent_id: [u8; 16],
    /// Unique id of this capability.
    pub cap_id: [u8; 16],
    /// Digest of the resource / object the capability is over.
    pub resource_id: [u8; 32],
    /// Permitted actions, as a bitmask / enum.
    pub action: [u8; 4],
    /// Remaining re-delegation depth. 0 means this capability may not be re-delegated further.
    pub max_depth: [u8; 1],
    /// Digest binding any additional out-of-band policy constraints.
    pub constraints_digest: [u8; 32],
    /// Validity start, unix seconds, big-endian.
    pub not_before: [u8; 8],
    /// Validity end / expiry, unix seconds, big-endian.
    pub not_after: [u8; 8],
    /// Freshness / anti-replay value.
    pub nonce: [u8; 16],
    /// Intended audience: the verifier / service this capability may be presented to. Binding it
    /// stops a captured token from being replayed against a different service.
    pub audience_id: [u8; 16],
}

impl CapV1 {
    /// An all-zero capability. Used as the target of `parse`'s fixed-offset copies.
    pub const fn zeroed() -> Self {
        CapV1 {
            version: [0; 1],
            suite_id: [0; 2],
            cap_type: [0; 1],
            flags: [0; 1],
            issuer_id: [0; 16],
            subject_id: [0; 16],
            parent_id: [0; 16],
            cap_id: [0; 16],
            resource_id: [0; 32],
            action: [0; 4],
            max_depth: [0; 1],
            constraints_digest: [0; 32],
            not_before: [0; 8],
            not_after: [0; 8],
            nonce: [0; 16],
            audience_id: [0; 16],
        }
    }
}

// Cumulative byte offsets after the 5-byte magic prefix. Each field starts where the previous ended.
const O_VERSION: usize = 5;
const O_SUITE_ID: usize = 6;
const O_CAP_TYPE: usize = 8;
const O_FLAGS: usize = 9;
const O_ISSUER_ID: usize = 10;
const O_SUBJECT_ID: usize = 26;
const O_PARENT_ID: usize = 42;
const O_CAP_ID: usize = 58;
const O_RESOURCE_ID: usize = 74;
const O_ACTION: usize = 106;
const O_MAX_DEPTH: usize = 110;
const O_CONSTRAINTS: usize = 111;
const O_NOT_BEFORE: usize = 143;
const O_NOT_AFTER: usize = 151;
const O_NONCE: usize = 159;
const O_AUDIENCE_ID: usize = 175;
const O_END: usize = 191;

/// Serialize a capability to its canonical 191-byte TBS: magic prefix, then each field at its fixed
/// offset. This is exactly the byte string a signer signs.
pub fn serialize(c: &CapV1) -> [u8; WIRE_LEN] {
    let mut b = [0u8; WIRE_LEN];
    b[0..O_VERSION].copy_from_slice(&MAGIC);
    b[O_VERSION..O_SUITE_ID].copy_from_slice(&c.version);
    b[O_SUITE_ID..O_CAP_TYPE].copy_from_slice(&c.suite_id);
    b[O_CAP_TYPE..O_FLAGS].copy_from_slice(&c.cap_type);
    b[O_FLAGS..O_ISSUER_ID].copy_from_slice(&c.flags);
    b[O_ISSUER_ID..O_SUBJECT_ID].copy_from_slice(&c.issuer_id);
    b[O_SUBJECT_ID..O_PARENT_ID].copy_from_slice(&c.subject_id);
    b[O_PARENT_ID..O_CAP_ID].copy_from_slice(&c.parent_id);
    b[O_CAP_ID..O_RESOURCE_ID].copy_from_slice(&c.cap_id);
    b[O_RESOURCE_ID..O_ACTION].copy_from_slice(&c.resource_id);
    b[O_ACTION..O_MAX_DEPTH].copy_from_slice(&c.action);
    b[O_MAX_DEPTH..O_CONSTRAINTS].copy_from_slice(&c.max_depth);
    b[O_CONSTRAINTS..O_NOT_BEFORE].copy_from_slice(&c.constraints_digest);
    b[O_NOT_BEFORE..O_NOT_AFTER].copy_from_slice(&c.not_before);
    b[O_NOT_AFTER..O_NONCE].copy_from_slice(&c.not_after);
    b[O_NONCE..O_AUDIENCE_ID].copy_from_slice(&c.nonce);
    b[O_AUDIENCE_ID..O_END].copy_from_slice(&c.audience_id);
    b
}

/// Parse a 191-byte TBS into a capability by reading each field from its fixed slice. Total: it
/// does not validate the magic (see `well_formed`); it recovers whatever bytes are present.
pub fn parse(b: &[u8; WIRE_LEN]) -> CapV1 {
    let mut c = CapV1::zeroed();
    c.version.copy_from_slice(&b[O_VERSION..O_SUITE_ID]);
    c.suite_id.copy_from_slice(&b[O_SUITE_ID..O_CAP_TYPE]);
    c.cap_type.copy_from_slice(&b[O_CAP_TYPE..O_FLAGS]);
    c.flags.copy_from_slice(&b[O_FLAGS..O_ISSUER_ID]);
    c.issuer_id.copy_from_slice(&b[O_ISSUER_ID..O_SUBJECT_ID]);
    c.subject_id.copy_from_slice(&b[O_SUBJECT_ID..O_PARENT_ID]);
    c.parent_id.copy_from_slice(&b[O_PARENT_ID..O_CAP_ID]);
    c.cap_id.copy_from_slice(&b[O_CAP_ID..O_RESOURCE_ID]);
    c.resource_id.copy_from_slice(&b[O_RESOURCE_ID..O_ACTION]);
    c.action.copy_from_slice(&b[O_ACTION..O_MAX_DEPTH]);
    c.max_depth.copy_from_slice(&b[O_MAX_DEPTH..O_CONSTRAINTS]);
    c.constraints_digest.copy_from_slice(&b[O_CONSTRAINTS..O_NOT_BEFORE]);
    c.not_before.copy_from_slice(&b[O_NOT_BEFORE..O_NOT_AFTER]);
    c.not_after.copy_from_slice(&b[O_NOT_AFTER..O_NONCE]);
    c.nonce.copy_from_slice(&b[O_NONCE..O_AUDIENCE_ID]);
    c.audience_id.copy_from_slice(&b[O_AUDIENCE_ID..O_END]);
    c
}

/// A byte string carries the Cap-V1 magic prefix.
pub fn well_formed(b: &[u8; WIRE_LEN]) -> bool {
    b[0..O_VERSION] == MAGIC
}

/// The 4-byte action field read as a bitmask.
pub fn action_bits(c: &CapV1) -> u32 {
    u32::from_be_bytes(c.action)
}

/// The validity window `(not_before, not_after)` in unix seconds.
pub fn window(c: &CapV1) -> (u64, u64) {
    (u64::from_be_bytes(c.not_before), u64::from_be_bytes(c.not_after))
}

/// The verifier's chain-link check: is `child` a well-formed re-delegation of `parent`?
///
/// This is where a chain either attenuates or is rejected. It enforces, at one link: only the
/// parent's delegate may re-delegate (`issuer == parent.subject`), the link is explicit
/// (`parent_id == parent.cap_id`), the target does not change (same resource, audience, suite), the
/// re-delegation budget strictly decreases (`max_depth` down, parent still had budget), authority
/// only narrows (child action bits are a subset of the parent's), and the validity window narrows
/// and stays non-empty. The Kani harnesses prove that this local check composes: down any chain,
/// authority can only shrink and depth must reach zero (so chains terminate).
pub fn valid_delegation(parent: &CapV1, child: &CapV1) -> bool {
    let (p_nb, p_na) = window(parent);
    let (c_nb, c_na) = window(child);
    child.issuer_id == parent.subject_id
        && child.parent_id == parent.cap_id
        && child.resource_id == parent.resource_id
        && child.audience_id == parent.audience_id
        && child.suite_id == parent.suite_id
        && parent.max_depth[0] > 0
        && child.max_depth[0] < parent.max_depth[0]
        && (action_bits(child) & !action_bits(parent)) == 0
        && c_nb >= p_nb
        && c_na <= p_na
        && c_nb <= c_na
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_roundtrip() {
        let c = CapV1 {
            version: [1],
            suite_id: [0, 1],
            cap_type: [7],
            flags: [1],
            issuer_id: [0x11; 16],
            subject_id: [0x22; 16],
            parent_id: [0; 16],
            cap_id: [0x33; 16],
            resource_id: [0x44; 32],
            action: [0, 0, 0, 5],
            max_depth: [3],
            constraints_digest: [0x55; 32],
            not_before: [0, 0, 0, 0, 0, 0, 0, 10],
            not_after: [0, 0, 0, 0, 0, 0, 0, 20],
            nonce: [0x66; 16],
            audience_id: [0x77; 16],
        };
        let b = serialize(&c);
        assert!(well_formed(&b));
        assert_eq!(parse(&b), c);
        assert_eq!(&b[0..5], b"CAPV1");
    }

    #[test]
    fn concrete_valid_delegation() {
        // A root capability with two action bits and depth budget 3.
        let mut parent = CapV1::zeroed();
        parent.subject_id = [0xAA; 16];
        parent.cap_id = [0xBB; 16];
        parent.resource_id = [0x44; 32];
        parent.audience_id = [0x77; 16];
        parent.suite_id = [0, 1];
        parent.max_depth = [3];
        parent.action = [0, 0, 0, 0b0000_0011];
        parent.not_before = 100u64.to_be_bytes();
        parent.not_after = 200u64.to_be_bytes();

        // A valid re-delegation: issued by the parent's delegate, links back, drops one action bit,
        // narrows the window, decrements depth.
        let mut child = CapV1::zeroed();
        child.issuer_id = parent.subject_id;
        child.subject_id = [0xCC; 16];
        child.parent_id = parent.cap_id;
        child.resource_id = parent.resource_id;
        child.audience_id = parent.audience_id;
        child.suite_id = parent.suite_id;
        child.max_depth = [2];
        child.action = [0, 0, 0, 0b0000_0001];
        child.not_before = 120u64.to_be_bytes();
        child.not_after = 180u64.to_be_bytes();

        assert!(valid_delegation(&parent, &child));

        // Escalating the action back to a bit the parent lacks is rejected.
        let mut escalate = child;
        escalate.action = [0, 0, 0, 0b0000_0111];
        assert!(!valid_delegation(&parent, &escalate));

        // Not decreasing depth is rejected.
        let mut same_depth = child;
        same_depth.max_depth = [3];
        assert!(!valid_delegation(&parent, &same_depth));
    }
}

/// Kani proof harnesses. Run with `cargo kani`. These establish, by bounded symbolic execution over
/// the full 191-byte buffer, that the Cap-V1 serializer is a bijection on its encoding and hence
/// injective: no two distinct capabilities share signed bytes.
#[cfg(kani)]
mod verification {
    use super::*;

    /// An arbitrary capability: every field is an independent slice of a fully symbolic buffer, so
    /// this ranges over all `CapV1` values.
    fn any_cap() -> CapV1 {
        parse(&kani::any::<[u8; WIRE_LEN]>())
    }

    /// The chain-link check is satisfiable (the delegation properties below are not vacuous).
    #[kani::proof]
    fn link_reachable() {
        let p = any_cap();
        let c = any_cap();
        kani::cover!(valid_delegation(&p, &c));
    }

    /// No privilege escalation at a link: a valid re-delegation grants no action bit the parent
    /// lacks.
    #[kani::proof]
    fn link_no_escalation() {
        let p = any_cap();
        let c = any_cap();
        kani::assume(valid_delegation(&p, &c));
        assert_eq!(action_bits(&c) & !action_bits(&p), 0);
    }

    /// Chains terminate: a valid re-delegation strictly decreases the re-delegation depth.
    #[kani::proof]
    fn link_depth_decreases() {
        let p = any_cap();
        let c = any_cap();
        kani::assume(valid_delegation(&p, &c));
        assert!(c.max_depth[0] < p.max_depth[0]);
    }

    /// Two-hop composition: if `a` delegates to `b` and `b` to `c`, then `c`'s authority is within
    /// `a`'s (action subset, narrower window), its depth is strictly below `a`'s, and the resource
    /// and audience are unchanged. The local link check composes into the global chain invariant:
    /// authority only attenuates down the chain. Proving it at two hops discharges the inductive
    /// step for any length.
    #[kani::proof]
    fn chain_attenuates() {
        let a = any_cap();
        let b = any_cap();
        let c = any_cap();
        kani::assume(valid_delegation(&a, &b));
        kani::assume(valid_delegation(&b, &c));
        assert_eq!(action_bits(&c) & !action_bits(&a), 0);
        assert!(c.max_depth[0] < a.max_depth[0]);
        let (a_nb, a_na) = window(&a);
        let (c_nb, c_na) = window(&c);
        assert!(c_nb >= a_nb && c_na <= a_na);
        assert_eq!(c.resource_id, a.resource_id);
        assert_eq!(c.audience_id, a.audience_id);
    }

    /// Round-trip on records: parsing a serialized capability recovers it exactly, for every
    /// capability. `parse(any_bytes)` ranges over all `CapV1` values because every field is an
    /// independent slice of the fully symbolic buffer, so this quantifies over all capabilities.
    #[kani::proof]
    fn roundtrip_parse_serialize() {
        let b: [u8; WIRE_LEN] = kani::any();
        let c = parse(&b);
        assert_eq!(parse(&serialize(&c)), c);
    }

    /// Round-trip on bytes: any well-formed byte string is exactly what serializing its parse gives.
    #[kani::proof]
    fn roundtrip_serialize_parse() {
        let b: [u8; WIRE_LEN] = kani::any();
        kani::assume(well_formed(&b));
        assert_eq!(serialize(&parse(&b)), b);
    }

    /// Injectivity: distinct capabilities never collide on the wire. No token-level malleability.
    #[kani::proof]
    fn serialize_injective() {
        let b1: [u8; WIRE_LEN] = kani::any();
        let b2: [u8; WIRE_LEN] = kani::any();
        let c1 = parse(&b1);
        let c2 = parse(&b2);
        kani::assume(serialize(&c1) == serialize(&c2));
        assert_eq!(c1, c2);
    }
}
