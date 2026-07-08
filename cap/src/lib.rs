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

/// Accept a single (leaf) capability presented to a verifier.
///
/// `sig_ok` is the outcome of the signature check over `serialize(cap)`. It is an input, not
/// computed here: the real verifier runs the hybrid ECDSA P-256 + ML-DSA-44 check, but keeping it
/// abstract means the structural guarantees below hold for any correct signature verifier (the same
/// device Q-SEAL uses for its uninterpreted verifiers). Acceptance additionally requires the
/// capability to name this verifier as its audience and `now` to fall inside the validity window.
pub fn accept_leaf(cap: &CapV1, verifier_id: &[u8; 16], now: u64, sig_ok: bool) -> bool {
    // `sig_ok` is the verifier's verdict over `signed_message(cap)`, i.e. the signature checked over
    // exactly the canonical TBS bytes. See `signed_message`.
    let (nb, na) = window(cap);
    sig_ok && cap.audience_id == *verifier_id && nb <= now && now <= na
}

/// The exact bytes a Cap-V1 signature must cover: the canonical 191-byte serialization. A verifier
/// checks the signature over precisely these bytes and nothing else.
///
/// Two facts about this message are machine-checked below: it covers every field of the capability
/// (`parse(signed_message(cap)) == cap`, so nothing authorized is left unsigned), and it is unique
/// to the capability (`serialize` is injective, so distinct capabilities never share signed bytes).
/// Given those, ML-DSA-44 unforgeability over this message transfers to the capability: a signature
/// that verifies for one capability's bytes is not valid over any other capability's bytes. That
/// last step is a reduction to the signature scheme's security, not proved here (the ML-DSA-44
/// primitive is verified elsewhere in this repo); see docs/cap/CAP-V1.md.
pub fn signed_message(cap: &CapV1) -> [u8; WIRE_LEN] {
    serialize(cap)
}

/// A hybrid public key. In HYB-1 this is an ECDSA P-256 point plus an ML-DSA-44 public key; here we
/// keep only what the verified glue needs, its bytes, since the binding theorems are about the key's
/// identity commitment, not its internal structure. The real key material is exercised in the
/// integration test (`cap/tests/hybrid.rs`), which runs actual ECDSA + ML-DSA over `serialize(cap)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct PublicKey {
    pub bytes: [u8; 32],
}

/// The 16-byte id a public key commits to, i.e. how `issuer_id` / `subject_id` are derived from a
/// key. In deployment this is a hash of the encoded hybrid key, truncated; here it is the leading 16
/// bytes, a stand-in. The key-binding theorems hold for any `key_id` (they are about the commitment,
/// not the hash), so the choice does not weaken them; a real deployment must use a collision-
/// resistant hash so that `key_id(pk) == id` pins `pk`.
pub fn key_id(pk: &PublicKey) -> [u8; 16] {
    let mut id = [0u8; 16];
    id.copy_from_slice(&pk.bytes[0..16]);
    id
}

/// Accept a single capability, now with the signer's key bound to the token.
///
/// `sig_ok` is the outcome of the real hybrid verify over `signed_message(cap)` under `issuer_pk`
/// (ECDSA P-256 and ML-DSA-44, both required). Kani does not run that check (ECDSA/ML-DSA are far too
/// large for CBMC); it is an assumed spec here and is exercised for real in `cap/tests/hybrid.rs`.
/// What this function adds over `accept_leaf` is the key commitment: the capability names its issuer
/// (`issuer_id`), and acceptance requires the presented key to be exactly that named key
/// (`key_id(issuer_pk) == cap.issuer_id`). So a signature under some other key does not accept, even
/// if valid: the token says who must sign.
pub fn accept_leaf_signed(
    cap: &CapV1,
    verifier_id: &[u8; 16],
    now: u64,
    issuer_pk: &PublicKey,
    sig_ok: bool,
) -> bool {
    key_id(issuer_pk) == cap.issuer_id && accept_leaf(cap, verifier_id, now, sig_ok)
}

/// Accept a two-link chain with both signers' keys bound to the tokens. Each link's signature must
/// verify under the key the link names as its issuer, and `leaf` must be a valid re-delegation of the
/// `root`. As with `accept_leaf_signed`, the `*_sig_ok` bits are the assumed outcomes of the real
/// hybrid verify over each link's `signed_message`, run for real in the integration test.
pub fn accept_chain2_signed(
    root: &CapV1,
    leaf: &CapV1,
    verifier_id: &[u8; 16],
    now: u64,
    root_pk: &PublicKey,
    root_sig_ok: bool,
    leaf_pk: &PublicKey,
    leaf_sig_ok: bool,
) -> bool {
    is_root(root)
        && key_id(root_pk) == root.issuer_id
        && root_sig_ok
        && valid_delegation(root, leaf)
        && key_id(leaf_pk) == leaf.issuer_id
        && leaf_sig_ok
        && accept_leaf(leaf, verifier_id, now, leaf_sig_ok)
}

/// Accept an N-link delegation chain: `caps[0]` is the root, each `caps[i]` is a re-delegation of
/// `caps[i-1]`, and `caps[N-1]` is the leaf actually presented. `sigs_ok[i]` is the signature-check
/// outcome for link `i` (abstract, as in `accept_leaf`). Acceptance requires: the first link is a
/// root, every link's signature verifies, every adjacent pair passes `valid_delegation`, and the
/// leaf passes the accept gate. `accept_chain2` is exactly the `N = 2` instance (machine-checked
/// below). `N` is a compile-time length, so the loops fully unroll; the Kani harnesses verify the
/// chain properties at concrete lengths (currently up to 4), not for all `N` at once.
pub fn accept_chain<const N: usize>(
    caps: &[CapV1; N],
    verifier_id: &[u8; 16],
    now: u64,
    sigs_ok: &[bool; N],
) -> bool {
    if N == 0 || !is_root(&caps[0]) {
        return false;
    }
    let mut i = 0;
    while i < N {
        if !sigs_ok[i] {
            return false;
        }
        i += 1;
    }
    let mut i = 1;
    while i < N {
        if !valid_delegation(&caps[i - 1], &caps[i]) {
            return false;
        }
        i += 1;
    }
    accept_leaf(&caps[N - 1], verifier_id, now, sigs_ok[N - 1])
}

/// Accept an N-link chain with every signer's key bound to its token: link `i`'s signature must
/// verify under `pks[i]`, and `pks[i]` must be the key the token names as issuer
/// (`key_id(pks[i]) == caps[i].issuer_id`). Combined with `valid_delegation`'s
/// `issuer == parent.subject`, this pins each link's signer to the agent the previous link delegated
/// to. `accept_chain2_signed` is exactly the `N = 2` instance (machine-checked below).
pub fn accept_chain_signed<const N: usize>(
    caps: &[CapV1; N],
    verifier_id: &[u8; 16],
    now: u64,
    pks: &[PublicKey; N],
    sigs_ok: &[bool; N],
) -> bool {
    let mut i = 0;
    while i < N {
        if key_id(&pks[i]) != caps[i].issuer_id {
            return false;
        }
        i += 1;
    }
    accept_chain(caps, verifier_id, now, sigs_ok)
}

/// Capacity of the bounded used-token store. Fixed so the replay properties are checkable by
/// bounded symbolic execution (the same device as Q-SEAL's CAP=8 challenge store). The store logic
/// does not depend on the value; the theorems are proved at this capacity, not for all capacities.
pub const STORE_CAP: usize = 8;

/// The replay key of a capability: `cap_id || nonce` (32 bytes). One verifier owns one store, and
/// audience binding (`accept_leaf`) already stops cross-verifier presentation, so the key does not
/// need a verifier component the way Q-SEAL's challenge key does.
pub fn replay_key(cap: &CapV1) -> [u8; 32] {
    let mut k = [0u8; 32];
    k[0..16].copy_from_slice(&cap.cap_id);
    k[16..32].copy_from_slice(&cap.nonce);
    k
}

/// A verifier's used-token store: an append-only log of consumed replay keys. Bounded at
/// `STORE_CAP`; when full, acceptance fails closed (a denial-of-service footgun, disclosed in the
/// spec's scope section, not a feature). `len` beyond `STORE_CAP` is treated as full.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct NonceStore {
    pub used: [[u8; 32]; STORE_CAP],
    pub len: usize,
}

impl NonceStore {
    pub const fn empty() -> Self {
        NonceStore { used: [[0u8; 32]; STORE_CAP], len: 0 }
    }
}

/// Is `key` already consumed? Scans only the live prefix `used[0..len]`.
pub fn store_contains(store: &NonceStore, key: &[u8; 32]) -> bool {
    let n = if store.len > STORE_CAP { STORE_CAP } else { store.len };
    let mut i = 0;
    while i < n {
        if store.used[i] == *key {
            return true;
        }
        i += 1;
    }
    false
}

/// Accept a leaf capability at most once: the leaf gate (`accept_leaf`) plus single-use. Returns
/// the verdict and the successor store; on acceptance the capability's replay key is appended, so
/// presenting the same token again rejects. Rejects (fail closed) if the key is already consumed or
/// the store is full. This is the stateful gate; `accept_leaf` alone allows unlimited replay to the
/// same audience inside the window.
pub fn accept_leaf_once(
    cap: &CapV1,
    verifier_id: &[u8; 16],
    now: u64,
    sig_ok: bool,
    store: &NonceStore,
) -> (bool, NonceStore) {
    let key = replay_key(cap);
    if !accept_leaf(cap, verifier_id, now, sig_ok)
        || store_contains(store, &key)
        || store.len >= STORE_CAP
    {
        return (false, *store);
    }
    let mut next = *store;
    next.used[next.len] = key;
    next.len += 1;
    (true, next)
}

/// A deliberately broken variant that forgets to consume: it checks the store but returns it
/// unchanged, so a replayed token accepts again. Used only to witness that the no-replay theorem
/// has content (the mutation device of the repo's other tracks). Not part of the shipped API.
#[cfg(any(test, kani))]
fn accept_leaf_once_noconsume(
    cap: &CapV1,
    verifier_id: &[u8; 16],
    now: u64,
    sig_ok: bool,
    store: &NonceStore,
) -> (bool, NonceStore) {
    let key = replay_key(cap);
    if !accept_leaf(cap, verifier_id, now, sig_ok)
        || store_contains(store, &key)
        || store.len >= STORE_CAP
    {
        return (false, *store);
    }
    (true, *store)
}

/// A deliberately broken signer that leaves `audience_id` out of the signed region (zeros it). Used
/// only to witness that field coverage is not vacuous: under this version a capability's audience
/// could be swapped after signing. Not part of the shipped API.
#[cfg(any(test, kani))]
fn signed_message_omitting_audience(cap: &CapV1) -> [u8; WIRE_LEN] {
    let mut b = serialize(cap);
    let mut i = O_AUDIENCE_ID;
    while i < O_END {
        b[i] = 0;
        i += 1;
    }
    b
}

/// A capability is a chain root: it has no parent.
pub fn is_root(cap: &CapV1) -> bool {
    cap.parent_id == [0u8; 16]
}

/// Accept a two-link chain: a root capability `root` and a re-delegation `leaf` of it, presented to
/// `verifier_id` at `now`. `root_sig_ok` / `leaf_sig_ok` are the two signature-check outcomes
/// (abstract, as in `accept_leaf`). Acceptance requires: `root` is a root, both signatures verify,
/// `leaf` is a valid re-delegation of `root`, and `leaf` passes the leaf accept gate (audience +
/// window). Because `valid_delegation` narrows the window and preserves audience, the leaf gate plus
/// the link check imply the root's own window and audience hold too, so they need not be rechecked.
pub fn accept_chain2(
    root: &CapV1,
    leaf: &CapV1,
    verifier_id: &[u8; 16],
    now: u64,
    root_sig_ok: bool,
    leaf_sig_ok: bool,
) -> bool {
    is_root(root)
        && root_sig_ok
        && valid_delegation(root, leaf)
        && accept_leaf(leaf, verifier_id, now, leaf_sig_ok)
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

    #[test]
    fn concrete_accept_leaf() {
        let mut cap = CapV1::zeroed();
        cap.audience_id = [0x77; 16];
        cap.not_before = 100u64.to_be_bytes();
        cap.not_after = 200u64.to_be_bytes();
        let v = [0x77; 16];

        assert!(accept_leaf(&cap, &v, 150, true));
        // No valid signature: rejected.
        assert!(!accept_leaf(&cap, &v, 150, false));
        // Wrong audience: rejected.
        assert!(!accept_leaf(&cap, &[0x88; 16], 150, true));
        // Expired / not yet valid: rejected.
        assert!(!accept_leaf(&cap, &v, 250, true));
        assert!(!accept_leaf(&cap, &v, 50, true));
    }

    #[test]
    fn concrete_accept_chain2() {
        let mut root = CapV1::zeroed();
        root.subject_id = [0xAA; 16];
        root.cap_id = [0xBB; 16];
        root.parent_id = [0; 16]; // root
        root.resource_id = [0x44; 32];
        root.audience_id = [0x77; 16];
        root.suite_id = [0, 1];
        root.max_depth = [3];
        root.action = [0, 0, 0, 0b0000_0011];
        root.not_before = 100u64.to_be_bytes();
        root.not_after = 200u64.to_be_bytes();

        let mut leaf = CapV1::zeroed();
        leaf.issuer_id = root.subject_id;
        leaf.subject_id = [0xCC; 16];
        leaf.parent_id = root.cap_id;
        leaf.resource_id = root.resource_id;
        leaf.audience_id = root.audience_id;
        leaf.suite_id = root.suite_id;
        leaf.max_depth = [2];
        leaf.action = [0, 0, 0, 0b0000_0001];
        leaf.not_before = 120u64.to_be_bytes();
        leaf.not_after = 180u64.to_be_bytes();

        let v = [0x77; 16];
        assert!(accept_chain2(&root, &leaf, &v, 150, true, true));
        // Drop either signature: rejected.
        assert!(!accept_chain2(&root, &leaf, &v, 150, false, true));
        assert!(!accept_chain2(&root, &leaf, &v, 150, true, false));
        // Root is not actually a root: rejected.
        let mut not_root = root;
        not_root.parent_id = [0x01; 16];
        assert!(!accept_chain2(&not_root, &leaf, &v, 150, true, true));
    }

    #[test]
    fn concrete_accept_chain3() {
        let mut root = CapV1::zeroed();
        root.subject_id = [0xAA; 16];
        root.cap_id = [0xB0; 16];
        root.resource_id = [0x44; 32];
        root.audience_id = [0x77; 16];
        root.suite_id = [0, 1];
        root.max_depth = [3];
        root.action = [0, 0, 0, 0b0000_0111];
        root.not_before = 100u64.to_be_bytes();
        root.not_after = 200u64.to_be_bytes();

        let mut mid = CapV1::zeroed();
        mid.issuer_id = root.subject_id;
        mid.subject_id = [0xCC; 16];
        mid.parent_id = root.cap_id;
        mid.cap_id = [0xB1; 16];
        mid.resource_id = root.resource_id;
        mid.audience_id = root.audience_id;
        mid.suite_id = root.suite_id;
        mid.max_depth = [2];
        mid.action = [0, 0, 0, 0b0000_0011];
        mid.not_before = 110u64.to_be_bytes();
        mid.not_after = 190u64.to_be_bytes();

        let mut leaf = CapV1::zeroed();
        leaf.issuer_id = mid.subject_id;
        leaf.subject_id = [0xEE; 16];
        leaf.parent_id = mid.cap_id;
        leaf.cap_id = [0xB2; 16];
        leaf.resource_id = root.resource_id;
        leaf.audience_id = root.audience_id;
        leaf.suite_id = root.suite_id;
        leaf.max_depth = [1];
        leaf.action = [0, 0, 0, 0b0000_0001];
        leaf.not_before = 120u64.to_be_bytes();
        leaf.not_after = 180u64.to_be_bytes();

        let v = [0x77; 16];
        let caps = [root, mid, leaf];
        assert!(accept_chain(&caps, &v, 150, &[true, true, true]));
        // Matches the two-link gate on its own ground.
        assert_eq!(
            accept_chain(&[root, mid], &v, 150, &[true, true]),
            accept_chain2(&root, &mid, &v, 150, true, true)
        );
        // Any missing signature: rejected.
        assert!(!accept_chain(&caps, &v, 150, &[true, false, true]));
        // A broken middle link (wrong parent id): rejected.
        let mut bad_mid = mid;
        bad_mid.parent_id = [0x01; 16];
        assert!(!accept_chain(&[root, bad_mid, leaf], &v, 150, &[true, true, true]));

        // Signed variant: keys must match the named issuers.
        let owner = PublicKey { bytes: [0xAB; 32] };
        let mid_k = PublicKey { bytes: [0xCD; 32] };
        let leaf_k = PublicKey { bytes: [0xEF; 32] };
        let mut root2 = root;
        root2.issuer_id = key_id(&owner);
        root2.subject_id = key_id(&mid_k);
        let mut mid2 = mid;
        mid2.issuer_id = key_id(&mid_k);
        mid2.subject_id = key_id(&leaf_k);
        let mut leaf2 = leaf;
        leaf2.issuer_id = key_id(&leaf_k);
        let caps2 = [root2, mid2, leaf2];
        assert!(accept_chain_signed(&caps2, &v, 150, &[owner, mid_k, leaf_k], &[true; 3]));
        // Foreign key at the last hop: rejected even with a valid signature bit.
        let foreign = PublicKey { bytes: [0x99; 32] };
        assert!(!accept_chain_signed(&caps2, &v, 150, &[owner, mid_k, foreign], &[true; 3]));
    }

    #[test]
    fn concrete_accept_once() {
        let mut cap = CapV1::zeroed();
        cap.cap_id = [0x31; 16];
        cap.nonce = [0x42; 16];
        cap.audience_id = [0x77; 16];
        cap.not_before = 100u64.to_be_bytes();
        cap.not_after = 200u64.to_be_bytes();
        let v = [0x77; 16];

        let store = NonceStore::empty();
        let (ok, next) = accept_leaf_once(&cap, &v, 150, true, &store);
        assert!(ok);
        assert!(store_contains(&next, &replay_key(&cap)));
        // Replay: rejected, even later in the window.
        let (ok2, next2) = accept_leaf_once(&cap, &v, 160, true, &next);
        assert!(!ok2);
        assert_eq!(next2, next);
        // A different token (fresh cap_id + nonce) still accepts.
        let mut other = cap;
        other.cap_id = [0x32; 16];
        other.nonce = [0x43; 16];
        let (ok3, _) = accept_leaf_once(&other, &v, 150, true, &next);
        assert!(ok3);
        // The no-consume mutant accepts the replay.
        let (m1, mnext) = accept_leaf_once_noconsume(&cap, &v, 150, true, &store);
        let (m2, _) = accept_leaf_once_noconsume(&cap, &v, 160, true, &mnext);
        assert!(m1 && m2);
        // Full store fails closed.
        let full = NonceStore { used: [[0xFF; 32]; STORE_CAP], len: STORE_CAP };
        let (ok4, _) = accept_leaf_once(&cap, &v, 150, true, &full);
        assert!(!ok4);
    }

    #[test]
    fn concrete_signed_message() {
        let mut cap = CapV1::zeroed();
        cap.audience_id = [0x77; 16];
        // Signed bytes are the canonical serialization, and cover every field.
        assert_eq!(signed_message(&cap), serialize(&cap));
        assert_eq!(parse(&signed_message(&cap)), cap);
        // The audience-omitting signer drops the audience: a differing-audience capability collides.
        let mut other = cap;
        other.audience_id = [0x88; 16];
        assert_ne!(signed_message(&cap), signed_message(&other));
        assert_eq!(
            signed_message_omitting_audience(&cap),
            signed_message_omitting_audience(&other)
        );
    }

    #[test]
    fn concrete_key_binding() {
        let owner = PublicKey { bytes: [0xAA; 32] };
        let delegate = PublicKey { bytes: [0xCC; 32] };
        let foreign = PublicKey { bytes: [0x99; 32] };

        let mut root = CapV1::zeroed();
        root.issuer_id = key_id(&owner);
        root.subject_id = key_id(&delegate); // root delegates to `delegate`
        root.cap_id = [0xBB; 16];
        root.resource_id = [0x44; 32];
        root.audience_id = [0x77; 16];
        root.suite_id = [0, 1];
        root.max_depth = [3];
        root.action = [0, 0, 0, 0b0000_0011];
        root.not_before = 100u64.to_be_bytes();
        root.not_after = 200u64.to_be_bytes();

        let mut leaf = CapV1::zeroed();
        leaf.issuer_id = key_id(&delegate); // leaf issued by the delegate
        leaf.subject_id = [0xEE; 16];
        leaf.parent_id = root.cap_id;
        leaf.resource_id = root.resource_id;
        leaf.audience_id = root.audience_id;
        leaf.suite_id = root.suite_id;
        leaf.max_depth = [2];
        leaf.action = [0, 0, 0, 0b0000_0001];
        leaf.not_before = 120u64.to_be_bytes();
        leaf.not_after = 180u64.to_be_bytes();

        let v = [0x77; 16];
        // Correct keys: accepted.
        assert!(accept_chain2_signed(&root, &leaf, &v, 150, &owner, true, &delegate, true));
        assert!(accept_leaf_signed(&leaf, &v, 150, &delegate, true));
        // Confused deputy: leaf signed by a foreign key, not the delegate. Rejected even with a
        // valid signature bit.
        assert!(!accept_chain2_signed(&root, &leaf, &v, 150, &owner, true, &foreign, true));
        assert!(!accept_leaf_signed(&leaf, &v, 150, &foreign, true));
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

    /// The accept gate is reachable (its guarantees below are not vacuous).
    #[kani::proof]
    fn accept_reachable() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let sig_ok: bool = kani::any();
        kani::cover!(accept_leaf(&cap, &v, now, sig_ok));
    }

    /// No capability is accepted without a valid signature: the signature check cannot be bypassed.
    #[kani::proof]
    fn accept_requires_signature() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        assert!(!accept_leaf(&cap, &v, now, false));
    }

    /// A capability accepted by verifier `v` names `v` as its audience: no cross-service replay.
    #[kani::proof]
    fn accept_binds_audience() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let sig_ok: bool = kani::any();
        kani::assume(accept_leaf(&cap, &v, now, sig_ok));
        assert_eq!(cap.audience_id, v);
    }

    /// An accepted capability is within its validity window at `now`: no expired or not-yet-valid
    /// token is accepted.
    #[kani::proof]
    fn accept_within_window() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let sig_ok: bool = kani::any();
        kani::assume(accept_leaf(&cap, &v, now, sig_ok));
        let (nb, na) = window(&cap);
        assert!(nb <= now && now <= na);
    }

    /// A two-link chain accept is reachable (the guarantees below are not vacuous).
    #[kani::proof]
    fn chain_accept_reachable() {
        let root = any_cap();
        let leaf = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        kani::cover!(accept_chain2(&root, &leaf, &v, now, true, true));
    }

    /// Accepting a chain requires every link's signature: dropping either the root or the leaf
    /// signature makes it reject. The post-quantum signature cannot be stripped from a link.
    #[kani::proof]
    fn chain_accept_requires_all_sigs() {
        let root = any_cap();
        let leaf = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let rs: bool = kani::any();
        let ls: bool = kani::any();
        kani::assume(accept_chain2(&root, &leaf, &v, now, rs, ls));
        assert!(rs && ls);
    }

    /// End-to-end attenuation: if a two-link chain is accepted, the delegated (leaf) capability
    /// grants no more than the root. Its action bits are a subset of the root's, its depth is below
    /// the root's, `now` falls inside the root's window, and both name the presenting verifier as
    /// audience over the same resource. Accepting a re-delegation can never exceed the root grant.
    #[kani::proof]
    fn chain_accept_attenuates() {
        let root = any_cap();
        let leaf = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let rs: bool = kani::any();
        let ls: bool = kani::any();
        kani::assume(accept_chain2(&root, &leaf, &v, now, rs, ls));
        assert_eq!(action_bits(&leaf) & !action_bits(&root), 0);
        assert!(leaf.max_depth[0] < root.max_depth[0]);
        let (r_nb, r_na) = window(&root);
        assert!(r_nb <= now && now <= r_na);
        assert_eq!(leaf.audience_id, v);
        assert_eq!(root.audience_id, v);
        assert_eq!(leaf.resource_id, root.resource_id);
        assert!(is_root(&root));
    }

    /// The signed message covers every field: parsing it back yields the same capability, so no
    /// authorized field sits outside the signature.
    #[kani::proof]
    fn signed_message_covers_all_fields() {
        let cap = any_cap();
        assert_eq!(parse(&signed_message(&cap)), cap);
    }

    /// Distinct capabilities never share signed bytes, so one signature cannot cover two of them.
    #[kani::proof]
    fn signed_message_injective() {
        let c1 = any_cap();
        let c2 = any_cap();
        kani::assume(signed_message(&c1) == signed_message(&c2));
        assert_eq!(c1, c2);
    }

    /// Coverage is not vacuous, and it is exactly what binds the audience: the correct signer gives
    /// two capabilities that differ only in `audience_id` different signed bytes, while a signer that
    /// omitted `audience_id` would give them identical bytes (so a signature would authorize either
    /// audience). This is the Kani analogue of the repo's mutation checks: the property catches the
    /// unsigned-field bug class.
    #[kani::proof]
    fn omitting_audience_breaks_binding() {
        let c1 = any_cap();
        let mut c2 = c1;
        c2.audience_id = kani::any();
        kani::assume(c1.audience_id != c2.audience_id);
        assert_ne!(signed_message(&c1), signed_message(&c2));
        assert_eq!(
            signed_message_omitting_audience(&c1),
            signed_message_omitting_audience(&c2)
        );
    }

    fn any_pk() -> PublicKey {
        PublicKey { bytes: kani::any() }
    }

    /// The key-bound chain accept is reachable (the binding theorems below are not vacuous).
    #[kani::proof]
    fn signed_chain_reachable() {
        let root = any_cap();
        let leaf = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let rpk = any_pk();
        let lpk = any_pk();
        kani::cover!(accept_chain2_signed(&root, &leaf, &v, now, &rpk, true, &lpk, true));
    }

    /// Key binding composes with the link check: if a two-link chain is accepted, the key that
    /// signed the leaf is exactly the key the root delegated authority to. `key_id(leaf_pk) ==
    /// leaf.issuer_id` (binding) and `leaf.issuer_id == root.subject_id` (valid_delegation) compose to
    /// `key_id(leaf_pk) == root.subject_id`. This is not a single-clause restatement; it joins two
    /// facts through the id.
    #[kani::proof]
    fn chain_signing_key_is_delegate() {
        let root = any_cap();
        let leaf = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let rpk = any_pk();
        let lpk = any_pk();
        let rs: bool = kani::any();
        let ls: bool = kani::any();
        kani::assume(accept_chain2_signed(&root, &leaf, &v, now, &rpk, rs, &lpk, ls));
        assert_eq!(key_id(&lpk), root.subject_id);
    }

    /// Confused deputy is rejected: an intermediate that signs the leaf with a key it was not
    /// delegated to (its `key_id` differs from the root's delegate) cannot get the chain accepted,
    /// whatever else it sets. This is the contrapositive of the binding theorem, stated as the attack.
    #[kani::proof]
    fn confused_deputy_rejected() {
        let root = any_cap();
        let leaf = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let rpk = any_pk();
        let lpk = any_pk();
        let rs: bool = kani::any();
        let ls: bool = kani::any();
        kani::assume(key_id(&lpk) != root.subject_id);
        assert!(!accept_chain2_signed(&root, &leaf, &v, now, &rpk, rs, &lpk, ls));
    }

    /// The generalized chain accept agrees with the two-link definition: `accept_chain::<2>` and
    /// `accept_chain2` are the same predicate, and likewise for the signed variants. So every
    /// two-link theorem above transfers to the generalized gate, and the generalization introduced
    /// no behavior change at the length it replaces.
    #[kani::proof]
    fn chain_n_agrees_with_chain2() {
        let root = any_cap();
        let leaf = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let rs: bool = kani::any();
        let ls: bool = kani::any();
        assert_eq!(
            accept_chain(&[root, leaf], &v, now, &[rs, ls]),
            accept_chain2(&root, &leaf, &v, now, rs, ls)
        );
        let rpk = any_pk();
        let lpk = any_pk();
        assert_eq!(
            accept_chain_signed(&[root, leaf], &v, now, &[rpk, lpk], &[rs, ls]),
            accept_chain2_signed(&root, &leaf, &v, now, &rpk, rs, &lpk, ls)
        );
    }

    /// A three-link chain accept is reachable (the N-link theorems below are not vacuous).
    #[kani::proof]
    fn chain3_reachable() {
        let caps = [any_cap(), any_cap(), any_cap()];
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        kani::cover!(accept_chain(&caps, &v, now, &[true, true, true]));
    }

    /// Accepting a three-link chain requires every link's signature: no link's check can be skipped.
    #[kani::proof]
    fn chain3_requires_all_sigs() {
        let caps = [any_cap(), any_cap(), any_cap()];
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let sigs: [bool; 3] = kani::any();
        kani::assume(accept_chain(&caps, &v, now, &sigs));
        assert!(sigs[0] && sigs[1] && sigs[2]);
    }

    /// End-to-end attenuation at three links: an accepted leaf grants no action bit the root lacks,
    /// sits inside the root's window at `now`, keeps resource and audience, and has consumed at
    /// least one unit of depth budget per hop (`root.max_depth >= leaf.max_depth + 2`), so the
    /// chain's length is bounded by the root's budget.
    #[kani::proof]
    fn chain3_attenuates() {
        let caps = [any_cap(), any_cap(), any_cap()];
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let sigs: [bool; 3] = kani::any();
        kani::assume(accept_chain(&caps, &v, now, &sigs));
        let (root, leaf) = (&caps[0], &caps[2]);
        assert_eq!(action_bits(leaf) & !action_bits(root), 0);
        assert!(root.max_depth[0] as usize >= leaf.max_depth[0] as usize + 2);
        let (r_nb, r_na) = window(root);
        assert!(r_nb <= now && now <= r_na);
        assert_eq!(leaf.audience_id, v);
        assert_eq!(leaf.resource_id, root.resource_id);
        assert!(is_root(root));
    }

    /// The same attenuation theorem at four links (depth margin 3). Together with the three-link
    /// case this checks the composition at every length the harnesses instantiate; lengths beyond
    /// these are covered by the argument that `valid_delegation` is link-local (see CAP-V1.md), not
    /// by a machine-checked induction.
    #[kani::proof]
    fn chain4_attenuates() {
        let caps = [any_cap(), any_cap(), any_cap(), any_cap()];
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let sigs: [bool; 4] = kani::any();
        kani::assume(accept_chain(&caps, &v, now, &sigs));
        let (root, leaf) = (&caps[0], &caps[3]);
        assert_eq!(action_bits(leaf) & !action_bits(root), 0);
        assert!(root.max_depth[0] as usize >= leaf.max_depth[0] as usize + 3);
        let (r_nb, r_na) = window(root);
        assert!(r_nb <= now && now <= r_na);
        assert_eq!(leaf.audience_id, v);
        assert_eq!(leaf.resource_id, root.resource_id);
    }

    /// Key binding down a three-link chain: every non-root link is signed by exactly the key the
    /// previous link delegated to (`key_id(pks[i]) == caps[i-1].subject_id`), joining the binding
    /// clause with `valid_delegation` at each hop.
    #[kani::proof]
    fn chain3_signing_keys_are_delegates() {
        let caps = [any_cap(), any_cap(), any_cap()];
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let pks = [any_pk(), any_pk(), any_pk()];
        let sigs: [bool; 3] = kani::any();
        kani::assume(accept_chain_signed(&caps, &v, now, &pks, &sigs));
        assert_eq!(key_id(&pks[1]), caps[0].subject_id);
        assert_eq!(key_id(&pks[2]), caps[1].subject_id);
    }

    /// Confused deputy at any hop of a three-link chain: if any non-root link is signed with a key
    /// that is not the one its parent delegated to, the chain rejects, whatever else is set.
    #[kani::proof]
    fn chain3_confused_deputy_rejected() {
        let caps = [any_cap(), any_cap(), any_cap()];
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let pks = [any_pk(), any_pk(), any_pk()];
        let sigs: [bool; 3] = kani::any();
        kani::assume(
            key_id(&pks[1]) != caps[0].subject_id || key_id(&pks[2]) != caps[1].subject_id,
        );
        assert!(!accept_chain_signed(&caps, &v, now, &pks, &sigs));
    }

    fn any_store() -> NonceStore {
        NonceStore { used: kani::any(), len: kani::any() }
    }

    /// The single-use gate is reachable (the replay theorems below are not vacuous).
    #[kani::proof]
    fn once_reachable() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let store = any_store();
        let (ok, _) = accept_leaf_once(&cap, &v, now, true, &store);
        kani::cover!(ok);
    }

    /// No replay: after a token is accepted, presenting the same token to the successor store
    /// rejects, whatever `now` the second presentation uses. This is the substantive stateful
    /// result (accept mutates the store, and the mutation is what blocks the second accept).
    #[kani::proof]
    fn no_replay() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now1: u64 = kani::any();
        let now2: u64 = kani::any();
        let s1: bool = kani::any();
        let s2: bool = kani::any();
        let store = any_store();
        let (ok, next) = accept_leaf_once(&cap, &v, now1, s1, &store);
        kani::assume(ok);
        let (ok2, _) = accept_leaf_once(&cap, &v, now2, s2, &next);
        assert!(!ok2);
    }

    /// A consumed key never accepts: if the capability's replay key is already in the store, the
    /// gate rejects.
    #[kani::proof]
    fn consumed_never_accepts() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let s: bool = kani::any();
        let store = any_store();
        kani::assume(store_contains(&store, &replay_key(&cap)));
        let (ok, _) = accept_leaf_once(&cap, &v, now, s, &store);
        assert!(!ok);
    }

    /// Acceptance consumes: an accepted token's replay key is in the successor store, and rejection
    /// leaves the store unchanged.
    #[kani::proof]
    fn accept_consumes() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let s: bool = kani::any();
        let store = any_store();
        let (ok, next) = accept_leaf_once(&cap, &v, now, s, &store);
        if ok {
            assert!(store_contains(&next, &replay_key(&cap)));
        } else {
            assert_eq!(next, store);
        }
    }

    /// The stateful gate does not weaken the stateless one: single-use acceptance implies the plain
    /// leaf gate (signature, audience, window all still required), and a full store fails closed.
    #[kani::proof]
    fn once_implies_leaf_gate() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now: u64 = kani::any();
        let s: bool = kani::any();
        let store = any_store();
        let (ok, _) = accept_leaf_once(&cap, &v, now, s, &store);
        if store.len >= STORE_CAP {
            assert!(!ok);
        }
        if ok {
            assert!(accept_leaf(&cap, &v, now, s));
        }
    }

    /// The no-replay theorem has content: under the no-consume mutant the same token CAN accept
    /// twice (a `kani::cover!` finds a double accept), while `no_replay` proves the correct gate
    /// never does. The mutation device of the repo's other tracks, stated inside Kani.
    #[kani::proof]
    fn noconsume_mutant_replays() {
        let cap = any_cap();
        let v: [u8; 16] = kani::any();
        let now1: u64 = kani::any();
        let now2: u64 = kani::any();
        let store = any_store();
        let (ok, next) = accept_leaf_once_noconsume(&cap, &v, now1, true, &store);
        let (ok2, _) = accept_leaf_once_noconsume(&cap, &v, now2, true, &next);
        kani::cover!(ok && ok2);
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
