//! Q-SEAL TBS-V1 transcript, matching the layout verified in qseal/model/QSEAL_TBS.cry and the C
//! reference qseal/ref/. Fixed 231 bytes, magic first, no optional fields. `create_assertion` is the
//! Rust twin of qseal/model/QSEAL_Assertion.cry `create`: the applet builds the transcript from the
//! validated request plus its own identity fields, so the signed bytes bind the challenge.

pub const QSEAL_TBS_LEN: usize = 231;
pub const MAGIC: &[u8; 5] = b"QSEAL";

/// Challenge/request fields supplied by the host (never an encoded transcript).
pub struct Request {
    pub suite_id: [u8; 2],
    pub assertion_type: [u8; 1],
    pub assertion_origin: [u8; 1],
    pub verifier_id: [u8; 16],
    pub request_id: [u8; 16],
    pub nonce: [u8; 32],
    pub policy_id: [u8; 4],
    pub expires_at: [u8; 8],
    pub subject_ref: [u8; 32],
    pub object_hash_algorithm: [u8; 1],
    pub object_length: [u8; 8],
    pub object_digest: [u8; 32],
    pub associated_claim_digest: [u8; 32],
}

/// Applet-controlled identity fields (never from the host).
pub struct AppletId {
    pub version: [u8; 1],
    pub issuer_id: [u8; 16],
    pub ak_id: [u8; 16],
    pub issued_at: [u8; 8],
}

/// The well-formedness gate the applet runs before signing, the Rust twin of QSEAL_Validate.cry
/// `valid` (proved equal to the C `qseal_validate_request` in qseal/proof/validate.saw): version 0x01,
/// suite 0x0001 (HYB-1), assertion_type 0x01..0x06, assertion_origin 0x01..0x03, hash alg 0x01.
pub fn validate_request(r: &Request, a: &AppletId) -> bool {
    a.version == [0x01]
        && r.suite_id == [0x00, 0x01]
        && (0x01..=0x06).contains(&r.assertion_type[0])
        && r.assertion_type[0] != 0x04 // PROFILE_ACTION_OBSERVED is not host-callable (spec 8.4)
        && (0x01..=0x03).contains(&r.assertion_origin[0])
        && r.object_hash_algorithm == [0x01]
}

/// Validate, then sign: `Some(transcript)` for a well-formed request, `None` (no signing) otherwise.
/// Mirrors the C `qseal_create_assertion_checked`.
pub fn create_assertion_checked(r: &Request, a: &AppletId) -> Option<[u8; QSEAL_TBS_LEN]> {
    if validate_request(r, a) {
        Some(create_assertion(r, a))
    } else {
        None
    }
}

/// Build the TBS-V1 bytes: challenge fields from the request, identity/clock from the applet.
/// Field order matches QSEAL_TBS.cry `serialize` exactly.
pub fn create_assertion(r: &Request, a: &AppletId) -> [u8; QSEAL_TBS_LEN] {
    let mut out = [0u8; QSEAL_TBS_LEN];
    let mut o = 0usize;
    let mut put = |src: &[u8]| {
        out[o..o + src.len()].copy_from_slice(src);
        o += src.len();
    };
    put(MAGIC);
    put(&a.version);
    put(&r.suite_id);
    put(&r.assertion_type);
    put(&r.assertion_origin);
    put(&a.issuer_id);
    put(&r.verifier_id);
    put(&a.ak_id);
    put(&r.request_id);
    put(&r.nonce);
    put(&r.policy_id);
    put(&a.issued_at);
    put(&r.expires_at);
    put(&r.subject_ref);
    put(&r.object_hash_algorithm);
    put(&r.object_length);
    put(&r.object_digest);
    put(&r.associated_claim_digest);
    debug_assert_eq!(o, QSEAL_TBS_LEN);
    out
}

// ---- TBS-V2 (spec 7.1, v0.2 draft): TBS-V1 plus pair_commitment after ak_id, 263 bytes ----

pub const QSEAL_TBS_V2_LEN: usize = 263;

/// FIPS 204 context string for the ML-DSA half of a V2 attestation (spec 7.1). Reserved: the
/// attestation key signs under no other ctx, and nothing else signs under this one.
pub const QSEAL_CTX_V2: &[u8] = b"Q-SEAL/v2";

/// Byte range of pair_commitment inside a serialized V2 transcript
/// (magic 5 + version 1 + suite 2 + type 1 + origin 1 + issuer 16 + verifier 16 + ak 16 = 58).
pub const V2_COMMITMENT_RANGE: std::ops::Range<usize> = 58..90;

/// Build the TBS-V2 bytes: as V1, with the applet-computed pair_commitment directly after ak_id.
/// Field order matches QSEAL_TBS_V2.cry `serialize2` exactly (verified C twin: qseal/ref/tbs_v2.c,
/// proved in qseal/proof/tbs_v2.saw). The commitment MUST come from the applet's own key material;
/// this function's caller plays the applet.
pub fn create_assertion_v2(
    r: &Request,
    a: &AppletId,
    pair_commitment: &[u8; 32],
) -> [u8; QSEAL_TBS_V2_LEN] {
    let mut out = [0u8; QSEAL_TBS_V2_LEN];
    let mut o = 0usize;
    let mut put = |src: &[u8]| {
        out[o..o + src.len()].copy_from_slice(src);
        o += src.len();
    };
    put(MAGIC);
    put(&a.version);
    put(&r.suite_id);
    put(&r.assertion_type);
    put(&r.assertion_origin);
    put(&a.issuer_id);
    put(&r.verifier_id);
    put(&a.ak_id);
    put(pair_commitment);
    put(&r.request_id);
    put(&r.nonce);
    put(&r.policy_id);
    put(&a.issued_at);
    put(&r.expires_at);
    put(&r.subject_ref);
    put(&r.object_hash_algorithm);
    put(&r.object_length);
    put(&r.object_digest);
    put(&r.associated_claim_digest);
    debug_assert_eq!(o, QSEAL_TBS_V2_LEN);
    out
}
