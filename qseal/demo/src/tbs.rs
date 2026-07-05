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
