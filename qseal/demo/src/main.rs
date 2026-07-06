//! Runnable Q-SEAL hybrid attestation demo.
//!
//! Real crypto: ECDSA P-256 (classical) + ML-DSA-44 (post-quantum, the RustCrypto crate this project
//! formally verifies), signing the verified TBS-V1 transcript. HYB-1 acceptance requires BOTH
//! signatures over the SAME transcript, matching the SAW-proved qseal/proof/hybrid.saw. This binary
//! shows three outcomes with no proof toolchain needed:
//!   1. a valid attestation accepts,
//!   2. a tampered transcript is rejected,
//!   3. a downgrade (valid classical signature, no valid PQ signature) is rejected, where a buggy
//!      "accept on either" verifier would have accepted,
//!   4. a replay of a valid attestation (same request_id, resubmitted) is rejected by a stateful
//!      verifier that consumes the challenge once, matching qseal/proof/nonce.saw (section 16
//!      property 4). A verifier that skips the consume step would accept the replay,
//!   5. a malformed request (unsupported suite) is refused before signing, matching
//!      qseal/proof/validate.saw (section 16 property 7). The applet produces no transcript at all.

mod tbs;
use tbs::{create_assertion, create_assertion_checked, AppletId, Request};

use std::collections::HashSet;

use ml_dsa::{Generate, Keypair, MlDsa44};
use ml_dsa::{Signature as MlSig, Signer as MlSign, SigningKey as MlSk, Verifier as MlVerify, VerifyingKey as MlVk};

use p256::ecdsa::signature::{Signer as EcSign, Verifier as EcVerify};
use p256::ecdsa::{Signature as EcSig, SigningKey as EcSk, VerifyingKey as EcVk};
use rand_core::OsRng;

struct SecretKeys {
    ec: EcSk,
    ml: MlSk<MlDsa44>,
}
struct PublicKeys {
    ec: EcVk,
    ml: MlVk<MlDsa44>,
}
struct HybridSig {
    ec: EcSig,
    ml: MlSig<MlDsa44>,
}

fn keygen() -> (SecretKeys, PublicKeys) {
    let ec = EcSk::random(&mut OsRng);
    let ec_pub = *ec.verifying_key();
    let ml = MlSk::<MlDsa44>::generate();
    let ml_pub = ml.verifying_key();
    (SecretKeys { ec, ml }, PublicKeys { ec: ec_pub, ml: ml_pub })
}

fn hybrid_sign(sk: &SecretKeys, tbs: &[u8]) -> HybridSig {
    HybridSig { ec: sk.ec.sign(tbs), ml: sk.ml.sign(tbs) }
}

/// Returns (classical_ok, pq_ok). HYB-1 accept is the AND of the two.
fn verify_both(pk: &PublicKeys, tbs: &[u8], sig: &HybridSig) -> (bool, bool) {
    let ok_c = pk.ec.verify(tbs, &sig.ec).is_ok();
    let ok_pq = pk.ml.verify(tbs, &sig.ml).is_ok();
    (ok_c, ok_pq)
}

/// Stateful single-use challenge store: the set of request_ids already consumed. This is the runnable
/// twin of qseal/ref/nonce.c (an append-only store there, a HashSet here; the single-use logic is what
/// qseal/proof/nonce.saw verifies). Accept iff the signatures/policy are OK AND the challenge is fresh;
/// on accept, consume it so a resubmission is rejected.
struct NonceStore(HashSet<[u8; 16]>);
impl NonceStore {
    fn new() -> Self {
        NonceStore(HashSet::new())
    }
    /// `sigs_ok` folds in the HYB-1 both-signatures decision. Returns true (accept) iff validated and
    /// the request_id has not been consumed; records it on accept.
    fn accept_once(&mut self, sigs_ok: bool, request_id: &[u8; 16]) -> bool {
        let fresh = !self.0.contains(request_id);
        let accept = sigs_ok && fresh;
        if accept {
            self.0.insert(*request_id);
        }
        accept
    }
}

fn sample_request() -> Request {
    Request {
        suite_id: [0x00, 0x01],           // HYB-1
        assertion_type: [0x01],           // ENROLLMENT
        assertion_origin: [0x01],         // HOST_ASSERTED
        verifier_id: *b"relying-party-01",
        request_id: *b"req-000000000001",
        nonce: *b"a-32-byte-server-challenge-nonce",
        policy_id: [0, 0, 0, 7],
        expires_at: [0, 0, 0, 0, 0, 0, 0, 60],
        subject_ref: *b"pseudonymous-subject-reference32",
        object_hash_algorithm: [0x01],    // SHA-256
        object_length: [0, 0, 0, 0, 0, 0, 0, 42],
        object_digest: [0x11; 32],
        associated_claim_digest: [0x22; 32],
    }
}

fn sample_applet() -> AppletId {
    AppletId {
        version: [0x01],
        issuer_id: *b"euicc-issuer-001",
        ak_id: *b"attestation-key0",
        issued_at: [0, 0, 0, 0, 0, 0, 0, 1],
    }
}

fn outcome(accept: bool) -> &'static str {
    if accept { "ACCEPT" } else { "REJECT" }
}

fn main() {
    println!("Q-SEAL hybrid attestation demo (ECDSA P-256 + ML-DSA-44 over the verified TBS-V1 transcript)\n");

    let (sk, pk) = keygen();
    let req = sample_request();
    let app = sample_applet();
    let tbs = create_assertion(&req, &app);
    println!("built a {}-byte TBS-V1 transcript, signed it with both keys\n", tbs.len());

    // 1. Valid attestation.
    let sig = hybrid_sign(&sk, &tbs);
    let (c, q) = verify_both(&pk, &tbs, &sig);
    println!("1. valid attestation           classical={c:5}  pq={q:5}  ->  {}", outcome(c && q));

    // 2. Tampered transcript: flip one byte of what the verifier checks.
    let mut tampered = tbs;
    tampered[100] ^= 0x01;
    let (c, q) = verify_both(&pk, &tampered, &sig);
    println!("2. tampered transcript         classical={c:5}  pq={q:5}  ->  {}", outcome(c && q));

    // 3. Downgrade: a valid classical signature, but the PQ signature is not from the real key
    //    (attacker who can forge the classical half but not the post-quantum one).
    let (attacker_sk, _) = keygen();
    let downgrade = HybridSig { ec: sk.ec.sign(&tbs[..]), ml: attacker_sk.ml.sign(&tbs[..]) };
    let (c, q) = verify_both(&pk, &tbs, &downgrade);
    println!("3. downgrade (classical only)  classical={c:5}  pq={q:5}  ->  {}", outcome(c && q));
    println!("   a buggy \"accept on either\" verifier would have returned {} here.", outcome(c || q));

    // 4. Replay: resubmit the SAME valid attestation. A stateful verifier consumes the request_id on
    //    first accept, so the replay is rejected even though both signatures still verify.
    let mut store = NonceStore::new();
    let (c, q) = verify_both(&pk, &tbs, &sig);
    let first = store.accept_once(c && q, &req.request_id);
    let (c, q) = verify_both(&pk, &tbs, &sig);
    let replay = store.accept_once(c && q, &req.request_id);
    println!("4. first submission            sigs_ok={:5}  fresh={:5}  ->  {}", c && q, first, outcome(first));
    println!("   replay (same request_id)    sigs_ok={:5}  fresh={:5}  ->  {}", c && q, replay, outcome(replay));
    println!("   a verifier that skips consume_nonce_once would have returned {} on the replay.", outcome(c && q));

    // 5. Malformed request: an unsupported suite. The applet validates before signing, so it produces
    //    no transcript at all (nothing to sign, nothing to verify).
    let mut bad = sample_request();
    bad.suite_id = [0x00, 0x02]; // not HYB-1
    let signed_ok = create_assertion_checked(&req, &app).is_some();
    let signed_bad = create_assertion_checked(&bad, &app).is_some();
    println!("5. valid request               validated={:5}  ->  {}", signed_ok, if signed_ok { "SIGN" } else { "REFUSE" });
    println!("   malformed (bad suite_id)    validated={:5}  ->  {}", signed_bad, if signed_bad { "SIGN" } else { "REFUSE" });
    println!("   a verifier that skipped the suite check would have signed the malformed request.");

    println!("\nHYB-1 accepts only when both signatures verify over the same transcript, each challenge");
    println!("is single-use, and a malformed request is never signed. Those rules are machine-checked in");
    println!("qseal/proof/hybrid.saw, qseal/proof/nonce.saw, and qseal/proof/validate.saw.");

    // Non-zero exit if the demo does not behave (keeps it usable as a check).
    let (c1, q1) = verify_both(&pk, &tbs, &sig);
    let ok_valid = c1 && q1;
    let (ct, qt) = verify_both(&pk, &tampered, &sig);
    let ok_tamper_rejected = !(ct && qt);
    let (cd, qd) = verify_both(&pk, &tbs, &downgrade);
    let ok_downgrade_rejected = !(cd && qd) && cd; // rejected overall, but classical alone was valid
    let mut store2 = NonceStore::new();
    let ok_first = store2.accept_once(true, &req.request_id); // fresh challenge accepts
    let ok_replay_rejected = !store2.accept_once(true, &req.request_id); // same id, now consumed
    let mut bad2 = sample_request();
    bad2.suite_id = [0x00, 0x02];
    let ok_valid_signed = create_assertion_checked(&req, &app).is_some();
    let ok_malformed_refused = create_assertion_checked(&bad2, &app).is_none();
    if !(ok_valid
        && ok_tamper_rejected
        && ok_downgrade_rejected
        && ok_first
        && ok_replay_rejected
        && ok_valid_signed
        && ok_malformed_refused)
    {
        eprintln!("DEMO SELF-CHECK FAILED");
        std::process::exit(1);
    }
}
