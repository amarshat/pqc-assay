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
//!      qseal/proof/validate.saw (section 16 property 7). The applet produces no transcript at all,
//!   6. evidence returned as fragments reassembles to exactly the original bytes, and a dropped
//!      fragment fails closed rather than being zero-filled, matching qseal/proof/evidence.saw
//!      (section 16 property 6).

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
struct NonceStore(HashSet<[u8; 64]>);
impl NonceStore {
    fn new() -> Self {
        NonceStore(HashSet::new())
    }
    /// `sigs_ok` folds in the HYB-1 both-signatures decision. The single-use challenge key is
    /// verifier_id || request_id || nonce, the key the spec's consume-once rule is defined over (a
    /// request_id is unique per verifier, so the key is also per-verifier). Returns true (accept) iff
    /// validated and the key has not been consumed; records it on accept.
    fn accept_once(
        &mut self,
        sigs_ok: bool,
        verifier_id: &[u8; 16],
        request_id: &[u8; 16],
        nonce: &[u8; 32],
    ) -> bool {
        let mut key = [0u8; 64];
        key[..16].copy_from_slice(verifier_id);
        key[16..32].copy_from_slice(request_id);
        key[32..].copy_from_slice(nonce);
        let fresh = !self.0.contains(&key);
        let accept = sigs_ok && fresh;
        if accept {
            self.0.insert(key);
        }
        accept
    }
}

// Evidence-fragment sizes, matching qseal/model/QSEAL_Evidence.cry and qseal/ref/evidence.c.
const FRAG_SIZE: usize = 32;
const NUM_FRAGS: usize = 4;
const EVID_LEN: usize = FRAG_SIZE * NUM_FRAGS;

struct Frag {
    seq: u8,
    total: u8,
    data: [u8; FRAG_SIZE],
}

/// Split an evidence blob into fragments (READ_EVIDENCE response chaining). Twin of the model `fragment`.
fn fragment_evidence(e: &[u8; EVID_LEN]) -> [Frag; NUM_FRAGS] {
    std::array::from_fn(|i| {
        let mut data = [0u8; FRAG_SIZE];
        data.copy_from_slice(&e[i * FRAG_SIZE..(i + 1) * FRAG_SIZE]);
        Frag { seq: i as u8, total: NUM_FRAGS as u8, data }
    })
}

/// Reassemble the blob iff the fragment set is well formed (indices a permutation of 0..NF-1, correct
/// total), else `None` (fail closed). Twin of qseal/ref/evidence.c, proved == the model in
/// qseal/proof/evidence.saw.
fn reassemble_evidence(frags: &[Frag; NUM_FRAGS]) -> Option<[u8; EVID_LEN]> {
    let totals_ok = frags.iter().all(|f| f.total as usize == NUM_FRAGS);
    let perm_ok = (0..NUM_FRAGS as u8).all(|j| frags.iter().filter(|f| f.seq == j).count() == 1);
    if !(totals_ok && perm_ok) {
        return None;
    }
    let mut out = [0u8; EVID_LEN];
    for j in 0..NUM_FRAGS {
        let f = frags.iter().find(|f| f.seq as usize == j).unwrap();
        out[j * FRAG_SIZE..(j + 1) * FRAG_SIZE].copy_from_slice(&f.data);
    }
    Some(out)
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
    let first = store.accept_once(c && q, &req.verifier_id, &req.request_id, &req.nonce);
    let (c, q) = verify_both(&pk, &tbs, &sig);
    let replay = store.accept_once(c && q, &req.verifier_id, &req.request_id, &req.nonce);
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

    // 6. Evidence read-back: the applet returns evidence as fragments; the host reassembles. A complete
    //    set recovers the exact bytes; a dropped fragment (a duplicated index) fails closed.
    let evidence: [u8; EVID_LEN] = std::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(1));
    let recovered = reassemble_evidence(&fragment_evidence(&evidence));
    let exact = recovered.as_ref() == Some(&evidence);
    let mut dropped = fragment_evidence(&evidence);
    dropped[2].seq = dropped[1].seq; // fragment 2 lost: index 1 now duplicated, index 2 missing
    let recovered_bad = reassemble_evidence(&dropped);
    println!("6. complete fragment set       exact={:5}      ->  {}", exact, if exact { "RECOVER" } else { "WRONG" });
    println!("   dropped fragment            recovered={:5}  ->  {}", recovered_bad.is_some(), if recovered_bad.is_none() { "REJECT" } else { "ACCEPT" });
    println!("   a reassembler that skipped the completeness check would have returned zero-filled bytes.");

    println!("\nHYB-1 accepts only when both signatures verify over the same transcript, each challenge is");
    println!("single-use, a malformed request is never signed, and fragmented evidence reassembles exactly");
    println!("or fails closed. Those rules are machine-checked in qseal/proof/hybrid.saw, nonce.saw,");
    println!("validate.saw, and evidence.saw.");

    // Non-zero exit if the demo does not behave (keeps it usable as a check).
    let (c1, q1) = verify_both(&pk, &tbs, &sig);
    let ok_valid = c1 && q1;
    let (ct, qt) = verify_both(&pk, &tampered, &sig);
    let ok_tamper_rejected = !(ct && qt);
    let (cd, qd) = verify_both(&pk, &tbs, &downgrade);
    let ok_downgrade_rejected = !(cd && qd) && cd; // rejected overall, but classical alone was valid
    let mut store2 = NonceStore::new();
    let ok_first = store2.accept_once(true, &req.verifier_id, &req.request_id, &req.nonce); // fresh challenge accepts
    let ok_replay_rejected = !store2.accept_once(true, &req.verifier_id, &req.request_id, &req.nonce); // same id, now consumed
    let mut bad2 = sample_request();
    bad2.suite_id = [0x00, 0x02];
    let ok_valid_signed = create_assertion_checked(&req, &app).is_some();
    let ok_malformed_refused = create_assertion_checked(&bad2, &app).is_none();
    let ev: [u8; EVID_LEN] = std::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(1));
    let ok_evidence_exact = reassemble_evidence(&fragment_evidence(&ev)).as_ref() == Some(&ev);
    let mut ev_dropped = fragment_evidence(&ev);
    ev_dropped[2].seq = ev_dropped[1].seq;
    let ok_dropped_rejected = reassemble_evidence(&ev_dropped).is_none();
    if !(ok_valid
        && ok_tamper_rejected
        && ok_downgrade_rejected
        && ok_first
        && ok_replay_rejected
        && ok_valid_signed
        && ok_malformed_refused
        && ok_evidence_exact
        && ok_dropped_rejected)
    {
        eprintln!("DEMO SELF-CHECK FAILED");
        std::process::exit(1);
    }
}
