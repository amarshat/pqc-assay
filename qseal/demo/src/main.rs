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
//!      (section 16 property 6),
//!   7. TBS-V2 (spec 7.1): the applet computes a pair commitment from its own key material and
//!      signs the 263-byte V2 transcript, ML-DSA under the reserved FIPS 204 ctx "Q-SEAL/v2". The
//!      verifier recomputes the commitment from the certified keys, so a zeroed commitment is
//!      rejected even with valid signatures, and an empty-ctx ML-DSA signature does not verify
//!      under the reserved ctx. The V2 layout is the one verified in qseal/proof/tbs_v2.saw.

mod tbs;
use tbs::{
    create_assertion, create_assertion_checked, create_assertion_v2, AppletId, Request,
    QSEAL_CTX_V2, V2_COMMITMENT_RANGE,
};

use std::collections::HashSet;

use ml_dsa::{Generate, Keypair, MlDsa44};
use ml_dsa::{Signature as MlSig, Signer as MlSign, SigningKey as MlSk, Verifier as MlVerify, VerifyingKey as MlVk};

use p256::ecdsa::signature::{Signer as EcSign, Verifier as EcVerify};
use p256::ecdsa::{Signature as EcSig, SigningKey as EcSk, VerifyingKey as EcVk};
use rand_core::OsRng;
use sha2::{Digest, Sha256};

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

// ---- TBS-V2 (spec 7.1): pair commitment + reserved ML-DSA context ----

/// pair_commitment = SHA-256("QSEAL-PAIR-HYB1" || compressed P-256 point || encoded ML-DSA-44 key).
/// The applet computes this from its OWN key material (a host-supplied value must be rejected);
/// the verifier recomputes it from the keys it validated via the ak_id certificate chain.
fn pair_commitment(pk: &PublicKeys) -> [u8; 32] {
    let ec_point = pk.ec.to_encoded_point(true); // 33-byte compressed SEC1 point
    let ml_encoded = pk.ml.encode(); // 1312-byte FIPS 204 encoding
    let mut h = Sha256::new();
    h.update(b"QSEAL-PAIR-HYB1");
    h.update(ec_point.as_bytes());
    h.update(ml_encoded.as_slice());
    h.finalize().into()
}

/// V2 signing: ECDSA as before (no context parameter; the key is dedicated, spec 6.1), ML-DSA under
/// the reserved FIPS 204 context "Q-SEAL/v2" (spec 7.1).
fn hybrid_sign_v2(sk: &SecretKeys, tbs2: &[u8]) -> HybridSig {
    HybridSig {
        ec: sk.ec.sign(tbs2),
        ml: sk.ml.expanded_key().sign_deterministic(tbs2, QSEAL_CTX_V2).expect("ctx under 255 bytes"),
    }
}

/// V2 acceptance: recompute the pair commitment from the validated keys and compare against the
/// transcript bytes, then require BOTH signatures, the ML-DSA one under the reserved context.
/// Returns (commitment_ok, classical_ok, pq_ok); accept is the AND of all three.
fn verify_v2(pk: &PublicKeys, tbs2: &[u8], sig: &HybridSig) -> (bool, bool, bool) {
    let commit_ok = tbs2[V2_COMMITMENT_RANGE] == pair_commitment(pk);
    let ok_c = pk.ec.verify(tbs2, &sig.ec).is_ok();
    let ok_pq = pk.ml.verify_with_context(tbs2, QSEAL_CTX_V2, &sig.ml);
    (commit_ok, ok_c, ok_pq)
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
    println!("Q-SEAL hybrid attestation demo (ECDSA P-256 + ML-DSA-44 over the verified TBS-V1/V2 transcripts)\n");

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

    // 7. TBS-V2: hybrid pair binding inside the signed bytes (spec 7.1). The applet computes
    //    pair_commitment from its own keys; the verifier recomputes it from the keys it validated
    //    via ak_id's certificate chain. The ML-DSA half signs under the reserved ctx "Q-SEAL/v2".
    let app2 = AppletId {
        version: [0x02],
        issuer_id: app.issuer_id,
        ak_id: app.ak_id,
        issued_at: app.issued_at,
    };
    let commit = pair_commitment(&pk);
    let tbs2 = create_assertion_v2(&req, &app2, &commit);
    let sig2 = hybrid_sign_v2(&sk, &tbs2);
    let (k, c, q) = verify_v2(&pk, &tbs2, &sig2);
    println!("7. V2 pair-bound transcript    commit={k:5} classical={c:5}  pq={q:5}  ->  {}", outcome(k && c && q));

    //    A commitment not derived from the pair (here zeroed): both signatures over the bytes still
    //    verify, but the recompute-and-compare check rejects. This is the check that makes a peeled
    //    component signature identify itself as half of a Q-SEAL pair.
    let tbs2_zero = create_assertion_v2(&req, &app2, &[0u8; 32]);
    let sig2_zero = hybrid_sign_v2(&sk, &tbs2_zero);
    let (k, c, q) = verify_v2(&pk, &tbs2_zero, &sig2_zero);
    println!("   zeroed commitment           commit={k:5} classical={c:5}  pq={q:5}  ->  {}", outcome(k && c && q));
    println!("   a verifier that skipped recompute-and-compare would have returned {} here.", outcome(c && q));

    //    Context separation: an ML-DSA signature over the same bytes with the empty ctx (V1 style)
    //    does not verify under the reserved ctx.
    let no_ctx_sig = sk.ml.sign(&tbs2[..]);
    let ctx_separated = !pk.ml.verify_with_context(&tbs2[..], QSEAL_CTX_V2, &no_ctx_sig);
    println!("   empty-ctx ML-DSA sig under reserved ctx      ->  {}",
        if ctx_separated { "REJECT (context separation live)" } else { "ACCEPT (BUG)" });

    println!("\nHYB-1 accepts only when both signatures verify over the same transcript, each challenge is");
    println!("single-use, a malformed request is never signed, fragmented evidence reassembles exactly or");
    println!("fails closed, and the V2 transcript binds the exact hybrid pair under a reserved ML-DSA ctx.");
    println!("Those rules are machine-checked in qseal/proof/hybrid.saw, nonce.saw, validate.saw,");
    println!("evidence.saw, and tbs_v2.saw.");

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
    let (k7, c7, q7) = verify_v2(&pk, &tbs2, &sig2);
    let ok_v2_valid = k7 && c7 && q7;
    let (kz, cz, qz) = verify_v2(&pk, &tbs2_zero, &sig2_zero);
    let ok_v2_commit_rejected = !kz && cz && qz; // signatures valid; the recompute check rejects
    let ok_v2_ctx_separated = ctx_separated;
    if !(ok_valid
        && ok_tamper_rejected
        && ok_downgrade_rejected
        && ok_first
        && ok_replay_rejected
        && ok_valid_signed
        && ok_malformed_refused
        && ok_evidence_exact
        && ok_dropped_rejected
        && ok_v2_valid
        && ok_v2_commit_rejected
        && ok_v2_ctx_separated)
    {
        eprintln!("DEMO SELF-CHECK FAILED");
        std::process::exit(1);
    }
}
