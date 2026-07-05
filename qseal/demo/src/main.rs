//! Runnable Q-SEAL hybrid attestation demo.
//!
//! Real crypto: ECDSA P-256 (classical) + ML-DSA-44 (post-quantum, the RustCrypto crate this project
//! formally verifies), signing the verified TBS-V1 transcript. HYB-1 acceptance requires BOTH
//! signatures over the SAME transcript, matching the SAW-proved qseal/proof/hybrid.saw. This binary
//! shows three outcomes with no proof toolchain needed:
//!   1. a valid attestation accepts,
//!   2. a tampered transcript is rejected,
//!   3. a downgrade (valid classical signature, no valid PQ signature) is rejected, where a buggy
//!      "accept on either" verifier would have accepted.

mod tbs;
use tbs::{create_assertion, AppletId, Request};

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

    println!("\nHYB-1 accepts only when both signatures verify over the same transcript.");
    println!("That acceptance rule is machine-checked in qseal/proof/hybrid.saw.");

    // Non-zero exit if the demo does not behave (keeps it usable as a check).
    let (c1, q1) = verify_both(&pk, &tbs, &sig);
    let ok_valid = c1 && q1;
    let (ct, qt) = verify_both(&pk, &tampered, &sig);
    let ok_tamper_rejected = !(ct && qt);
    let (cd, qd) = verify_both(&pk, &tbs, &downgrade);
    let ok_downgrade_rejected = !(cd && qd) && cd; // rejected overall, but classical alone was valid
    if !(ok_valid && ok_tamper_rejected && ok_downgrade_rejected) {
        eprintln!("DEMO SELF-CHECK FAILED");
        std::process::exit(1);
    }
}
