//! Integration test: real hybrid crypto over the Cap-V1 canonical bytes, driving the actual verified
//! accept decision.
//!
//! This is the "post-quantum actually runs" half of the layer. It generates real ECDSA P-256 and
//! ML-DSA-44 keys, signs `serialize(cap)` (the exact bytes the Kani `signed_message` harnesses pin),
//! verifies both, and feeds the outcomes plus the key commitments into the *same*
//! `accept_chain2_signed` / `accept_leaf_signed` that Kani proved the glue for. So the assumed `sig_ok`
//! bit in the proofs is discharged here by an actual hybrid verify, and the key-commitment bytes come
//! from the library's deployment definition (`hyb1::hyb1_key_id`, truncated domain-separated SHA-256
//! of the encoded hybrid key), carried into the gates by the machine-checked `committing_to` bridge.
//!
//! Scenarios: valid accepts; tampered message rejects; downgrade (only the classical signature valid)
//! rejects where accept-on-either would pass; confused deputy (leaf validly signed by a key that is
//! not the delegated one) rejects even though the signature verifies; expired rejects.

use cap_v1::*;

use ml_dsa::{Generate, Keypair, MlDsa44};
use ml_dsa::{
    Signature as MlSig, Signer as MlSign, SigningKey as MlSk, Verifier as MlVerify,
    VerifyingKey as MlVk,
};
use p256::ecdsa::signature::{Signer as EcSign, Verifier as EcVerify};
use p256::ecdsa::{Signature as EcSig, SigningKey as EcSk, VerifyingKey as EcVk};
use rand_core::OsRng;

struct Sk {
    ec: EcSk,
    ml: MlSk<MlDsa44>,
}
struct Pk {
    ec: EcVk,
    ml: MlVk<MlDsa44>,
}
struct HSig {
    ec: EcSig,
    ml: MlSig<MlDsa44>,
}

fn keygen() -> (Sk, Pk) {
    let ec = EcSk::random(&mut OsRng);
    let ec_pub = *ec.verifying_key();
    let ml = MlSk::<MlDsa44>::generate();
    let ml_pub = ml.verifying_key();
    (Sk { ec, ml }, Pk { ec: ec_pub, ml: ml_pub })
}

fn hybrid_sign(sk: &Sk, msg: &[u8]) -> HSig {
    HSig {
        ec: sk.ec.sign(msg),
        ml: sk.ml.sign(msg),
    }
}

/// HYB-1 accept is the AND of the two verifications, over the same bytes. Returns (classical_ok, pq_ok).
fn hybrid_verify(pk: &Pk, msg: &[u8], sig: &HSig) -> (bool, bool) {
    let ec_ok = pk.ec.verify(msg, &sig.ec).is_ok();
    let ml_ok = pk.ml.verify(msg, &sig.ml).is_ok();
    (ec_ok, ml_ok)
}

/// The real key commitment, computed by the library's deployment definition (`hyb1::hyb1_key_id`,
/// truncated domain-separated SHA-256 over the encoded hybrid key). This is what `issuer_id` /
/// `subject_id` bind to; the same definition, not a test-local copy, so the bytes the verified gates
/// compare are the deployed ones.
fn commit(pk: &Pk) -> [u8; 16] {
    let ec = pk.ec.to_encoded_point(true);
    let ec_bytes: &[u8; hyb1::EC_P256_COMPRESSED_LEN] =
        ec.as_bytes().try_into().expect("compressed P-256 point is 33 bytes");
    let ml = pk.ml.encode();
    let ml_bytes: &[u8; hyb1::ML_DSA_44_PK_LEN] =
        (&ml[..]).try_into().expect("ML-DSA-44 public key encodes to 1312 bytes");
    hyb1::hyb1_key_id(ec_bytes, ml_bytes)
}

/// The model `PublicKey` whose `key_id(..)` equals `id`: the library bridge, machine-checked by the
/// `committing_to_commits` harness, so the verified `accept_*_signed` see exactly the deployment
/// commitment `commit()` computes.
fn model_pk(id: [u8; 16]) -> PublicKey {
    PublicKey::committing_to(id)
}

fn root_cap(owner_id: [u8; 16], delegate_id: [u8; 16]) -> CapV1 {
    let mut c = CapV1::zeroed();
    c.version = [1];
    c.suite_id = [0, 1];
    c.issuer_id = owner_id; // signed by the resource owner
    c.subject_id = delegate_id; // delegates to `delegate`
    c.cap_id = [0xBB; 16];
    c.resource_id = [0x44; 32];
    c.audience_id = [0x77; 16];
    c.max_depth = [3];
    c.action = [0, 0, 0, 0b0000_0011];
    c.not_before = 100u64.to_be_bytes();
    c.not_after = 200u64.to_be_bytes();
    c
}

fn leaf_cap(root: &CapV1, delegate_id: [u8; 16], bearer_id: [u8; 16]) -> CapV1 {
    let mut c = CapV1::zeroed();
    c.version = [1];
    c.suite_id = root.suite_id;
    c.issuer_id = delegate_id; // issued by the delegate
    c.subject_id = bearer_id;
    c.parent_id = root.cap_id;
    c.resource_id = root.resource_id;
    c.audience_id = root.audience_id;
    c.max_depth = [2];
    c.action = [0, 0, 0, 0b0000_0001]; // attenuated
    c.not_before = 120u64.to_be_bytes();
    c.not_after = 180u64.to_be_bytes();
    c
}

#[test]
fn hybrid_chain_accepts_and_rejects() {
    let (owner_sk, owner_pk) = keygen();
    let (deleg_sk, deleg_pk) = keygen();
    let (foreign_sk, foreign_pk) = keygen();

    let owner_id = commit(&owner_pk);
    let deleg_id = commit(&deleg_pk);

    let root = root_cap(owner_id, deleg_id);
    let leaf = leaf_cap(&root, deleg_id, [0xEE; 16]);

    let root_bytes = serialize(&root);
    let leaf_bytes = serialize(&leaf);

    // Real signatures over the canonical bytes.
    let root_sig = hybrid_sign(&owner_sk, &root_bytes);
    let leaf_sig = hybrid_sign(&deleg_sk, &leaf_bytes);

    let verifier = [0x77; 16];
    let now = 150u64;

    // 1. Valid chain accepts. Both hybrid verifies pass; keys commit to the named ids.
    let (rc, rp) = hybrid_verify(&owner_pk, &root_bytes, &root_sig);
    let (lc, lp) = hybrid_verify(&deleg_pk, &leaf_bytes, &leaf_sig);
    assert!(rc && rp && lc && lp, "real hybrid verify should pass on untampered bytes");
    assert!(accept_chain2_signed(
        &root,
        &leaf,
        &verifier,
        now,
        &model_pk(owner_id),
        rc && rp,
        &model_pk(deleg_id),
        lc && lp,
    ));
    assert!(accept_leaf_signed(&leaf, &verifier, now, &model_pk(deleg_id), lc && lp));

    // 2. Tampered leaf: attacker escalates the action after signing. Verify the old signature against
    // the new bytes -> fails, and the chain is rejected.
    let mut tampered = leaf;
    tampered.action = [0, 0, 0, 0xFF];
    let tampered_bytes = serialize(&tampered);
    let (tc, tp) = hybrid_verify(&deleg_pk, &tampered_bytes, &leaf_sig);
    assert!(!(tc && tp), "signature must not verify over tampered bytes");
    assert!(!accept_chain2_signed(
        &root, &leaf, &verifier, now, &model_pk(owner_id), rc && rp, &model_pk(deleg_id), tc && tp,
    ));

    // 3. Downgrade: only the classical signature is valid (PQ signature is over other bytes). HYB-1
    // AND rejects; an accept-on-either verifier (lc || lp_bad) would have wrongly accepted.
    let other = keygen().0;
    let bad_ml = other.ml.sign(b"not the leaf");
    let downgrade = HSig { ec: leaf_sig.ec.clone(), ml: bad_ml };
    let (dc, dp) = hybrid_verify(&deleg_pk, &leaf_bytes, &downgrade);
    assert!(dc && !dp, "classical valid, PQ invalid");
    assert!(
        !accept_leaf_signed(&leaf, &verifier, now, &model_pk(deleg_id), dc && dp),
        "AND-of-both rejects the downgrade"
    );
    assert!(dc || dp, "accept-on-either would have accepted: this is the downgrade the AND catches");

    // 4. Confused deputy: the leaf is validly signed, but by a foreign key, not the delegated one.
    // The hybrid verify PASSES, yet the chain is rejected because the key does not commit to the
    // named issuer.
    let cd_sig = hybrid_sign(&foreign_sk, &leaf_bytes);
    let (fc, fp) = hybrid_verify(&foreign_pk, &leaf_bytes, &cd_sig);
    assert!(fc && fp, "foreign key really did sign the leaf");
    assert!(
        !accept_chain2_signed(
            &root, &leaf, &verifier, now, &model_pk(owner_id), rc && rp, &model_pk(commit(&foreign_pk)), fc && fp,
        ),
        "valid signature under the wrong key must not accept"
    );

    // 5. Expired: now past not_after. Rejected.
    assert!(!accept_leaf_signed(&leaf, &verifier, 999, &model_pk(deleg_id), lc && lp));
}
