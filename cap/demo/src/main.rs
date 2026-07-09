//! Runnable Cap-V1 agent-delegation demo.
//!
//! Real crypto: ECDSA P-256 (classical) + ML-DSA-44 (post-quantum, the RustCrypto crate this
//! project formally verifies), signing the canonical 191-byte capability bytes. The accept
//! decisions below are made by `accept_chain_full`, the deployment gate whose composition and
//! rules the library's Kani harnesses cover (55 harnesses over the library, `make cap-kani`).
//! Key commitments come from the library's deployment definition (`hyb1::hyb1_key_id`, truncated
//! domain-separated SHA-256, KAT-pinned; the hash itself is not harness-covered, SHA-256 is out
//! of Kani's reach). No proof toolchain needed to run this.
//!
//! The cast: an orchestrator (resource owner) delegates a scoped capability to an agent; the
//! agent re-delegates an attenuated leaf to a worker, which presents the chain to a tool server
//! (the verifier). Eight outcomes:
//!   1. a valid delegation chain accepts,
//!   2. replaying the same presentation is rejected (single-use store consumed the leaf),
//!   3. tampering with the leaf after signing is rejected (signature dies),
//!   4. an escalated leaf (action bit the root never granted) is rejected even though its
//!      signature is VALID: an authorization failure, not a forgery,
//!   5. a leaf signed by a key the chain never delegated to is rejected despite a valid
//!      signature (confused deputy; the token pins its signer),
//!   6. a downgrade (valid classical signature, invalid post-quantum one) is rejected, where an
//!      accept-on-either verifier would have accepted,
//!   7. a terminal leaf (FLAG_DELEGATE cleared) cannot spawn a further delegation,
//!   8. after the orchestrator revokes the root, a fresh, otherwise-valid presentation through
//!      that root is rejected (revocation is checked on every link, not just the leaf).

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
    HSig { ec: sk.ec.sign(msg), ml: sk.ml.sign(msg) }
}

/// HYB-1 accept is the AND of the two verifications over the same bytes.
fn hybrid_verify(pk: &Pk, msg: &[u8], sig: &HSig) -> (bool, bool) {
    (pk.ec.verify(msg, &sig.ec).is_ok(), pk.ml.verify(msg, &sig.ml).is_ok())
}

/// The real key commitment, via the library's deployment definition.
fn commit(pk: &Pk) -> [u8; 16] {
    let ec = pk.ec.to_encoded_point(true);
    let ec_bytes: &[u8; hyb1::EC_P256_COMPRESSED_LEN] =
        ec.as_bytes().try_into().expect("compressed P-256 point is 33 bytes");
    let ml = pk.ml.encode();
    let ml_bytes: &[u8; hyb1::ML_DSA_44_PK_LEN] =
        (&ml[..]).try_into().expect("ML-DSA-44 public key encodes to 1312 bytes");
    hyb1::hyb1_key_id(ec_bytes, ml_bytes)
}

const TOOL_SERVER: [u8; 16] = *b"tool-server-0001";
const NOW: u64 = 150;

/// The root grant: orchestrator -> agent. Read+write, re-delegable, depth budget 2.
fn root_cap(owner_id: [u8; 16], agent_id: [u8; 16]) -> CapV1 {
    let mut c = CapV1::zeroed();
    c.version = VERSION_V1;
    c.suite_id = SUITE_HYB1;
    c.issuer_id = owner_id;
    c.subject_id = agent_id;
    c.cap_id = [0xA1; 16];
    c.resource_id = [0x44; 32];
    c.audience_id = TOOL_SERVER;
    c.max_depth = [2];
    c.flags = [FLAG_DELEGATE];
    c.action = [0, 0, 0, 0b0000_0011]; // read | write
    c.not_before = 100u64.to_be_bytes();
    c.not_after = 200u64.to_be_bytes();
    c.nonce = [0x01; 16];
    c
}

/// An attenuated leaf: agent -> worker. Read only, terminal (FLAG_DELEGATE cleared), narrower
/// window, fresh cap_id and nonce per presentation.
fn leaf_cap(root: &CapV1, agent_id: [u8; 16], worker_id: [u8; 16], serial: u8) -> CapV1 {
    let mut c = CapV1::zeroed();
    c.version = VERSION_V1;
    c.suite_id = root.suite_id;
    c.issuer_id = agent_id;
    c.subject_id = worker_id;
    c.parent_id = root.cap_id;
    c.cap_id = [serial; 16];
    c.resource_id = root.resource_id;
    c.audience_id = root.audience_id;
    c.max_depth = [1];
    c.flags = [0]; // terminal
    c.action = [0, 0, 0, 0b0000_0001]; // read only
    c.constraints_digest = root.constraints_digest;
    c.not_before = 120u64.to_be_bytes();
    c.not_after = 180u64.to_be_bytes();
    c.nonce = [serial ^ 0xFF; 16];
    c
}

fn outcome(b: bool) -> &'static str {
    if b {
        "ACCEPT"
    } else {
        "REJECT"
    }
}

fn main() {
    println!(
        "Cap-V1 agent-delegation demo (ECDSA P-256 + ML-DSA-44 driving the Kani-verified gates)\n"
    );

    let (owner_sk, owner_pk) = keygen();
    let (agent_sk, agent_pk) = keygen();
    let (worker_sk, worker_pk) = keygen();
    let (foreign_sk, foreign_pk) = keygen();

    let owner_id = commit(&owner_pk);
    let agent_id = commit(&agent_pk);
    let worker_id = commit(&worker_pk);

    let root = root_cap(owner_id, agent_id);
    let leaf = leaf_cap(&root, agent_id, worker_id, 0xB1);
    let root_bytes = serialize(&root);
    let leaf_bytes = serialize(&leaf);
    let root_sig = hybrid_sign(&owner_sk, &root_bytes);
    let leaf_sig = hybrid_sign(&agent_sk, &leaf_bytes);
    println!(
        "orchestrator granted read|write to the agent (191-byte capability, re-delegable, depth 2);"
    );
    println!("agent re-delegated read-only, terminal, narrower-window leaf to the worker\n");

    let pks = [PublicKey::committing_to(owner_id), PublicKey::committing_to(agent_id)];
    let store = NonceStore::empty();
    let no_revocations = RevocationStore::empty();
    let mut results: Vec<(&str, bool, bool)> = Vec::new(); // (label, got, expected)

    // 1. Valid chain accepts. Both hybrid signatures verify; keys commit to the named issuers.
    let (rc, rp) = hybrid_verify(&owner_pk, &root_bytes, &root_sig);
    let (lc, lp) = hybrid_verify(&agent_pk, &leaf_bytes, &leaf_sig);
    let sigs = [rc && rp, lc && lp];
    let (v1, store) =
        accept_chain_full(&[root, leaf], &TOOL_SERVER, NOW, &pks, &sigs, &store, &no_revocations);
    println!("1. valid delegation chain      sigs=[{:5},{:5}]  ->  {}", sigs[0], sigs[1], outcome(v1));
    results.push(("valid chain", v1, true));

    // 2. Replay of the same presentation: the store consumed the leaf's replay key on accept.
    let (v2, store) =
        accept_chain_full(&[root, leaf], &TOOL_SERVER, NOW, &pks, &sigs, &store, &no_revocations);
    println!("2. replay, same leaf           sigs unchanged     ->  {}", outcome(v2));
    println!("   a gate without the single-use store would have returned ACCEPT again.");
    results.push(("replay", v2, false));

    // 3. Tamper after signing: flip the leaf's action byte, verify the old signature over the new
    // bytes. The signature covers all 191 bytes (signed_message_covers_all_fields), so it dies.
    let mut tampered = leaf;
    tampered.action = [0, 0, 0, 0b0000_0011];
    let (tc, tp) = hybrid_verify(&agent_pk, &serialize(&tampered), &leaf_sig);
    let (v3, store) = accept_chain_full(
        &[root, tampered],
        &TOOL_SERVER,
        NOW,
        &pks,
        &[rc && rp, tc && tp],
        &store,
        &no_revocations,
    );
    println!("3. tampered leaf               sigs=[{:5},{:5}]  ->  {}", rc && rp, tc && tp, outcome(v3));
    results.push(("tamper", v3, false));

    // 4. Escalation: the agent SIGNS a leaf claiming an action bit the root never granted. The
    // signature is genuinely valid; the chain-link check (action subset, Kani: link_no_escalation,
    // chain_attenuates) rejects. Authorization failure, not forgery.
    let mut escalated = leaf_cap(&root, agent_id, worker_id, 0xB2);
    escalated.action = [0, 0, 0, 0b0000_0111];
    let esc_bytes = serialize(&escalated);
    let esc_sig = hybrid_sign(&agent_sk, &esc_bytes);
    let (ec_ok, ep_ok) = hybrid_verify(&agent_pk, &esc_bytes, &esc_sig);
    let (v4, store) = accept_chain_full(
        &[root, escalated],
        &TOOL_SERVER,
        NOW,
        &pks,
        &[rc && rp, ec_ok && ep_ok],
        &store,
        &no_revocations,
    );
    println!("4. escalated leaf, valid sig   sigs=[{:5},{:5}]  ->  {}", rc && rp, ec_ok && ep_ok, outcome(v4));
    println!("   the signature IS valid; the link check rejects the action bit the root never granted.");
    results.push(("escalation", v4, false));

    // 5. Confused deputy: a fresh leaf validly signed by a key the chain never delegated to. The
    // hybrid verify passes under the foreign key, but the token names its issuer and the gate
    // requires key_id(presented key) == issuer_id (Kani: confused_deputy_rejected).
    let cd_leaf = leaf_cap(&root, agent_id, worker_id, 0xB3);
    let cd_bytes = serialize(&cd_leaf);
    let cd_sig = hybrid_sign(&foreign_sk, &cd_bytes);
    let (fc, fp) = hybrid_verify(&foreign_pk, &cd_bytes, &cd_sig);
    let cd_pks = [PublicKey::committing_to(owner_id), PublicKey::committing_to(commit(&foreign_pk))];
    let (v5, store) = accept_chain_full(
        &[root, cd_leaf],
        &TOOL_SERVER,
        NOW,
        &cd_pks,
        &[rc && rp, fc && fp],
        &store,
        &no_revocations,
    );
    println!("5. foreign signer, valid sig   sigs=[{:5},{:5}]  ->  {}", rc && rp, fc && fp, outcome(v5));
    println!("   the foreign key really signed the leaf; the key commitment pins the named issuer.");
    results.push(("confused deputy", v5, false));

    // 6. Downgrade: only the classical signature is valid over the leaf (the post-quantum one is
    // over other bytes). HYB-1 requires both; accept-on-either would pass exactly when the
    // classical scheme falls.
    let dg_leaf = leaf_cap(&root, agent_id, worker_id, 0xB4);
    let dg_bytes = serialize(&dg_leaf);
    let good = hybrid_sign(&agent_sk, &dg_bytes);
    let bad_ml = hybrid_sign(&agent_sk, b"not the leaf").ml;
    let downgrade = HSig { ec: good.ec.clone(), ml: bad_ml };
    let (dc, dp) = hybrid_verify(&agent_pk, &dg_bytes, &downgrade);
    let (v6, store) = accept_chain_full(
        &[root, dg_leaf],
        &TOOL_SERVER,
        NOW,
        &pks,
        &[rc && rp, dc && dp],
        &store,
        &no_revocations,
    );
    println!("6. downgrade (classical only)  sigs=[{:5},{:5}]  ->  {}", dc, dp, outcome(v6));
    println!("   an accept-on-either verifier would have returned {} here.", outcome(dc || dp));
    results.push(("downgrade", v6, false));

    // 7. Terminal leaf cannot re-delegate: the worker mints a sub-delegation under the leaf, which
    // cleared FLAG_DELEGATE. Every signature in the 3-link chain is valid; the link check requires
    // the delegation flag on every parent (Kani: link_requires_delegation_flag).
    let leaf2 = leaf_cap(&root, agent_id, worker_id, 0xB5);
    let leaf2_bytes = serialize(&leaf2);
    let leaf2_sig = hybrid_sign(&agent_sk, &leaf2_bytes);
    let (l2c, l2p) = hybrid_verify(&agent_pk, &leaf2_bytes, &leaf2_sig);
    let mut subleaf = leaf_cap(&leaf2, worker_id, commit(&foreign_pk), 0xB6);
    subleaf.max_depth = [0];
    let sub_bytes = serialize(&subleaf);
    let sub_sig = hybrid_sign(&worker_sk, &sub_bytes);
    let (sc, sp) = hybrid_verify(&worker_pk, &sub_bytes, &sub_sig);
    let three_pks = [
        PublicKey::committing_to(owner_id),
        PublicKey::committing_to(agent_id),
        PublicKey::committing_to(worker_id),
    ];
    let (v7, store) = accept_chain_full(
        &[root, leaf2, subleaf],
        &TOOL_SERVER,
        NOW,
        &three_pks,
        &[rc && rp, l2c && l2p, sc && sp],
        &store,
        &no_revocations,
    );
    println!(
        "7. re-delegated terminal leaf  sigs=[{:5},{:5},{:5}]  ->  {}",
        rc && rp,
        l2c && l2p,
        sc && sp,
        outcome(v7)
    );
    println!("   the leaf was minted terminal (FLAG_DELEGATE cleared), so it spawns no children.");
    results.push(("terminal re-delegation", v7, false));

    // 8. Revocation: the orchestrator revokes the root's cap_id. A fresh, otherwise-valid
    // presentation (new leaf, unconsumed nonce, valid signatures) is rejected because the gate
    // checks revocation on every link (Kani: revoked_any_link_kills_chain).
    let (revoked_ok, revocations) = revoke(&no_revocations, &root.cap_id);
    let fresh = leaf_cap(&root, agent_id, worker_id, 0xB7);
    let fresh_bytes = serialize(&fresh);
    let fresh_sig = hybrid_sign(&agent_sk, &fresh_bytes);
    let (nc, np) = hybrid_verify(&agent_pk, &fresh_bytes, &fresh_sig);
    let (v8, _store) = accept_chain_full(
        &[root, fresh],
        &TOOL_SERVER,
        NOW,
        &pks,
        &[rc && rp, nc && np],
        &store,
        &revocations,
    );
    println!("8. fresh leaf, root revoked    sigs=[{:5},{:5}]  ->  {}", rc && rp, nc && np, outcome(v8));
    println!("   a gate that checked revocation on the leaf alone would have returned ACCEPT.");
    results.push(("revoked root", v8, false));
    results.push(("revoke call", revoked_ok, true));

    println!(
        "\nThe gate accepts only a chain whose every link is signed by the key it names, whose"
    );
    println!("authority never exceeds the root grant, exactly once per presented leaf, and not after");
    println!("revocation. Those rules are machine-checked in cap/src/lib.rs (55 Kani harnesses,");
    println!("`make cap-kani`); this binary feeds them real hybrid signatures.");

    let failed: Vec<&(&str, bool, bool)> = results.iter().filter(|(_, got, want)| got != want).collect();
    if !failed.is_empty() {
        for (label, got, want) in &failed {
            eprintln!("DEMO SELF-CHECK FAILED: {label}: got {got}, expected {want}");
        }
        std::process::exit(1);
    }
}
