/* Q-SEAL TBS-V2 reference (de)serializer. See tbs_v2.h. Verified against QSEAL_TBS_V2.cry by
 * qseal/proof/tbs_v2.saw. Fixed offsets, constant-size copies, no slicing. */
#include "tbs_v2.h"

static const uint8_t QSEAL_MAGIC[5] = { 'Q', 'S', 'E', 'A', 'L' };

/* local constant-size byte copy (avoids a libc dependency in the bitcode) */
static void cpy(uint8_t *dst, const uint8_t *src, unsigned n) {
    for (unsigned i = 0; i < n; i++) dst[i] = src[i];
}

void qseal_tbs_v2_serialize(const qseal_tbs_v2_t *t, uint8_t out[QSEAL_TBS_V2_LEN]) {
    unsigned o = 0;
    cpy(out + o, QSEAL_MAGIC,                 5); o += 5;
    cpy(out + o, t->version,                  1); o += 1;
    cpy(out + o, t->suite_id,                 2); o += 2;
    cpy(out + o, t->assertion_type,           1); o += 1;
    cpy(out + o, t->assertion_origin,         1); o += 1;
    cpy(out + o, t->issuer_id,               16); o += 16;
    cpy(out + o, t->verifier_id,             16); o += 16;
    cpy(out + o, t->ak_id,                   16); o += 16;
    cpy(out + o, t->pair_commitment,         32); o += 32;
    cpy(out + o, t->request_id,              16); o += 16;
    cpy(out + o, t->nonce,                   32); o += 32;
    cpy(out + o, t->policy_id,                4); o += 4;
    cpy(out + o, t->issued_at,                8); o += 8;
    cpy(out + o, t->expires_at,               8); o += 8;
    cpy(out + o, t->subject_ref,             32); o += 32;
    cpy(out + o, t->object_hash_algorithm,    1); o += 1;
    cpy(out + o, t->object_length,            8); o += 8;
    cpy(out + o, t->object_digest,           32); o += 32;
    cpy(out + o, t->associated_claim_digest, 32); o += 32;
    /* o == QSEAL_TBS_V2_LEN == 263 */
}

int qseal_tbs_v2_parse(const uint8_t in[QSEAL_TBS_V2_LEN], qseal_tbs_v2_t *t) {
    for (unsigned i = 0; i < 5; i++)
        if (in[i] != QSEAL_MAGIC[i]) return 0;
    unsigned o = 5;
    cpy(t->version,                 in + o,  1); o += 1;
    cpy(t->suite_id,                in + o,  2); o += 2;
    cpy(t->assertion_type,          in + o,  1); o += 1;
    cpy(t->assertion_origin,        in + o,  1); o += 1;
    cpy(t->issuer_id,               in + o, 16); o += 16;
    cpy(t->verifier_id,             in + o, 16); o += 16;
    cpy(t->ak_id,                   in + o, 16); o += 16;
    cpy(t->pair_commitment,         in + o, 32); o += 32;
    cpy(t->request_id,              in + o, 16); o += 16;
    cpy(t->nonce,                   in + o, 32); o += 32;
    cpy(t->policy_id,               in + o,  4); o += 4;
    cpy(t->issued_at,               in + o,  8); o += 8;
    cpy(t->expires_at,              in + o,  8); o += 8;
    cpy(t->subject_ref,             in + o, 32); o += 32;
    cpy(t->object_hash_algorithm,   in + o,  1); o += 1;
    cpy(t->object_length,           in + o,  8); o += 8;
    cpy(t->object_digest,           in + o, 32); o += 32;
    cpy(t->associated_claim_digest, in + o, 32); o += 32;
    return 1;
}

/* MUTANT, used only for the non-vacuity check in qseal/proof/tbs_v2.saw. Nothing calls it. It zeroes
 * the pair_commitment slot instead of writing it, so the signed bytes no longer commit to the hybrid
 * key pair: the defect the model-level collision witness (omitting_commitment_breaks_binding) targets,
 * here at the C level. */
void qseal_tbs_v2_serialize_nocommit(const qseal_tbs_v2_t *t, uint8_t out[QSEAL_TBS_V2_LEN]) {
    unsigned o = 0;
    cpy(out + o, QSEAL_MAGIC,                 5); o += 5;
    cpy(out + o, t->version,                  1); o += 1;
    cpy(out + o, t->suite_id,                 2); o += 2;
    cpy(out + o, t->assertion_type,           1); o += 1;
    cpy(out + o, t->assertion_origin,         1); o += 1;
    cpy(out + o, t->issuer_id,               16); o += 16;
    cpy(out + o, t->verifier_id,             16); o += 16;
    cpy(out + o, t->ak_id,                   16); o += 16;
    for (unsigned i = 0; i < 32; i++) out[o + i] = 0; o += 32;   /* BUG: commitment not written */
    cpy(out + o, t->request_id,              16); o += 16;
    cpy(out + o, t->nonce,                   32); o += 32;
    cpy(out + o, t->policy_id,                4); o += 4;
    cpy(out + o, t->issued_at,                8); o += 8;
    cpy(out + o, t->expires_at,               8); o += 8;
    cpy(out + o, t->subject_ref,             32); o += 32;
    cpy(out + o, t->object_hash_algorithm,    1); o += 1;
    cpy(out + o, t->object_length,            8); o += 8;
    cpy(out + o, t->object_digest,           32); o += 32;
    cpy(out + o, t->associated_claim_digest, 32); o += 32;
}

/* MUTANT (not fail-closed): skips the magic check, so it decodes any 263 bytes and returns 1. Must NOT
 * satisfy the reject spec in qseal/proof/tbs_v2.saw. */
int qseal_tbs_v2_parse_nomagic(const uint8_t in[QSEAL_TBS_V2_LEN], qseal_tbs_v2_t *t) {
    unsigned o = 5;
    cpy(t->version,                 in + o,  1); o += 1;
    cpy(t->suite_id,                in + o,  2); o += 2;
    cpy(t->assertion_type,          in + o,  1); o += 1;
    cpy(t->assertion_origin,        in + o,  1); o += 1;
    cpy(t->issuer_id,               in + o, 16); o += 16;
    cpy(t->verifier_id,             in + o, 16); o += 16;
    cpy(t->ak_id,                   in + o, 16); o += 16;
    cpy(t->pair_commitment,         in + o, 32); o += 32;
    cpy(t->request_id,              in + o, 16); o += 16;
    cpy(t->nonce,                   in + o, 32); o += 32;
    cpy(t->policy_id,               in + o,  4); o += 4;
    cpy(t->issued_at,               in + o,  8); o += 8;
    cpy(t->expires_at,              in + o,  8); o += 8;
    cpy(t->subject_ref,             in + o, 32); o += 32;
    cpy(t->object_hash_algorithm,   in + o,  1); o += 1;
    cpy(t->object_length,           in + o,  8); o += 8;
    cpy(t->object_digest,           in + o, 32); o += 32;
    cpy(t->associated_claim_digest, in + o, 32); o += 32;
    return 1;
}

