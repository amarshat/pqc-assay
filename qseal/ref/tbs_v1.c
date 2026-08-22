/* Q-SEAL TBS-V1 reference (de)serializer. See tbs_v1.h. Verified against QSEAL_TBS.cry by
 * qseal/proof/tbs_v1.saw. Fixed offsets, constant-size copies, no slicing. */
#include "tbs_v1.h"

static const uint8_t QSEAL_MAGIC[5] = { 'Q', 'S', 'E', 'A', 'L' };

/* local constant-size byte copy (avoids a libc dependency in the bitcode) */
static void cpy(uint8_t *dst, const uint8_t *src, unsigned n) {
    for (unsigned i = 0; i < n; i++) dst[i] = src[i];
}

void qseal_tbs_serialize(const qseal_tbs_t *t, uint8_t out[QSEAL_TBS_LEN]) {
    unsigned o = 0;
    cpy(out + o, QSEAL_MAGIC,                 5); o += 5;
    cpy(out + o, t->version,                  1); o += 1;
    cpy(out + o, t->suite_id,                 2); o += 2;
    cpy(out + o, t->assertion_type,           1); o += 1;
    cpy(out + o, t->assertion_origin,         1); o += 1;
    cpy(out + o, t->issuer_id,               16); o += 16;
    cpy(out + o, t->verifier_id,             16); o += 16;
    cpy(out + o, t->ak_id,                   16); o += 16;
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
    /* o == QSEAL_TBS_LEN == 231 */
}

int qseal_tbs_parse(const uint8_t in[QSEAL_TBS_LEN], qseal_tbs_t *t) {
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

/* Deliberate mutants, used only for the non-vacuity checks in qseal/proof/tbs_v1.saw. They are not
 * part of the reference; nothing calls them. Each breaks exactly one clause of property 1. */

/* MUTANT (not injective): fills the verifier_id slot from issuer_id, so the serialized transcript does
 * not carry the verifier the request named, and two transcripts differing only in verifier_id map to
 * the same 231 bytes. This is the transcript-malleability class property 1 forbids. */
void qseal_tbs_serialize_aliased(const qseal_tbs_t *t, uint8_t out[QSEAL_TBS_LEN]) {
    unsigned o = 0;
    cpy(out + o, QSEAL_MAGIC,                 5); o += 5;
    cpy(out + o, t->version,                  1); o += 1;
    cpy(out + o, t->suite_id,                 2); o += 2;
    cpy(out + o, t->assertion_type,           1); o += 1;
    cpy(out + o, t->assertion_origin,         1); o += 1;
    cpy(out + o, t->issuer_id,               16); o += 16;
    cpy(out + o, t->issuer_id,               16); o += 16;   /* BUG: verifier_id slot, issuer_id data */
    cpy(out + o, t->ak_id,                   16); o += 16;
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

/* MUTANT (off-by-one field offset): reads the nonce one byte early, so parse is no longer the
 * serializer's inverse and the round trip breaks. */
int qseal_tbs_parse_shifted(const uint8_t in[QSEAL_TBS_LEN], qseal_tbs_t *t) {
    for (unsigned i = 0; i < 5; i++)
        if (in[i] != QSEAL_MAGIC[i]) return 0;
    unsigned o = 5;
    cpy(t->version,                 in + o,      1); o += 1;
    cpy(t->suite_id,                in + o,      2); o += 2;
    cpy(t->assertion_type,          in + o,      1); o += 1;
    cpy(t->assertion_origin,        in + o,      1); o += 1;
    cpy(t->issuer_id,               in + o,     16); o += 16;
    cpy(t->verifier_id,             in + o,     16); o += 16;
    cpy(t->ak_id,                   in + o,     16); o += 16;
    cpy(t->request_id,              in + o,     16); o += 16;
    cpy(t->nonce,                   in + o - 1, 32); o += 32;   /* BUG: one byte early */
    cpy(t->policy_id,               in + o,      4); o += 4;
    cpy(t->issued_at,               in + o,      8); o += 8;
    cpy(t->expires_at,              in + o,      8); o += 8;
    cpy(t->subject_ref,             in + o,     32); o += 32;
    cpy(t->object_hash_algorithm,   in + o,      1); o += 1;
    cpy(t->object_length,           in + o,      8); o += 8;
    cpy(t->object_digest,           in + o,     32); o += 32;
    cpy(t->associated_claim_digest, in + o,     32); o += 32;
    return 1;
}

/* MUTANT (not fail-closed): skips the magic check, so it accepts and decodes any 231 bytes. Must NOT
 * satisfy the reject spec in qseal/proof/tbs_v1.saw, which requires return 0 and an untouched struct
 * on input that does not carry the magic prefix. */
int qseal_tbs_parse_nomagic(const uint8_t in[QSEAL_TBS_LEN], qseal_tbs_t *t) {
    unsigned o = 5;
    cpy(t->version,                 in + o,  1); o += 1;
    cpy(t->suite_id,                in + o,  2); o += 2;
    cpy(t->assertion_type,          in + o,  1); o += 1;
    cpy(t->assertion_origin,        in + o,  1); o += 1;
    cpy(t->issuer_id,               in + o, 16); o += 16;
    cpy(t->verifier_id,             in + o, 16); o += 16;
    cpy(t->ak_id,                   in + o, 16); o += 16;
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
