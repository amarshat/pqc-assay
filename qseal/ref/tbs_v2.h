/* Q-SEAL TBS-V2 reference (de)serializer, C.
 *
 * Fixed 263-byte transcript, no optional fields (Q-SEAL spec section 7.1, v0.2 draft): TBS-V1
 * plus a 32-byte pair_commitment directly after ak_id, binding the hybrid key pair inside the
 * signed bytes. Same discipline as tbs_v1: fixed offsets, constant-size copies, no slicing.
 * The SAW harness (qseal/proof/tbs_v2.saw) proves serialize/parse here compute exactly the
 * Cryptol model qseal/model/QSEAL_TBS_V2.cry, which is proven bijective and injective with the
 * commitment signed and position-pinned.
 */
#ifndef QSEAL_TBS_V2_H
#define QSEAL_TBS_V2_H

#include <stdint.h>

#define QSEAL_TBS_V2_LEN 263

/* Field layout matches QSEAL_TBS_V2.cry exactly (byte lengths and order). */
typedef struct {
    uint8_t version[1];
    uint8_t suite_id[2];
    uint8_t assertion_type[1];
    uint8_t assertion_origin[1];
    uint8_t issuer_id[16];
    uint8_t verifier_id[16];
    uint8_t ak_id[16];
    uint8_t pair_commitment[32];
    uint8_t request_id[16];
    uint8_t nonce[32];
    uint8_t policy_id[4];
    uint8_t issued_at[8];
    uint8_t expires_at[8];
    uint8_t subject_ref[32];
    uint8_t object_hash_algorithm[1];
    uint8_t object_length[8];
    uint8_t object_digest[32];
    uint8_t associated_claim_digest[32];
} qseal_tbs_v2_t;

/* Serialize the record into exactly QSEAL_TBS_V2_LEN bytes, magic "QSEAL" first. */
void qseal_tbs_v2_serialize(const qseal_tbs_v2_t *t, uint8_t out[QSEAL_TBS_V2_LEN]);

/* Parse QSEAL_TBS_V2_LEN bytes into the record. Returns 1 if the magic prefix matches, else 0
 * (and leaves *t unmodified on reject). */
int qseal_tbs_v2_parse(const uint8_t in[QSEAL_TBS_V2_LEN], qseal_tbs_v2_t *t);

/* Deliberate mutant used only for the mutation demonstration in qseal/proof/tbs_v2.saw: zeroes the
 * pair_commitment slot, so the transcript does not commit to the hybrid key pair. */
void qseal_tbs_v2_serialize_nocommit(const qseal_tbs_v2_t *t, uint8_t out[QSEAL_TBS_V2_LEN]);

#endif
