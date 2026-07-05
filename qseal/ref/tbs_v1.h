/* Q-SEAL TBS-V1 reference (de)serializer, C.
 *
 * Fixed 231-byte transcript, no optional fields (Q-SEAL v0.1 section 7). This is a reference
 * implementation deliberately written to be verifiable: fixed offsets, constant-size memcpy, no
 * slicing tricks. The SAW harness (qseal/proof/tbs_v1.saw) proves serialize/parse here compute
 * exactly the Cryptol model qseal/model/QSEAL_TBS.cry, which is proven bijective and injective.
 */
#ifndef QSEAL_TBS_V1_H
#define QSEAL_TBS_V1_H

#include <stdint.h>

#define QSEAL_TBS_LEN 231

/* Field layout matches QSEAL_TBS.cry exactly (byte lengths and order). */
typedef struct {
    uint8_t version[1];
    uint8_t suite_id[2];
    uint8_t assertion_type[1];
    uint8_t assertion_origin[1];
    uint8_t issuer_id[16];
    uint8_t verifier_id[16];
    uint8_t ak_id[16];
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
} qseal_tbs_t;

/* Serialize the record into exactly QSEAL_TBS_LEN bytes, magic "QSEAL" first. */
void qseal_tbs_serialize(const qseal_tbs_t *t, uint8_t out[QSEAL_TBS_LEN]);

/* Parse QSEAL_TBS_LEN bytes into the record. Returns 1 if the magic prefix matches, else 0
 * (and leaves *t unmodified on reject). */
int qseal_tbs_parse(const uint8_t in[QSEAL_TBS_LEN], qseal_tbs_t *t);

#endif
