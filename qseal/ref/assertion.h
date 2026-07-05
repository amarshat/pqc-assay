/* Q-SEAL CREATE_ASSERTION reference: the applet builds TBS-V1 internally from the validated request
 * (challenge fields) plus its own identity fields, then serializes. The host supplies fields, never an
 * encoded transcript, so the signed bytes bind the challenge and cannot spoof the applet identity.
 * Verified against QSEAL_Assertion.cry (`create`) by qseal/proof/assertion.saw. */
#ifndef QSEAL_ASSERTION_H
#define QSEAL_ASSERTION_H

#include "tbs_v1.h"

/* Challenge/request fields supplied by the host (everything the applet does not control). */
typedef struct {
    uint8_t suite_id[2];
    uint8_t assertion_type[1];
    uint8_t assertion_origin[1];
    uint8_t verifier_id[16];
    uint8_t request_id[16];
    uint8_t nonce[32];
    uint8_t policy_id[4];
    uint8_t expires_at[8];
    uint8_t subject_ref[32];
    uint8_t object_hash_algorithm[1];
    uint8_t object_length[8];
    uint8_t object_digest[32];
    uint8_t associated_claim_digest[32];
} qseal_request_t;

/* Applet-controlled fields (never from the host): protocol version, issuer + attestation-key
 * identity, and the applet clock stamp. */
typedef struct {
    uint8_t version[1];
    uint8_t issuer_id[16];
    uint8_t ak_id[16];
    uint8_t issued_at[8];
} qseal_applet_id_t;

/* Build TBS-V1 from (request, applet identity) and serialize into out[QSEAL_TBS_LEN]. */
void qseal_create_assertion(const qseal_request_t *r, const qseal_applet_id_t *a,
                            uint8_t out[QSEAL_TBS_LEN]);

#endif
