/* Q-SEAL CREATE_ASSERTION reference. See assertion.h. The applet places the request's challenge
 * fields and its own identity fields into TBS-V1, then serializes. Verified == QSEAL_Assertion.cry
 * `create` by qseal/proof/assertion.saw. Built in one TU with tbs_v1.c (for qseal_tbs_serialize). */
#include "assertion.h"

/* local constant-size copy (distinct name from tbs_v1.c's cpy so the combined TU has no collision) */
static void bcpy(uint8_t *dst, const uint8_t *src, unsigned n) {
    for (unsigned i = 0; i < n; i++) dst[i] = src[i];
}

void qseal_create_assertion(const qseal_request_t *r, const qseal_applet_id_t *a,
                            uint8_t out[QSEAL_TBS_LEN]) {
    qseal_tbs_t t;
    /* applet-controlled identity + clock */
    bcpy(t.version,   a->version,   1);
    bcpy(t.issuer_id, a->issuer_id, 16);
    bcpy(t.ak_id,     a->ak_id,     16);
    bcpy(t.issued_at, a->issued_at, 8);
    /* challenge fields from the validated request */
    bcpy(t.suite_id,                r->suite_id,                2);
    bcpy(t.assertion_type,          r->assertion_type,          1);
    bcpy(t.assertion_origin,        r->assertion_origin,        1);
    bcpy(t.verifier_id,             r->verifier_id,             16);
    bcpy(t.request_id,              r->request_id,              16);
    bcpy(t.nonce,                   r->nonce,                   32);
    bcpy(t.policy_id,               r->policy_id,               4);
    bcpy(t.expires_at,              r->expires_at,              8);
    bcpy(t.subject_ref,             r->subject_ref,             32);
    bcpy(t.object_hash_algorithm,   r->object_hash_algorithm,   1);
    bcpy(t.object_length,           r->object_length,           8);
    bcpy(t.object_digest,           r->object_digest,           32);
    bcpy(t.associated_claim_digest, r->associated_claim_digest, 32);

    qseal_tbs_serialize(&t, out);
}
