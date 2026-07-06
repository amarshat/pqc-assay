/* Q-SEAL single-use challenge store reference (section 16 property 4: a consumed request_id cannot be
 * accepted twice). Verified against QSEAL_Nonce.cry by qseal/proof/nonce.saw. The signature/policy
 * checks are folded into the `ok` bit (property 3, opaque here); this file is only the consume-once
 * state machine. Capacity is fixed and small so the proof stays bounded; the single-use logic is
 * independent of it. */
#ifndef QSEAL_NONCE_H
#define QSEAL_NONCE_H

#include <stdint.h>

#define QSEAL_REQID_LEN 16
#define QSEAL_STORE_CAP 8

/* Append-only single-use store: the first `count` slots hold consumed request_ids. Field order and
 * types match the Cryptol Store record (count : [8], slots : [CAP][16][8]). */
typedef struct qseal_nonce_store_t {
    uint8_t count;
    uint8_t slots[QSEAL_STORE_CAP][QSEAL_REQID_LEN];
} qseal_nonce_store_t;

/* Returns 1 iff r is already among the first `count` slots (already consumed). */
int qseal_nonce_seen(const qseal_nonce_store_t *s, const uint8_t r[QSEAL_REQID_LEN]);

/* The verifier's single-use decision for an otherwise-validated request (ok nonzero = signatures and
 * policy already checked). Accept iff validated, r not already consumed, and the store is not full
 * (fail-closed). On accept, records r and returns 1; otherwise leaves the store unchanged and returns
 * 0. */
int qseal_nonce_accept(qseal_nonce_store_t *s, int ok, const uint8_t r[QSEAL_REQID_LEN]);

/* Deliberate replay bug used only for the mutation demonstration: makes the same accept decision but
 * never records the request_id, so the same request is accepted again. */
int qseal_nonce_accept_noconsume(qseal_nonce_store_t *s, int ok, const uint8_t r[QSEAL_REQID_LEN]);

#endif
