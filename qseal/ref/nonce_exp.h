/* Q-SEAL single-use challenge store WITH EXPIRY EVICTION (section 16 property 4, second version).
 * See qseal/model/QSEAL_NonceExp.cry for the model and what changes: the v0.1 store in nonce.c is
 * append-only and fail-closed, so a host that submits CAP distinct validated requests wedges
 * attestation permanently. This one reuses slots whose recorded expiry has passed, which is the
 * retention mechanism the spec names in section 10. The single-use guarantee becomes windowed: a
 * request cannot be replayed while the transcript it came from is still valid.
 * Verified equal to the model by qseal/proof/nonce_exp.saw. */
#ifndef QSEAL_NONCE_EXP_H
#define QSEAL_NONCE_EXP_H

#include <stdint.h>

#define QSEAL_EXP_KEY_LEN 64   /* verifier_id (16) || request_id (16) || nonce (32) */
#define QSEAL_EXP_CAP     8

/* Slot i holds a consumed key and the expiry of the transcript it came from. exps[i] == 0 means the
 * slot was never used; exps[i] <= now means it may be reused. Field order and types match the Cryptol
 * Store record (keys : [CAP][64][8], exps : [CAP][32]). */
typedef struct qseal_nonce_exp_store_t {
    uint8_t  keys[QSEAL_EXP_CAP][QSEAL_EXP_KEY_LEN];
    uint32_t exps[QSEAL_EXP_CAP];
} qseal_nonce_exp_store_t;

/* Accept iff the request is otherwise validated (ok nonzero), its transcript has not expired
 * (now < req_exp), its key is not recorded live, and some slot is free or expired. On accept, records
 * the key with its expiry in the lowest reusable slot and returns 1; otherwise leaves the store
 * unchanged and returns 0. */
int qseal_nonce_exp_accept(qseal_nonce_exp_store_t *s, int ok, const uint8_t k[QSEAL_EXP_KEY_LEN],
                           uint32_t req_exp, uint32_t now);

/* Deliberate bug used only for the mutation demonstration: evicts slot 0 whether or not it is still
 * live, so a request consumed a moment ago can be replayed inside its own validity window. */
int qseal_nonce_exp_accept_evictlive(qseal_nonce_exp_store_t *s, int ok,
                                     const uint8_t k[QSEAL_EXP_KEY_LEN],
                                     uint32_t req_exp, uint32_t now);

#endif
