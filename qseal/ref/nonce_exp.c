/* Q-SEAL single-use challenge store with expiry eviction. See nonce_exp.h. Verified equal to
 * QSEAL_NonceExp.cry (accept / step) by qseal/proof/nonce_exp.saw. Written as fixed unrolled scans
 * with constant indices, matching the model's liveSlots / seenLive / firstFree. */
#include "nonce_exp.h"

int qseal_nonce_exp_accept(qseal_nonce_exp_store_t *s, int ok, const uint8_t k[QSEAL_EXP_KEY_LEN],
                           uint32_t req_exp, uint32_t now) {
    int seen_live = 0;
    int has_room = 0;
    uint8_t first_free = QSEAL_EXP_CAP;

    for (unsigned i = 0; i < QSEAL_EXP_CAP; i++) {
        int live = (s->exps[i] > now);
        int eq = 1;
        for (unsigned j = 0; j < QSEAL_EXP_KEY_LEN; j++)
            if (s->keys[i][j] != k[j]) eq = 0;
        if (eq && live) seen_live = 1;
        if (!live) {
            has_room = 1;
            if (first_free == QSEAL_EXP_CAP) first_free = (uint8_t)i;
        }
    }

    int a = (ok != 0) && (now < req_exp) && !seen_live && has_room;
    if (a) {
        for (unsigned i = 0; i < QSEAL_EXP_CAP; i++)
            if (i == first_free) {
                for (unsigned j = 0; j < QSEAL_EXP_KEY_LEN; j++)
                    s->keys[i][j] = k[j];
                s->exps[i] = req_exp;
            }
    }
    return a ? 1 : 0;
}

int qseal_nonce_exp_accept_evictlive(qseal_nonce_exp_store_t *s, int ok,
                                     const uint8_t k[QSEAL_EXP_KEY_LEN],
                                     uint32_t req_exp, uint32_t now) {
    int seen_live = 0;
    for (unsigned i = 0; i < QSEAL_EXP_CAP; i++) {
        int live = (s->exps[i] > now);
        int eq = 1;
        for (unsigned j = 0; j < QSEAL_EXP_KEY_LEN; j++)
            if (s->keys[i][j] != k[j]) eq = 0;
        if (eq && live) seen_live = 1;
    }
    /* BUG: always evicts slot 0, live or not, so the store never runs out and a live entry can be
     * thrown away. A request consumed a moment ago is then accepted again inside its own window. */
    int a = (ok != 0) && (now < req_exp) && !seen_live;
    if (a) {
        for (unsigned j = 0; j < QSEAL_EXP_KEY_LEN; j++)
            s->keys[0][j] = k[j];
        s->exps[0] = req_exp;
    }
    return a ? 1 : 0;
}
