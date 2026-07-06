/* Q-SEAL single-use challenge store reference. See nonce.h. Verified equal to QSEAL_Nonce.cry
 * (acceptBit / nextStore) by qseal/proof/nonce.saw. Written as fixed unrolled scans with constant
 * indices (no slicing, whole-array rebuild) so it maps directly onto the Cryptol model and onto SAW.
 * The key k is verifier_id || request_id (see nonce.h), so the store is per-verifier. */
#include "nonce.h"

int qseal_nonce_seen(const qseal_nonce_store_t *s, const uint8_t k[QSEAL_KEY_LEN]) {
    int found = 0;
    for (uint8_t i = 0; i < QSEAL_STORE_CAP; i++) {
        int eq = 1;
        for (uint32_t j = 0; j < QSEAL_KEY_LEN; j++)
            if (s->slots[i][j] != k[j]) eq = 0;
        if (i < s->count && eq) found = 1;
    }
    return found;
}

int qseal_nonce_accept(qseal_nonce_store_t *s, int ok, const uint8_t k[QSEAL_KEY_LEN]) {
    int is_seen = qseal_nonce_seen(s, k);
    int is_full = (s->count >= QSEAL_STORE_CAP);
    int a = (ok != 0) && !is_seen && !is_full;
    if (a) {
        /* append k at index count (constant-index guarded scan, matching the model's rebuild) */
        for (uint8_t i = 0; i < QSEAL_STORE_CAP; i++)
            if (i == s->count)
                for (uint32_t j = 0; j < QSEAL_KEY_LEN; j++)
                    s->slots[i][j] = k[j];
        s->count = (uint8_t)(s->count + 1);
    }
    return a ? 1 : 0;
}

int qseal_nonce_accept_noconsume(qseal_nonce_store_t *s, int ok, const uint8_t k[QSEAL_KEY_LEN]) {
    int is_seen = qseal_nonce_seen(s, k);
    int is_full = (s->count >= QSEAL_STORE_CAP);
    int a = (ok != 0) && !is_seen && !is_full;
    /* BUG: never records k, so the same validated request is accepted again (replay). */
    return a ? 1 : 0;
}
