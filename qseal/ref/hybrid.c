/* Q-SEAL HYB-1 hybrid verifier reference. See hybrid.h. Verified against QSEAL_Verify.cry by
 * qseal/proof/hybrid.saw (signature verifiers uninterpreted). */
#include "hybrid.h"

/* Placeholder verifier bodies so the bitcode links; the SAW proof overrides these with uninterpreted
 * specs, so these values are never used. Real deployments link ECDSA P-256 / ML-DSA-44 here. */
int qseal_verify_ecdsa(const uint8_t *pk, const uint8_t tbs[QSEAL_TBS_LEN], const uint8_t *sig) {
    (void)pk; (void)tbs; (void)sig; return 0;
}
int qseal_verify_mldsa(const uint8_t *pk, const uint8_t tbs[QSEAL_TBS_LEN], const uint8_t *sig) {
    (void)pk; (void)tbs; (void)sig; return 0;
}

int qseal_hybrid_accept(const uint8_t tbs[QSEAL_TBS_LEN],
                        const uint8_t *pk_c,  const uint8_t *sig_c,
                        const uint8_t *pk_pq, const uint8_t *sig_pq) {
    int ok_c  = qseal_verify_ecdsa(pk_c,  tbs, sig_c);
    int ok_pq = qseal_verify_mldsa(pk_pq, tbs, sig_pq);
    return ok_c && ok_pq;   /* HYB-1: BOTH signatures, over the SAME transcript */
}

int qseal_hybrid_accept_downgrade(const uint8_t tbs[QSEAL_TBS_LEN],
                        const uint8_t *pk_c,  const uint8_t *sig_c,
                        const uint8_t *pk_pq, const uint8_t *sig_pq) {
    int ok_c  = qseal_verify_ecdsa(pk_c,  tbs, sig_c);
    int ok_pq = qseal_verify_mldsa(pk_pq, tbs, sig_pq);
    return ok_c || ok_pq;   /* BUG: accepts on either signature alone (silent downgrade) */
}
