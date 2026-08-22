/* Q-SEAL HYB-1 hybrid verifier reference. accept iff BOTH the ECDSA and ML-DSA signatures verify over
 * the SAME transcript. Verified against QSEAL_Verify.cry by qseal/proof/hybrid.saw, with the underlying
 * signature verifiers kept uninterpreted (the proof is about the acceptance structure). */
#ifndef QSEAL_HYBRID_H
#define QSEAL_HYBRID_H

#include "tbs_v1.h"

/* Opaque signature verifiers (return nonzero iff the signature is valid). Real implementations are
 * ECDSA P-256 / ML-DSA-44; abstracted in the proof. */
int qseal_verify_ecdsa(const uint8_t *pk, const uint8_t tbs[QSEAL_TBS_LEN], const uint8_t *sig);
int qseal_verify_mldsa(const uint8_t *pk, const uint8_t tbs[QSEAL_TBS_LEN], const uint8_t *sig);

/* HYB-1 acceptance: BOTH signatures, over the same transcript. Returns 1 to accept, 0 to reject. */
int qseal_hybrid_accept(const uint8_t tbs[QSEAL_TBS_LEN],
                        const uint8_t *pk_c,  const uint8_t *sig_c,
                        const uint8_t *pk_pq, const uint8_t *sig_pq);

/* Deliberate downgrade bug used only for the mutation demonstration: accepts on EITHER signature. */
int qseal_hybrid_accept_downgrade(const uint8_t tbs[QSEAL_TBS_LEN],
                        const uint8_t *pk_c,  const uint8_t *sig_c,
                        const uint8_t *pk_pq, const uint8_t *sig_pq);

/* Deliberate mutant: a conjunction like the reference, but the two verifiers see different transcripts. */
int qseal_hybrid_accept_othertbs(const uint8_t tbs[QSEAL_TBS_LEN],
                        const uint8_t *pk_c,  const uint8_t *sig_c,
                        const uint8_t *pk_pq, const uint8_t *sig_pq);

#endif
