/* Q-SEAL evidence-fragment reassembly reference. See evidence.h. Verified equal to QSEAL_Evidence.cry
 * (reassemble) by qseal/proof/evidence.saw. Fixed unrolled scans, constant indices; the placement scan
 * mirrors the model's `place` (for each output index, copy the payload of the fragment carrying it). */
#include "evidence.h"

int qseal_evidence_reassemble(const qseal_frag_t frags[QSEAL_NUM_FRAGS], uint8_t out[QSEAL_EVID_LEN]) {
    int ok = 1;
    for (int i = 0; i < QSEAL_NUM_FRAGS; i++)
        if (frags[i].total != QSEAL_NUM_FRAGS) ok = 0;         /* every fragment agrees on the total */
    for (uint8_t j = 0; j < QSEAL_NUM_FRAGS; j++) {
        int c = 0;
        for (int i = 0; i < QSEAL_NUM_FRAGS; i++)
            if (frags[i].seq == j) c++;
        if (c != 1) ok = 0;                                    /* index j present exactly once */
    }
    if (!ok) {
        for (int i = 0; i < QSEAL_EVID_LEN; i++) out[i] = 0;   /* fail closed */
        return 0;
    }
    for (uint8_t j = 0; j < QSEAL_NUM_FRAGS; j++)
        for (int i = 0; i < QSEAL_NUM_FRAGS; i++)
            if (frags[i].seq == j)
                for (int k = 0; k < QSEAL_FRAG_SIZE; k++)
                    out[j * QSEAL_FRAG_SIZE + k] = frags[i].data[k];
    return 1;
}

int qseal_evidence_reassemble_nocomplete(const qseal_frag_t frags[QSEAL_NUM_FRAGS], uint8_t out[QSEAL_EVID_LEN]) {
    /* BUG: the permutation/completeness check is missing, so a missing index is silently zero-filled. */
    int ok = 1;
    for (int i = 0; i < QSEAL_NUM_FRAGS; i++)
        if (frags[i].total != QSEAL_NUM_FRAGS) ok = 0;
    for (int i = 0; i < QSEAL_EVID_LEN; i++) out[i] = 0;
    if (ok)
        for (uint8_t j = 0; j < QSEAL_NUM_FRAGS; j++)
            for (int i = 0; i < QSEAL_NUM_FRAGS; i++)
                if (frags[i].seq == j)
                    for (int k = 0; k < QSEAL_FRAG_SIZE; k++)
                        out[j * QSEAL_FRAG_SIZE + k] = frags[i].data[k];
    return ok;
}
