/* Q-SEAL evidence-fragment reassembly reference (section 16 property 6: reassembly produces exactly
 * the original evidence bytes or fails closed). READ_EVIDENCE returns the evidence blob as response
 * fragments; the host reassembles them. Verified against QSEAL_Evidence.cry by qseal/proof/evidence.saw.
 * Sizes are fixed and small so the proof stays bounded; the reassembly logic is independent of them. */
#ifndef QSEAL_EVIDENCE_H
#define QSEAL_EVIDENCE_H

#include <stdint.h>

/* Overridable at compile time so the same reference can be proved at more than one fragment arity:
 * the readable 4x32 instance and a deployed-scale one (see qseal/proof/gen_evidence_instance.py). */
#ifndef QSEAL_FRAG_SIZE
#define QSEAL_FRAG_SIZE 32
#endif
#ifndef QSEAL_NUM_FRAGS
#define QSEAL_NUM_FRAGS 4
#endif
#define QSEAL_EVID_LEN  (QSEAL_FRAG_SIZE * QSEAL_NUM_FRAGS)   /* 128 */

/* One response fragment: its index, the total fragment count, and its payload. Field order and types
 * match the Cryptol Frag record. */
typedef struct qseal_frag_t {
    uint8_t seq;
    uint8_t total;
    uint8_t data[QSEAL_FRAG_SIZE];
} qseal_frag_t;

/* Reassemble the evidence blob. Returns 1 and fills out iff the fragment set is well formed (every
 * fragment reports total == NF and the indices are a permutation of 0..NF-1); otherwise zeroes out and
 * returns 0 (fail closed, no partial output). */
int qseal_evidence_reassemble(const qseal_frag_t frags[QSEAL_NUM_FRAGS], uint8_t out[QSEAL_EVID_LEN]);

/* Deliberate bug used only for the mutation demonstration: drops the completeness (permutation) check,
 * so an incomplete transfer is accepted and any missing index is zero-filled (corruption). */
int qseal_evidence_reassemble_nocomplete(const qseal_frag_t frags[QSEAL_NUM_FRAGS], uint8_t out[QSEAL_EVID_LEN]);

#endif
