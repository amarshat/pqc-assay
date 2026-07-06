/* Q-SEAL request validation reference (section 16 property 7: a malformed request fails before
 * signing). qseal_validate_request is the well-formedness gate; qseal_create_assertion_checked signs
 * only after it passes. Verified against QSEAL_Validate.cry by qseal/proof/validate.saw. */
#ifndef QSEAL_VALIDATE_H
#define QSEAL_VALIDATE_H

#include "assertion.h"   /* qseal_request_t, qseal_applet_id_t, qseal_create_assertion, QSEAL_TBS_LEN */

/* Returns 1 iff the request is well-formed per the spec enumerations: version 0x01, suite 0x0001
 * (HYB-1), assertion_type 0x01..0x06, assertion_origin 0x01..0x03, object_hash_algorithm 0x01. */
int qseal_validate_request(const qseal_request_t *r, const qseal_applet_id_t *a);

/* Validate, then sign: on a valid request, builds TBS-V1 into out and returns 1; on a malformed
 * request, zeroes out and returns 0 (the applet does not sign). */
int qseal_create_assertion_checked(const qseal_request_t *r, const qseal_applet_id_t *a,
                                   uint8_t out[QSEAL_TBS_LEN]);

/* Deliberate bug used only for the mutation demonstration: validates without the suite check, so it
 * signs a request under an unsupported suite. */
int qseal_create_assertion_checked_nosuitecheck(const qseal_request_t *r, const qseal_applet_id_t *a,
                                   uint8_t out[QSEAL_TBS_LEN]);

#endif
