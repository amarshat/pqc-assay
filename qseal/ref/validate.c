/* Q-SEAL request validation reference. See validate.h. Verified equal to QSEAL_Validate.cry
 * (valid / create_checked) by qseal/proof/validate.saw. */
#include "validate.h"

int qseal_validate_request(const qseal_request_t *r, const qseal_applet_id_t *a) {
    int ok = 1;
    if (a->version[0] != 0x01) ok = 0;                                   /* version = TBS-V1 */
    if (!(r->suite_id[0] == 0x00 && r->suite_id[1] == 0x01)) ok = 0;     /* suite = HYB-1 (0x0001) */
    if (!(r->assertion_type[0] >= 0x01 && r->assertion_type[0] <= 0x06)) ok = 0;   /* section 8 */
    if (r->assertion_type[0] == 0x04) ok = 0;    /* PROFILE_ACTION_OBSERVED not host-callable (8.4) */
    if (!(r->assertion_origin[0] >= 0x01 && r->assertion_origin[0] <= 0x03)) ok = 0;/* section 9 */
    if (r->object_hash_algorithm[0] != 0x01) ok = 0;                     /* SHA-256 */
    return ok;
}

int qseal_create_assertion_checked(const qseal_request_t *r, const qseal_applet_id_t *a,
                                   uint8_t out[QSEAL_TBS_LEN]) {
    if (!qseal_validate_request(r, a)) {
        for (int i = 0; i < QSEAL_TBS_LEN; i++) out[i] = 0;   /* malformed: do not sign */
        return 0;
    }
    qseal_create_assertion(r, a, out);
    return 1;
}

int qseal_create_assertion_checked_nosuitecheck(const qseal_request_t *r, const qseal_applet_id_t *a,
                                   uint8_t out[QSEAL_TBS_LEN]) {
    /* BUG: the suite check is missing, so a request under an unsupported suite is signed. */
    int ok = 1;
    if (a->version[0] != 0x01) ok = 0;
    if (!(r->assertion_type[0] >= 0x01 && r->assertion_type[0] <= 0x06)) ok = 0;
    if (!(r->assertion_origin[0] >= 0x01 && r->assertion_origin[0] <= 0x03)) ok = 0;
    if (r->object_hash_algorithm[0] != 0x01) ok = 0;
    if (!ok) {
        for (int i = 0; i < QSEAL_TBS_LEN; i++) out[i] = 0;
        return 0;
    }
    qseal_create_assertion(r, a, out);
    return 1;
}

int qseal_create_assertion_checked_allowobserved(const qseal_request_t *r, const qseal_applet_id_t *a,
                                   uint8_t out[QSEAL_TBS_LEN]) {
    /* BUG: keeps the suite check but drops the observed-type rejection, so a host request for
     * PROFILE_ACTION_OBSERVED (0x04) is signed (spec 8.4 forbids this; property 5). */
    int ok = 1;
    if (a->version[0] != 0x01) ok = 0;
    if (!(r->suite_id[0] == 0x00 && r->suite_id[1] == 0x01)) ok = 0;
    if (!(r->assertion_type[0] >= 0x01 && r->assertion_type[0] <= 0x06)) ok = 0;
    if (!(r->assertion_origin[0] >= 0x01 && r->assertion_origin[0] <= 0x03)) ok = 0;
    if (r->object_hash_algorithm[0] != 0x01) ok = 0;
    if (!ok) {
        for (int i = 0; i < QSEAL_TBS_LEN; i++) out[i] = 0;
        return 0;
    }
    qseal_create_assertion(r, a, out);
    return 1;
}

/* MUTANT paired to validate_spec (not to checked_spec, which the other two mutants target): the origin
 * range check is widened by one, so an out-of-enumeration origin passes the gate. */
int qseal_validate_request_wideorigin(const qseal_request_t *r, const qseal_applet_id_t *a) {
    int ok = 1;
    if (a->version[0] != 0x01) ok = 0;
    if (!(r->suite_id[0] == 0x00 && r->suite_id[1] == 0x01)) ok = 0;
    if (!(r->assertion_type[0] >= 0x01 && r->assertion_type[0] <= 0x06)) ok = 0;
    if (r->assertion_type[0] == 0x04) ok = 0;
    if (!(r->assertion_origin[0] >= 0x01 && r->assertion_origin[0] <= 0x04)) ok = 0;  /* BUG: <= 0x03 */
    if (r->object_hash_algorithm[0] != 0x01) ok = 0;
    return ok;
}
