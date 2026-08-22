/* GSMA SGP.29 v1.1 EID validation reference. Verified equal to esim-eid/model/EID.cry `eidValid` by
 * esim-eid/proof/eid.saw. Fixed unrolled scan, constant indices. */
#include "eid.h"

int gsma_eid_valid(const uint8_t d[GSMA_EID_DIGITS]) {
    int ok = 1;
    for (unsigned i = 0; i < GSMA_EID_DIGITS; i++)
        if (d[i] > 9) ok = 0;                       /* decimal digits only */
    if (d[0] == 8 && d[1] == 9) ok = 0;             /* AE.R02: 89 is reserved for ITU-T E.118 */
    uint32_t acc = 0;
    for (unsigned i = 0; i < GSMA_EID_DIGITS; i++)
        acc = (acc * 10u + d[i]) % 97u;             /* section 10, folded: acc stays below 97 */
    if (acc != 1u) ok = 0;
    return ok;
}

int gsma_eid_valid_noe118(const uint8_t d[GSMA_EID_DIGITS]) {
    int ok = 1;
    for (unsigned i = 0; i < GSMA_EID_DIGITS; i++)
        if (d[i] > 9) ok = 0;
    /* BUG: AE.R02 dropped, so an EID in the range reserved for the ITU-T E.118 scheme is accepted. Its
     * check digits are unaffected, so only a clause-directed vector or this spec catches it. */
    uint32_t acc = 0;
    for (unsigned i = 0; i < GSMA_EID_DIGITS; i++)
        acc = (acc * 10u + d[i]) % 97u;
    if (acc != 1u) ok = 0;
    return ok;
}

int gsma_eid_valid_latereduce(const uint8_t d[GSMA_EID_DIGITS]) {
    int ok = 1;
    for (unsigned i = 0; i < GSMA_EID_DIGITS; i++)
        if (d[i] > 9) ok = 0;
    if (d[0] == 8 && d[1] == 9) ok = 0;
    /* BUG: follows the standard's wording literally in a 32-bit word. "Using the 32 digits as a decimal
     * integer" needs about 107 bits, so this wraps long before the last digit. */
    uint32_t acc = 0;
    for (unsigned i = 0; i < GSMA_EID_DIGITS; i++)
        acc = acc * 10u + d[i];
    if (acc % 97u != 1u) ok = 0;
    return ok;
}

int gsma_eid_valid_nodigits(const uint8_t d[GSMA_EID_DIGITS]) {
    int ok = 1;
    /* BUG: no digit-range check, so a byte above 9 still contributes to the remainder. */
    if (d[0] == 8 && d[1] == 9) ok = 0;
    uint32_t acc = 0;
    for (unsigned i = 0; i < GSMA_EID_DIGITS; i++)
        acc = (acc * 10u + d[i]) % 97u;
    if (acc != 1u) ok = 0;
    return ok;
}
