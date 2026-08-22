/* GSMA SGP.29 v1.1 EID validation reference. See esim-eid/model/EID.cry for the clause-by-clause
 * transcription and the section numbers. Digits are one per byte with value 0..9, not ASCII. */
#ifndef GSMA_EID_H
#define GSMA_EID_H

#include <stdint.h>

#define GSMA_EID_DIGITS 32   /* SGP.29 EID.R01: "The length of the EID SHALL be 32 digits." */

/* Returns 1 iff every byte is a decimal digit, the EID does not start with 89 (AE.R02, reserved for
 * the ITU-T E.118 scheme), and the check digits verify (section 10: the 32 digits as a decimal integer
 * leave remainder 1 on division by 97). The remainder is folded digit by digit because 32 decimal
 * digits need about 107 bits and do not fit in a machine word. */
int gsma_eid_valid(const uint8_t d[GSMA_EID_DIGITS]);

/* Deliberate mutants for the non-vacuity checks in esim-eid/proof/eid.saw. Nothing calls them. */
int gsma_eid_valid_noe118(const uint8_t d[GSMA_EID_DIGITS]);      /* drops AE.R02 */
int gsma_eid_valid_latereduce(const uint8_t d[GSMA_EID_DIGITS]);  /* one remainder at the end */
int gsma_eid_valid_nodigits(const uint8_t d[GSMA_EID_DIGITS]);    /* drops the digit-range check */

#endif
