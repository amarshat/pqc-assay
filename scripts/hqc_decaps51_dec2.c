/* Self-composition harness for the v5.1.0 leak check: two decapsulations of the same ciphertext
 * under the same key and the same fault, with the hash_g override switched to an independent
 * function between them by hqc_epoch. Not part of HQC. */
#include <stdint.h>
int8_t hqc_kem_decaps(uint8_t *K_prime, const uint8_t *dk_kem, const uint8_t *c_kem);
uint8_t hqc_epoch;
int dec2(uint8_t *k1, uint8_t *k2, const uint8_t *dk, const uint8_t *c) {
    hqc_epoch = 0;
    hqc_kem_decaps(k1, dk, c);
    hqc_epoch = 1;
    hqc_kem_decaps(k2, dk, c);
    return 0;
}
