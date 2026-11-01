/* Self-composition harness for the leak check (scripts/hqc_decaps_faults_run.sh, NI mode): two
 * decapsulations of the same ciphertext under the same secret key and the same fault, with the
 * hash_g override switched to an independent function between them by hqc_epoch. Not part of HQC. */
#include <stdint.h>
int crypto_kem_dec(uint8_t *K_prime, const uint8_t *c_kem, const uint8_t *dk_kem);
uint8_t hqc_epoch;
int dec2(uint8_t *k1, uint8_t *k2, const uint8_t *c, const uint8_t *sk) {
    hqc_epoch = 0;
    crypto_kem_dec(k1, c, sk);
    hqc_epoch = 1;
    crypto_kem_dec(k2, c, sk);
    return 0;
}
