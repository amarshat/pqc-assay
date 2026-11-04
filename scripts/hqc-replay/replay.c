/* Native replay of call-skip faults in HQC v5.1.0 hqc-1 decapsulation (paper 2, Section 6). Linked
 * against one faulted hqc-kem.c (scripts/hqc-replay/skip.py) or the unfaulted one, with the real
 * SHA-3, XOF, PKE and decoder. For two key pairs and four ciphertexts it prints the decapsulation
 * output and J(H(ek), 0^k, c), which anyone who knows ek and c can compute. Not part of HQC. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include "hqc-kem.h"
#include "parameters.h"
#include "parsing.h"
#include "symmetric.h"

static uint64_t rs;
int randombytes(uint8_t *out, size_t outlen) {
    for (size_t i = 0; i < outlen; i++) {
        rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
        out[i] = (uint8_t)rs;
    }
    return 0;
}

static void hex(const char *label, const uint8_t *k) {
    printf("%s ", label);
    for (int i = 0; i < CRYPTO_BYTES; i++) printf("%02x", k[i]);
    printf("\n");
}

static void public_j(uint8_t *out, const uint8_t *ek, const uint8_t *c) {
    uint8_t hek[SEED_BYTES], sigma0[PARAM_K] = {0}, salt[SALT_BYTES];
    uint64_t u[VEC_N_PKE_WORDS] = {0}, v[VEC_N1N2_PKE_WORDS] = {0};
    hash_h(hek, ek);
    hqc_c_kem_from_string(u, v, salt, c);
    hash_j(out, hek, sigma0, u, v, salt);
}

int main(void) {
    static uint8_t ek[2][CRYPTO_PUBLICKEYBYTES], dk[2][CRYPTO_SECRETKEYBYTES];
    static uint8_t cv[2][CRYPTO_CIPHERTEXTBYTES], cs[4][CRYPTO_CIPHERTEXTBYTES];
    uint8_t K[2][CRYPTO_BYTES], out[CRYPTO_BYTES], pj[CRYPTO_BYTES];
    const char *cname[4] = {"flip", "zero", "rand", "flip2"};
    for (int p = 0; p < 2; p++) {
        rs = 0x9e3779b97f4a7c15ULL + 0x1000 * (uint64_t)p;
        hqc_kem_keygen(ek[p], dk[p]);
        hqc_kem_encaps(K[p], cv[p], ek[p]);
    }
    memcpy(cs[0], cv[0], CRYPTO_CIPHERTEXTBYTES); cs[0][100] ^= 1;        /* invalid for key 0 */
    memset(cs[1], 0, CRYPTO_CIPHERTEXTBYTES);                              /* all zero */
    rs = 0x243f6a8885a308d3ULL; randombytes(cs[2], CRYPTO_CIPHERTEXTBYTES); /* random */
    memcpy(cs[3], cv[1], CRYPTO_CIPHERTEXTBYTES); cs[3][100] ^= 1;        /* invalid for key 1 */
    for (int p = 0; p < 2; p++) {
        char l[32];
        hqc_kem_decaps(out, dk[p], cv[p]);
        snprintf(l, sizeof l, "key%d valid  out", p); hex(l, out);
        snprintf(l, sizeof l, "key%d valid  K  ", p); hex(l, K[p]);
        for (int j = 0; j < 4; j++) {
            hqc_kem_decaps(out, dk[p], cs[j]);
            public_j(pj, ek[p], cs[j]);
            snprintf(l, sizeof l, "key%d %-5s out", p, cname[j]); hex(l, out);
            snprintf(l, sizeof l, "key%d %-5s pubJ", p, cname[j]); hex(l, pj);
        }
    }
    return 0;
}
