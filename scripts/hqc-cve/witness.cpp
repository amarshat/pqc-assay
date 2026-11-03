// CVE-2024-54137 witness on an archived HQC reference implementation (hqc-128): decapsulate a
// ciphertext with one bit of v flipped and report whether the output is the accept key
// SHAKE256-512(m' || u || v) or the reject key SHAKE256-512(sigma || u || v), each computed here from
// the implementation's own decryption and hash. Built by scripts/hqc_cve_witness.sh. Not part of HQC.
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include "api.h"
#include "parameters.h"
#include "hqc.h"
#include "parsing.h"
#include "shake_ds.h"
#include "shake_prng.h"

static int eq(const uint8_t *a, const uint8_t *b, size_t n) { return memcmp(a, b, n) == 0; }

int main(void) {
    uint8_t entropy[48];
    for (int i = 0; i < 48; i++) entropy[i] = (uint8_t)i;
    shake_prng_init(entropy, NULL, 48, 0);
    static uint8_t pk[CRYPTO_PUBLICKEYBYTES], sk[CRYPTO_SECRETKEYBYTES], ct[CRYPTO_CIPHERTEXTBYTES];
    uint8_t k_enc[CRYPTO_BYTES], k_dec[CRYPTO_BYTES], k_mod[CRYPTO_BYTES];
    crypto_kem_keypair(pk, sk);
    crypto_kem_enc(ct, k_enc, pk);
    int r_honest = crypto_kem_dec(k_dec, ct, sk);
    ct[VEC_N_SIZE_BYTES + 5] ^= 0x01;                 // one bit of v
    int r_mod = crypto_kem_dec(k_mod, ct, sk);

    // accept and reject keys for the modified ciphertext, from the implementation's primitives
    uint64_t u[VEC_N_SIZE_64] = {0}, v[VEC_N1N2_SIZE_64] = {0}, salt[SALT_SIZE_64] = {0};
    uint8_t m[VEC_K_SIZE_BYTES] = {0}, sigma[VEC_K_SIZE_BYTES] = {0};
    hqc_ciphertext_from_string(u, v, salt, ct);
    hqc_pke_decrypt((uint64_t *)m, sigma, u, v, sk);
    static uint8_t mc[VEC_K_SIZE_BYTES + VEC_N_SIZE_BYTES + VEC_N1N2_SIZE_BYTES];
    uint8_t k_acc[CRYPTO_BYTES], k_rej[CRYPTO_BYTES];
    shake256incctx st;
    memcpy(mc + VEC_K_SIZE_BYTES, u, VEC_N_SIZE_BYTES);
    memcpy(mc + VEC_K_SIZE_BYTES + VEC_N_SIZE_BYTES, v, VEC_N1N2_SIZE_BYTES);
    memcpy(mc, m, VEC_K_SIZE_BYTES);
    shake256_512_ds(&st, k_acc, mc, sizeof mc, K_FCT_DOMAIN);
    memcpy(mc, sigma, VEC_K_SIZE_BYTES);
    shake256_512_ds(&st, k_rej, mc, sizeof mc, K_FCT_DOMAIN);

    printf("honest ciphertext: decaps == encaps key: %s (return %d)\n",
           eq(k_dec, k_enc, CRYPTO_BYTES) ? "yes" : "no", r_honest);
    printf("one bit of v flipped: output == accept key SHAKE(m'||u||v): %s; == reject key SHAKE(sigma||u||v): %s (return %d)\n",
           eq(k_mod, k_acc, CRYPTO_BYTES) ? "yes" : "no", eq(k_mod, k_rej, CRYPTO_BYTES) ? "yes" : "no", r_mod);
    return 0;
}
