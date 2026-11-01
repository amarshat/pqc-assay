/* Timing of HQC v5.1.0 hqc-1 decapsulation, shipped or hardened (paper 2, Section 6). Median and
 * mean wall-clock nanoseconds of N calls, for a valid ciphertext and for one with a flipped bit.
 * Also prints a hash of the outputs so that two builds can be compared. Not part of HQC. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "hqc-kem.h"

int randombytes(uint8_t *out, size_t outlen) {
    /* deterministic, so that both builds see the same keys and ciphertexts */
    static uint64_t s = 0x9e3779b97f4a7c15ULL;
    for (size_t i = 0; i < outlen; i++) {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        out[i] = (uint8_t)s;
    }
    return 0;
}

static int cmp(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return (x > y) - (x < y);
}

static void run(const char *label, const uint8_t *dk, const uint8_t *c, int n, uint64_t *t) {
    uint8_t k[CRYPTO_BYTES];
    uint64_t sum = 0, fold = 0;
    for (int i = 0; i < 50; i++) hqc_kem_decaps(k, dk, c);
    for (int i = 0; i < n; i++) {
        uint64_t a = clock_gettime_nsec_np(CLOCK_UPTIME_RAW);
        hqc_kem_decaps(k, dk, c);
        t[i] = clock_gettime_nsec_np(CLOCK_UPTIME_RAW) - a;
        sum += t[i];
    }
    for (int j = 0; j < CRYPTO_BYTES; j++) fold = fold * 131 + k[j];
    qsort(t, n, sizeof t[0], cmp);
    printf("%-8s median %8llu ns  mean %8llu ns  key %016llx\n", label, (unsigned long long)t[n / 2],
           (unsigned long long)(sum / n), (unsigned long long)fold);
}

int main(int argc, char **argv) {
    int n = argc > 1 ? atoi(argv[1]) : 2000;
    uint8_t ek[CRYPTO_PUBLICKEYBYTES], dk[CRYPTO_SECRETKEYBYTES], c[CRYPTO_CIPHERTEXTBYTES], K[CRYPTO_BYTES];
    uint64_t *t = malloc(sizeof(uint64_t) * n);
    hqc_kem_keygen(ek, dk);
    hqc_kem_encaps(K, c, ek);
    run("valid", dk, c, n, t);
    c[100] ^= 1;
    run("invalid", dk, c, n, t);
    free(t);
    return 0;
}
