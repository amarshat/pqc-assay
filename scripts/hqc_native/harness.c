// Differential test: repaired AVX2 vect_mul against reference vect_mul (HQC v5.0.0), native x86-64.
#include <immintrin.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "parameters.h"   /* the AVX2 parameter set */
void ref_vect_mul(uint64_t *o, const uint64_t *v1, const uint64_t *v2);
void vect_mul(__m256i *o, const __m256i *v1, const __m256i *v2);
static uint64_t s = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void) { s ^= s << 13; s ^= s >> 7; s ^= s << 17; return s; }
static void fill(uint64_t *v, int kind) {
  memset(v, 0, VEC_N_SIZE_64 * 8);
  for (int i = 0; i < VEC_N_SIZE_64; i++) v[i] = kind == 0 ? rnd() : kind == 1 ? ~0ull : 0;
  if (kind == 2) v[0] = 1;
  if (kind == 3) v[(PARAM_N - 1) / 64] = 1ull << ((PARAM_N - 1) % 64);
  v[VEC_N_SIZE_64 - 1] &= (PARAM_N % 64) ? ((1ull << (PARAM_N % 64)) - 1) : ~0ull;
}
int main(int argc, char **argv) {
  int iters = argc > 1 ? atoi(argv[1]) : 1000, bad = 0;
  uint64_t *a = calloc(VEC_N_SIZE_64, 8), *b = calloc(VEC_N_SIZE_64, 8), *r = calloc(VEC_N_SIZE_64, 8);
  __m256i *A = aligned_alloc(32, VEC_N_256_SIZE_64 * 8 + 64), *B = aligned_alloc(32, VEC_N_256_SIZE_64 * 8 + 64);
  size_t outw = VEC_N_256_SIZE_64 + 8; __m256i *O = aligned_alloc(32, outw * 8);
  for (int t = 0; t < iters + 16; t++) {
    int ka = t < 16 ? t % 4 : 0, kb = t < 16 ? t / 4 : 0;
    fill(a, ka); fill(b, kb);
    memset(A, 0, VEC_N_256_SIZE_64 * 8 + 64); memset(B, 0, VEC_N_256_SIZE_64 * 8 + 64);
    memcpy(A, a, VEC_N_SIZE_64 * 8); memcpy(B, b, VEC_N_SIZE_64 * 8);
    memset(O, 0xA5, outw * 8);
    ref_vect_mul(r, a, b);
    vect_mul(O, A, B);
    const uint8_t *ob = (const uint8_t *)O, *rb = (const uint8_t *)r;
    if (memcmp(ob, rb, VEC_N_SIZE_BYTES)) { bad++; if (bad < 4) printf("MISMATCH at test %d\n", t); }
    for (size_t i = VEC_N_SIZE_BYTES; i < outw * 8; i++) if (ob[i] != 0xA5) { bad++; printf("WROTE past VEC_N_SIZE_BYTES at byte %zu, test %d\n", i, t); break; }
    for (size_t i = VEC_N_SIZE_BYTES; i < (size_t)VEC_N_SIZE_64 * 8; i++) if (rb[i]) { bad++; printf("ref nonzero above n at byte %zu\n", i); break; }
    if (ob[VEC_N_SIZE_BYTES - 1] >> (PARAM_N % 8 ? PARAM_N % 8 : 8)) { bad++; printf("high bits of last AVX2 byte nonzero, test %d\n", t); }
  }
  printf("n=%d tests=%d mismatches=%d\n", PARAM_N, iters + 16, bad);
  return bad != 0;
}
