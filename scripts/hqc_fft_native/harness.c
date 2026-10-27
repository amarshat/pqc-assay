// Native differential test of the additive-FFT reference C (not a proof): the entry points the SAW
// proofs cover, against a schoolbook carry-less product written here, at the three HQC lengths.
// HQC_P selects the length: 1 -> polymul_280U64_input/_mul, 3 -> polymul_576U64_input/_mul,
// 5 -> polymul_input_transform/polymul_output at 1024 words. Buffers have the sizes of the SAW specs,
// so AddressSanitizer reports any access outside them. Inputs: random operands of degree below n and of
// full width, plus every pair from {0, 1, x^(n-1), x^(64W-1), all ones below n, all ones}.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "polymul.h"
#include "polymul_hqclen.h"

#if HQC_P == 1
#define W 280
#define NBITS 17669
#define FW 512
#define CW 560
#elif HQC_P == 3
#define W 576
#define NBITS 35851
#define FW 1024
#define CW 1152
#else
#define W 1024
#define NBITS 57637
#define FW 2048
#define CW 2048
#endif

static uint64_t rng = 0x9e3779b97f4a7c15ULL;
static uint64_t next(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void school(uint64_t *c, const uint64_t *a, const uint64_t *b) {
  memset(c, 0, 2 * W * sizeof *c);
  for (int i = 0; i < W; i++) {
    if (!a[i]) continue;
    for (int j = 0; j < W; j++) {
      uint64_t x = a[i], y = b[j], lo = 0, hi = 0;
      for (int k = 0; k < 64; k++)
        if ((y >> k) & 1) { lo ^= x << k; if (k) hi ^= x >> (64 - k); }
      c[i + j] ^= lo; c[i + j + 1] ^= hi;
    }
  }
}

static void fft(uint64_t *c, const uint64_t *a, const uint64_t *b) {
  uint64_t *af = malloc(FW * 8), *bf = malloc(FW * 8), *cc = malloc(CW * 8);
#if HQC_P == 1
  polymul_280U64_input(af, a); polymul_280U64_input(bf, b); polymul_280U64_mul(cc, a, b, af, bf);
#elif HQC_P == 3
  polymul_576U64_input(af, a); polymul_576U64_input(bf, b); polymul_576U64_mul(cc, a, b, af, bf);
#else
  polymul_input_transform(af, a, W); polymul_input_transform(bf, b, W); polymul_output(cc, af, bf, W);
#endif
  memcpy(c, cc, CW * 8);
  free(af); free(bf); free(cc);
}

static void special(uint64_t *a, int k) {
  memset(a, 0, W * 8);
  switch (k) {
  case 0: break;
  case 1: a[0] = 1; break;
  case 2: a[(NBITS - 1) / 64] = 1ULL << ((NBITS - 1) % 64); break;
  case 3: a[W - 1] = 1ULL << 63; break;
  case 4: for (int i = 0; i < NBITS; i++) a[i / 64] |= 1ULL << (i % 64); break;
  default: memset(a, 0xff, W * 8);
  }
}

int main(int argc, char **argv) {
  int iters = argc > 1 ? atoi(argv[1]) : 100, bad = 0, n = 0;
  uint64_t *a = malloc(W * 8), *b = malloc(W * 8), *r = calloc(2 * W, 8), *c = malloc(CW * 8);
  for (int t = 0; t < 36 + iters; t++, n++) {
    if (t < 36) { special(a, t / 6); special(b, t % 6); }
    else {
      int full = t & 1;  // alternate degree < n and full width
      for (int i = 0; i < W; i++) { a[i] = next(); b[i] = next(); }
      if (!full) { a[W - 1] = b[W - 1] = 0; for (int i = NBITS; i < 64 * W; i++) { a[i / 64] &= ~(1ULL << (i % 64)); b[i / 64] &= ~(1ULL << (i % 64)); } }
    }
    school(r, a, b);
    fft(c, a, b);
    // the FFT output has CW words; the schoolbook product 2W words, zero above CW when CW < 2W
    int ok = memcmp(r, c, CW * 8) == 0;
    for (int i = CW; i < 2 * W; i++) ok &= r[i] == 0;
    if (!ok) { if (bad < 3) fprintf(stderr, "mismatch at test %d\n", t); bad++; }
  }
  printf("%d tests, %d mismatches\n", n, bad);
  return bad != 0;
}
