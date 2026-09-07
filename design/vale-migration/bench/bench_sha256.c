/* SHA-256: Vale assembly vs C-with-SHA-NI-intrinsics vs HACL* portable C.
 *
 * Validates that all three agree, then measures. Expect ~1.00x for the
 * intrinsics version -- both it and Vale are bound by sha256rnds2 latency.
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <x86intrin.h>

#include "internal/Hacl_Hash_SHA2.h"
#include "sha256_ni.h"

/* The Vale routine, from dist/vale/sha256-x86_64-linux.S. */
extern uint64_t sha256_update(uint32_t *st, uint8_t *b, uint64_t n, uint32_t *k);

static const uint32_t IV[8] = {
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
};

#define NB 1024   /* blocks per call: 64 KiB */
#define R  200

int main(void)
{
  static uint8_t buf[NB * 64];
  for (size_t i = 0; i < sizeof buf; i++) buf[i] = (uint8_t)(i * 31 + 7);

  uint32_t a[8], b[8], c[8];
  memcpy(a, IV, 32); memcpy(b, IV, 32); memcpy(c, IV, 32);

  /* Hacl_Hash_SHA2_k224_256 is const; Vale's prototype is not. */
  sha256_update(a, buf, NB, (uint32_t *)Hacl_Hash_SHA2_k224_256);
  sha256_ni_update(b, buf, NB);
  Hacl_Hash_SHA2_sha256_update_nblocks(NB * 64, buf, c);

  int ok = (memcmp(a, b, 32) == 0) && (memcmp(a, c, 32) == 0);
  printf("digests match -- Vale==intrinsics: %s   Vale==pureC: %s\n",
         memcmp(a, b, 32) == 0 ? "YES" : "NO",
         memcmp(a, c, 32) == 0 ? "YES" : "NO");
  if (!ok) return 1;

  double bv = 1e30, bi = 1e30, bc = 1e30;
  unsigned long long t0, t1;
  double v;

  for (int r = 0; r < 7; r++) {
    /* The memory barrier is load-bearing: without it clang hoists the whole
     * loop out and reports 0.00 c/B. */
    memcpy(a, IV, 32);
    t0 = __rdtsc();
    for (int k = 0; k < R; k++) {
      sha256_update(a, buf, NB, (uint32_t *)Hacl_Hash_SHA2_k224_256);
      __asm__ volatile("" ::: "memory");
    }
    t1 = __rdtsc();
    v = (double)(t1 - t0) / ((double)R * NB * 64); if (v < bv) bv = v;

    memcpy(b, IV, 32);
    t0 = __rdtsc();
    for (int k = 0; k < R; k++) {
      sha256_ni_update(b, buf, NB);
      __asm__ volatile("" ::: "memory");
    }
    t1 = __rdtsc();
    v = (double)(t1 - t0) / ((double)R * NB * 64); if (v < bi) bi = v;

    memcpy(c, IV, 32);
    t0 = __rdtsc();
    for (int k = 0; k < R; k++) {
      Hacl_Hash_SHA2_sha256_update_nblocks(NB * 64, buf, c);
      __asm__ volatile("" ::: "memory");
    }
    t1 = __rdtsc();
    v = (double)(t1 - t0) / ((double)R * NB * 64); if (v < bc) bc = v;
  }

  printf("SHA-256 Vale asm     (SHA-NI) : %5.2f cycles/byte\n", bv);
  printf("SHA-256 C intrinsics (SHA-NI) : %5.2f cycles/byte  (%.2fx vs Vale)\n", bi, bi / bv);
  printf("SHA-256 HACL* pure C (scalar) : %5.2f cycles/byte  (%.2fx vs Vale)\n", bc, bc / bv);
  return 0;
}
