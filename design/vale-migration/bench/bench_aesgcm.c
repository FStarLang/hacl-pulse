/* AES-128-GCM: EverCrypt (Vale assembly) vs src/aesgcm_x86_intrin.c.
 *
 * Validates ciphertext and tag bit-for-bit against EverCrypt before timing.
 *
 * Fairness note: both sides get a pre-built key context. EverCrypt keeps its
 * expanded key and H-powers in EverCrypt_AEAD_state_s across calls; an
 * earlier version of this benchmark rebuilt the C side's key schedule on
 * every call, which understated it by ~4% at 16 KiB and much more on short
 * messages.
 *
 * Build with -DLEN=<n> to sweep message sizes.
 */

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <x86intrin.h>

#include "EverCrypt_AEAD.h"
#include "EverCrypt_AutoConfig2.h"
#include "aesgcm_x86_intrin.h"

#ifndef LEN
#define LEN 16384
#endif
#ifndef REPS
#define REPS 2000
#endif

int main(void)
{
  EverCrypt_AutoConfig2_init();

  static aesgcm_ctx G;
  static uint8_t pt[LEN], ct1[LEN], ct2[LEN], aad[20];
  uint8_t key[16], iv16[16], tag1[16], tag2[16];

  for (int i = 0; i < LEN; i++) pt[i]  = (uint8_t)(i * 29 + 11);
  for (int i = 0; i < 16; i++)  key[i] = (uint8_t)(i * 3 + 1);
  for (int i = 0; i < 12; i++)  iv16[i] = (uint8_t)(i * 7 + 2);
  iv16[12] = 0; iv16[13] = 0; iv16[14] = 0; iv16[15] = 1;  /* counter = 1 */
  for (int i = 0; i < 20; i++)  aad[i] = (uint8_t)(i + 5);

  EverCrypt_AEAD_state_s *st = NULL;
  if (EverCrypt_AEAD_create_in(Spec_Agile_AEAD_AES128_GCM, &st, key)
        != EverCrypt_Error_Success) {
    printf("EverCrypt_AEAD_create_in failed (no AES-NI?)\n");
    return 1;
  }
  aesgcm128_init(&G, key);

  EverCrypt_AEAD_encrypt(st, iv16, 12, aad, 20, pt, LEN, ct1, tag1);
  aesgcm128_encrypt(&G, iv16, aad, 20, pt, LEN, ct2, tag2);

  int ok = !memcmp(ct1, ct2, LEN) && !memcmp(tag1, tag2, 16);
  printf("AGG=%d len=%d  ciphertext+tag match EverCrypt: %s\n",
         AESGCM_AGG, LEN, ok ? "YES" : "NO");
  if (!ok) return 1;

  double bv = 1e30, bi = 1e30;
  unsigned long long c0, c1;
  for (int r = 0; r < 7; r++) {
    c0 = __rdtsc();
    for (int k = 0; k < REPS; k++) {
      EverCrypt_AEAD_encrypt(st, iv16, 12, aad, 20, pt, LEN, ct1, tag1);
      __asm__ volatile("" ::: "memory");
    }
    c1 = __rdtsc();
    double v = (double)(c1 - c0) / ((double)REPS * LEN); if (v < bv) bv = v;

    c0 = __rdtsc();
    for (int k = 0; k < REPS; k++) {
      aesgcm128_encrypt(&G, iv16, aad, 20, pt, LEN, ct2, tag2);
      __asm__ volatile("" ::: "memory");
    }
    c1 = __rdtsc();
    v = (double)(c1 - c0) / ((double)REPS * LEN); if (v < bi) bi = v;
  }

  printf("  Vale asm     : %5.3f c/B\n"
         "  C intrinsics : %5.3f c/B   (%.2fx vs Vale)\n", bv, bi, bi / bv);
  return 0;
}
