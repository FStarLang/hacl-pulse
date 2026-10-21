/* Salsa20's sixteen- and eight-way paths, differentially, at every length
 * they can split.
 *
 * Hacl_Salsa20_encrypt hands whole 1024-byte chunks to the AVX-512 code in
 * Hacl.Salsa20.Vec512, then a whole 512-byte chunk to the AVX2 code in
 * Hacl.Salsa20.Vec256, and finishes the rest one block at a time from the
 * block counter where the vector code stopped.  The seams are therefore at
 * every multiple of 512 and at every block boundary after it.  This test
 * runs every length from 0 to 2100 bytes against a plain Salsa20 block
 * function written here (Bernstein's specification, 64-bit counter with a
 * zero high word), at counters 0 and 1, and at counters close enough
 * to 2^32 that the last legal block falls inside or just after a chunk.
 * It also checks that the input is left alone and nothing past the end of
 * the output is written.
 *
 * On a machine without AVX-512F or AVX2 this exercises the remaining paths
 * only, and still passes.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl.h"

#define MAX 2100

static uint32_t rd32(const uint8_t *p) {
  return (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 |
         (uint32_t)p[3] << 24;
}

static uint32_t rotl(uint32_t x, int s) { return (x << s) | (x >> (32 - s)); }

#define QR(a, b, c, d)                                                         \
  b ^= rotl(a + d, 7);                                                         \
  c ^= rotl(b + a, 9);                                                         \
  d ^= rotl(c + b, 13);                                                        \
  a ^= rotl(d + c, 18);

static void ref_block(uint8_t out[64], const uint8_t key[32],
                      const uint8_t nonce[8], uint32_t ctr) {
  uint32_t s[16], x[16];
  s[0] = 0x61707865; s[5] = 0x3320646e; s[10] = 0x79622d32; s[15] = 0x6b206574;
  for (int i = 0; i < 4; i++) s[1 + i] = rd32(key + 4 * i);
  for (int i = 0; i < 4; i++) s[11 + i] = rd32(key + 16 + 4 * i);
  s[6] = rd32(nonce); s[7] = rd32(nonce + 4);
  s[8] = ctr; s[9] = 0;
  memcpy(x, s, sizeof x);
  for (int r = 0; r < 10; r++) {
    QR(x[0], x[4], x[8], x[12]) QR(x[5], x[9], x[13], x[1])
    QR(x[10], x[14], x[2], x[6]) QR(x[15], x[3], x[7], x[11])
    QR(x[0], x[1], x[2], x[3]) QR(x[5], x[6], x[7], x[4])
    QR(x[10], x[11], x[8], x[9]) QR(x[15], x[12], x[13], x[14])
  }
  for (int i = 0; i < 16; i++) {
    uint32_t w = x[i] + s[i];
    out[4 * i] = (uint8_t)w;
    out[4 * i + 1] = (uint8_t)(w >> 8);
    out[4 * i + 2] = (uint8_t)(w >> 16);
    out[4 * i + 3] = (uint8_t)(w >> 24);
  }
}

static void ref_encrypt(uint8_t *out, const uint8_t *msg, size_t len,
                        const uint8_t key[32], const uint8_t nonce[8],
                        uint32_t ctr) {
  uint8_t ks[64];
  for (size_t b = 0; b < len; b += 64, ctr++) {
    ref_block(ks, key, nonce, ctr);
    for (size_t k = 0; k < 64 && b + k < len; k++) out[b + k] = msg[b + k] ^ ks[k];
  }
}

static uint8_t key[32], nonce[8], msg[MAX], copy[MAX];
static uint8_t want[MAX], got[MAX + 64];

int main(void) {
  int failures = 0;
  uint64_t seed = 0x2545f4914f6cdd1dULL;
  for (size_t i = 0; i < sizeof key; i++) key[i] = (uint8_t)(i * 29 + 3);
  for (size_t i = 0; i < sizeof nonce; i++) nonce[i] = (uint8_t)(i * 13 + 7);
  for (size_t i = 0; i < MAX; i++) {
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
    msg[i] = (uint8_t)(seed >> 24);
  }
  memcpy(copy, msg, MAX);

  /* For a counter near the top, only lengths up to (2^32 - ctr) * 64 are in
     the contract; those are the ones tried. */
  static const uint32_t ctrs[] = {0, 1, 0xffffffffu - 40, 0xffffffffu - 24, 0xffffffffu - 8,
                                  0xffffffffu - 7, 0xffffffffu};
  for (size_t c = 0; c < sizeof ctrs / sizeof ctrs[0]; c++) {
    uint32_t ctr = ctrs[c];
    uint64_t room = ((uint64_t)1 << 32) - ctr;
    size_t lim = room * 64 < MAX ? (size_t)(room * 64) : MAX;
    int bad = 0;
    for (size_t len = 0; len <= lim; len++) {
      ref_encrypt(want, msg, len, key, nonce, ctr);
      memset(got, 0xc3, sizeof got);
      Hacl_Salsa20_encrypt(got, msg, len, key, nonce, ctr);
      bool ok = memcmp(got, want, len) == 0 && memcmp(msg, copy, MAX) == 0;
      for (size_t i = len; i < len + 64 && i < sizeof got; i++)
        ok &= got[i] == 0xc3;
      if (!ok) {
        if (bad < 5) printf("  FAIL ctr=%u len=%zu\n", ctr, len);
        bad++;
      }
    }
    if (bad) {
      printf("  FAIL ctr=%u: %d length(s) of 0..%zu wrong\n", ctr, bad, lim);
      failures++;
    } else {
      printf("  ok   ctr=%u, every length 0..%zu\n", ctr, lim);
    }
  }

  if (failures) {
    printf("%d Salsa20 differential check(s) failed\n", failures);
    return 1;
  }
  printf("Salsa20 agrees with the reference at every length\n");
  return 0;
}
