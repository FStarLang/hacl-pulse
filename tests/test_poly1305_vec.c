/* Poly1305's four-lane path, differentially, at every length it can split.
 *
 * Hacl_Poly1305_mac hands the longest whole multiple of four blocks to the
 * AVX2 code in Hacl.Poly1305.Vec256 once the message has at least eight,
 * and finishes the rest one block at a time.  This test runs every length
 * from 0 to 2100 bytes against a plain RFC 8439 Poly1305 written here, with
 * random keys, with r at its largest after clamping, and with all-0xff
 * messages, which keep every limb as large as the bounds allow.  It also
 * checks that the input is left alone.
 *
 * On a machine without AVX2 this exercises the scalar path only, and still
 * passes.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl.h"

#define MAX 2100

/* Bits [lo, lo + 26) of a little-endian byte string of n bytes. */
static uint64_t bits26(const uint8_t *p, size_t n, unsigned lo) {
  uint64_t x = 0;
  for (unsigned b = 0; b < 26; b++) {
    unsigned k = lo + b;
    if (k / 8 < n) x |= (uint64_t)((p[k / 8] >> (k % 8)) & 1) << b;
  }
  return x;
}

/* Five limbs of 26 bits, fully carried modulo 2^130 - 5. */
static void carry(uint64_t h[5]) {
  for (int pass = 0; pass < 3; pass++) {
    for (int i = 0; i < 4; i++) {
      h[i + 1] += h[i] >> 26;
      h[i] &= 0x3ffffff;
    }
    h[0] += 5 * (h[4] >> 26);
    h[4] &= 0x3ffffff;
  }
}

/* h <- h * r modulo 2^130 - 5, the schoolbook way. */
static void mulmod(uint64_t h[5], const uint64_t r[5]) {
  uint64_t d[5] = {0};
  for (int i = 0; i < 5; i++)
    for (int j = 0; j < 5; j++) {
      uint64_t p = h[i] * r[j];
      if (i + j < 5) d[i + j] += p;
      else d[i + j - 5] += 5 * p;
    }
  memcpy(h, d, sizeof d);
  carry(h);
}

static void ref_mac(uint8_t tag[16], const uint8_t *msg, size_t len,
                    const uint8_t key[32]) {
  uint8_t rb[16];
  memcpy(rb, key, 16);
  rb[3] &= 15; rb[7] &= 15; rb[11] &= 15; rb[15] &= 15;
  rb[4] &= 252; rb[8] &= 252; rb[12] &= 252;
  uint64_t r[5], h[5] = {0};
  for (int i = 0; i < 5; i++) r[i] = bits26(rb, 16, 26 * i);
  for (size_t off = 0; off < len; off += 16) {
    uint8_t blk[17] = {0};
    size_t n = len - off < 16 ? len - off : 16;
    memcpy(blk, msg + off, n);
    blk[n] = 1;
    for (int i = 0; i < 5; i++) h[i] += bits26(blk, 17, 26 * i);
    mulmod(h, r);
  }
  /* h is below 2^130; subtract the prime once if it is not below it. */
  carry(h);
  uint64_t g[5];
  memcpy(g, h, sizeof g);
  g[0] += 5;
  for (int i = 0; i < 4; i++) {
    g[i + 1] += g[i] >> 26;
    g[i] &= 0x3ffffff;
  }
  if (g[4] >> 26) {
    g[4] &= 0x3ffffff;
    memcpy(h, g, sizeof g);
  }
  unsigned __int128 acc = 0;
  for (int i = 4; i >= 0; i--) acc = (acc << 26) | h[i];
  unsigned __int128 s = 0;
  for (int i = 15; i >= 0; i--) s = (s << 8) | key[16 + i];
  acc += s;
  for (int i = 0; i < 16; i++) tag[i] = (uint8_t)(acc >> (8 * i));
}

static uint8_t msg[MAX], copy[MAX];

int main(void) {
  int failures = 0;
  uint64_t seed = 0x2545f4914f6cdd1dULL;
  uint8_t key[32];

  for (int kind = 0; kind < 4; kind++) {
    for (size_t i = 0; i < MAX; i++) {
      seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
      msg[i] = kind >= 2 ? 0xff : (uint8_t)(seed >> 24);
    }
    for (size_t i = 0; i < 32; i++) {
      seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
      key[i] = kind % 2 ? 0xff : (uint8_t)(seed >> 24);
    }
    memcpy(copy, msg, MAX);
    int bad = 0;
    for (size_t len = 0; len <= MAX; len++) {
      uint8_t want[16], got[16];
      ref_mac(want, msg, len, key);
      Hacl_Poly1305_mac(got, msg, len, key);
      if (memcmp(got, want, 16) != 0 || memcmp(msg, copy, MAX) != 0) {
        if (bad < 5) printf("  FAIL kind=%d len=%zu\n", kind, len);
        bad++;
      }
    }
    static const char *names[] = {"random key, random message",
                                  "largest r, random message",
                                  "random key, all-0xff message",
                                  "largest r, all-0xff message"};
    if (bad) {
      printf("  FAIL %s: %d length(s) wrong\n", names[kind], bad);
      failures++;
    } else {
      printf("  ok   %s, every length 0..%d\n", names[kind], MAX);
    }
  }

  if (failures) {
    printf("%d Poly1305 differential check(s) failed\n", failures);
    return 1;
  }
  printf("Poly1305 agrees with the reference at every length\n");
  return 0;
}
