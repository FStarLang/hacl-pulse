/* AES-GCM's stitched path, differentially, at every length it can split.
 *
 * Messages of 128 bytes or more are encrypted by Hacl.AES.GCM.Stitch, which
 * hashes each 128 bytes of ciphertext while encrypting the next 128, and
 * finishes the tail (under 128 bytes) with the ordinary counter-mode and
 * GHASH code.  The CAVP vectors in test_gcm.c stop at 51 bytes, so they
 * never get there.
 *
 * Decryption does not use the stitched path: it hashes the ciphertext with
 * Hacl.AES.GHash and decrypts it with Hacl.AES.CTR, separately.  GCM is a
 * function, so a ciphertext and tag that decrypt to the plaintext under
 * that code are exactly what the unstitched encryption would have produced.
 * This test therefore encrypts at every length from 0 to 1300 bytes, with
 * both key sizes, both nonce paths and several lengths of associated data,
 * and checks that decryption accepts the result and gives the plaintext
 * back; that flipping a bit of the ciphertext or of the tag is rejected,
 * leaving the output untouched; and that nothing past the end of the output
 * buffer is written.  Every length runs both in place (out == msg) and with
 * a separate output buffer, in which case the input must come back
 * unchanged.
 *
 * On a machine without AES-NI and PCLMULQDQ the stitched path is not taken
 * and this exercises the portable code only, and still passes.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl.h"

#define MAX 1300
#define PAD 32

static uint64_t rng = 0x243f6a8885a308d3ULL;

static uint8_t rnd8(void) {
  rng ^= rng << 13;
  rng ^= rng >> 7;
  rng ^= rng << 17;
  return (uint8_t)(rng >> 24);
}

static void fill(uint8_t *b, size_t n) {
  for (size_t i = 0; i < n; i++)
    b[i] = rnd8();
}

static int failures = 0;

static void encrypt(int bits, bool expanded, uint8_t *out, uint8_t *t,
                    uint8_t *m, size_t n, uint8_t *k, uint8_t *iv,
                    size_t ivlen, uint8_t *a, size_t alen) {
  uint8_t ek[240], hk[128];
  if (bits == 128) {
    if (expanded) {
      Hacl_AES_GCM_aes128_expand(ek, hk, k);
      Hacl_AES_GCM_aes128_encrypt_expanded(out, t, m, n, ek, hk, iv, ivlen, a,
                                           alen);
    } else
      Hacl_AES_GCM_aes128_encrypt(out, t, m, n, k, iv, ivlen, a, alen);
  } else {
    if (expanded) {
      Hacl_AES_GCM_aes256_expand(ek, hk, k);
      Hacl_AES_GCM_aes256_encrypt_expanded(out, t, m, n, ek, hk, iv, ivlen, a,
                                           alen);
    } else
      Hacl_AES_GCM_aes256_encrypt(out, t, m, n, k, iv, ivlen, a, alen);
  }
}

static bool decrypt(int bits, uint8_t *out, uint8_t *m, size_t n, uint8_t *t,
                    uint8_t *k, uint8_t *iv, size_t ivlen, uint8_t *a,
                    size_t alen) {
  if (bits == 128)
    return Hacl_AES_GCM_aes128_decrypt(out, m, n, t, k, iv, ivlen, a, alen);
  return Hacl_AES_GCM_aes256_decrypt(out, m, n, t, k, iv, ivlen, a, alen);
}

/* In place, the input is [buf] itself.  Otherwise it is [src], which must
   come back unchanged, and [buf] starts out holding junk.  Either way the
   PAD bytes after [buf] must survive. */
static uint8_t *input(bool inplace, uint8_t *buf, uint8_t *src,
                      const uint8_t *from, size_t n) {
  if (inplace) {
    memcpy(buf, from, n);
    return buf;
  }
  memcpy(src, from, n);
  memset(buf, 0xcc, n);
  return src;
}

static bool intact(bool inplace, const uint8_t *buf, const uint8_t *src,
                   const uint8_t *from, size_t n) {
  for (size_t i = 0; i < PAD; i++)
    if (buf[n + i] != 0x5c)
      return false;
  return inplace || memcmp(src, from, n) == 0;
}

static void one(int bits, bool expanded, bool inplace, size_t n, size_t ivlen,
                size_t alen) {
  uint8_t k[32], iv[64], a[100], pt[MAX], buf[MAX + PAD], src[MAX], tag[16],
      t2[16];
  const char *how = inplace ? "in place" : "separate";
  fill(k, sizeof k);
  fill(iv, ivlen);
  fill(a, alen);
  fill(pt, n);
  memset(buf + n, 0x5c, PAD);

  uint8_t *m = input(inplace, buf, src, pt, n);
  encrypt(bits, expanded, buf, tag, m, n, k, iv, ivlen, a, alen);
  if (!intact(inplace, buf, src, pt, n)) {
    printf("FAIL aes%d %s n=%zu iv=%zu aad=%zu: wrote past the end or to "
           "the input\n",
           bits, how, n, ivlen, alen);
    failures++;
    return;
  }

  uint8_t ct[MAX];
  memcpy(ct, buf, n);
  m = input(inplace, buf, src, ct, n);
  if (!decrypt(bits, buf, m, n, tag, k, iv, ivlen, a, alen) ||
      memcmp(buf, pt, n) != 0 || !intact(inplace, buf, src, ct, n)) {
    printf("FAIL aes%d%s %s n=%zu iv=%zu aad=%zu: does not decrypt\n", bits,
           expanded ? " expanded" : "", how, n, ivlen, alen);
    failures++;
    return;
  }

  uint8_t before[MAX];
  memcpy(t2, tag, 16);
  t2[n % 16] ^= 1;
  m = input(inplace, buf, src, ct, n);
  memcpy(before, buf, n);
  if (decrypt(bits, buf, m, n, t2, k, iv, ivlen, a, alen)) {
    printf("FAIL aes%d %s n=%zu: corrupted tag accepted\n", bits, how, n);
    failures++;
    return;
  }
  if (memcmp(buf, before, n) != 0) {
    printf("FAIL aes%d %s n=%zu: output written on a rejected tag\n", bits,
           how, n);
    failures++;
    return;
  }
  if (n > 0) {
    uint8_t bad[MAX];
    memcpy(bad, ct, n);
    bad[(n * 7) % n] ^= 0x80;
    m = input(inplace, buf, src, bad, n);
    if (decrypt(bits, buf, m, n, tag, k, iv, ivlen, a, alen)) {
      printf("FAIL aes%d %s n=%zu: corrupted ciphertext accepted\n", bits,
             how, n);
      failures++;
    }
  }
}

int main(void) {
  static const size_t ivs[] = {12, 16, 60};
  static const size_t aads[] = {0, 13, 16, 100};
  int count = 0;
  for (int bits = 128; bits <= 256; bits += 128)
    for (size_t n = 0; n <= MAX; n++) {
      size_t ivlen = ivs[n % 3];
      size_t alen = aads[(n / 3) % 4];
      one(bits, (n & 1) != 0, true, n, ivlen, alen);
      one(bits, (n & 1) != 0, false, n, ivlen, alen);
      count++;
    }
  if (failures == 0) {
    printf("test_gcm_long: all %d lengths round-trip and reject forgeries, "
           "in place and separate\n",
           count);
    return 0;
  }
  printf("test_gcm_long: %d failures\n", failures);
  return 1;
}
