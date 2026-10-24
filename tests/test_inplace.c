/* In-place encryption and decryption, differentially.
 *
 * The AEAD and secretbox functions below take the output buffer either as
 * exactly the input buffer or as one that does not overlap it.  For a range
 * of lengths (around the 64-byte block, the 32-byte secretbox split and the
 * vector chunk sizes) this encrypts once into a separate buffer and once in
 * place, checks that ciphertext and tag agree, then decrypts both ways and
 * checks the round trip.  A corrupted tag must be rejected in place too.
 * (ChaCha20 and Salsa20 alone are covered by their own vector tests, AES-GCM
 * by test_gcm.)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl.h"

#define MAX 2200

static const size_t lens[] = {0,   1,   15,  16,  31,  32,   33,   63,   64,
                              65,  95,  96,  127, 128, 255,  256,  511,  512,
                              513, 1023, 1024, 1025, 1056, 2048, 2111, 2200};

static uint8_t msg[MAX], ct[MAX], buf[MAX], pt[MAX];
static uint8_t tag1[16], tag2[16];

static void fill(uint8_t *p, size_t n, uint32_t seed) {
  for (size_t i = 0; i < n; i++) {
    seed = seed * 1103515245u + 12345u;
    p[i] = (uint8_t)(seed >> 16);
  }
}

static int fail(const char *what, size_t len) {
  printf("  FAIL %s (len %zu)\n", what, len);
  return 1;
}

static int test_chachapoly(void) {
  uint8_t key[32], nonce[12], aad[13];
  fill(key, 32, 1);
  fill(nonce, 12, 2);
  fill(aad, 13, 3);
  int err = 0;
  for (size_t t = 0; t < sizeof lens / sizeof lens[0]; t++) {
    size_t n = lens[t];
    fill(msg, n, 100 + (uint32_t)n);
    Hacl_Chacha20Poly1305_encrypt(ct, tag1, msg, n, aad, 13, key, nonce);
    memcpy(buf, msg, n);
    Hacl_Chacha20Poly1305_encrypt(buf, tag2, buf, n, aad, 13, key, nonce);
    if (memcmp(buf, ct, n) || memcmp(tag1, tag2, 16))
      err |= fail("chachapoly encrypt in place", n);

    if (!Hacl_Chacha20Poly1305_decrypt(pt, ct, n, tag1, aad, 13, key, nonce) ||
        memcmp(pt, msg, n))
      err |= fail("chachapoly decrypt", n);
    if (!Hacl_Chacha20Poly1305_decrypt(buf, buf, n, tag1, aad, 13, key,
                                       nonce) ||
        memcmp(buf, msg, n))
      err |= fail("chachapoly decrypt in place", n);

    memcpy(buf, ct, n);
    tag2[0] ^= 1;
    if (Hacl_Chacha20Poly1305_decrypt(buf, buf, n, tag2, aad, 13, key, nonce))
      err |= fail("chachapoly bad tag in place", n);
  }
  if (!err)
    printf("  ok   chacha20poly1305 in place\n");
  return err;
}

static int test_secretbox(void) {
  uint8_t key[32], nonce[24];
  fill(key, 32, 4);
  fill(nonce, 24, 5);
  int err = 0;
  for (size_t t = 0; t < sizeof lens / sizeof lens[0]; t++) {
    size_t n = lens[t];
    fill(msg, n, 200 + (uint32_t)n);
    if (Hacl_NaCl_crypto_secretbox_detached(ct, tag1, msg, n, nonce, key))
      err |= fail("secretbox detached", n);
    memcpy(buf, msg, n);
    if (Hacl_NaCl_crypto_secretbox_detached(buf, tag2, buf, n, nonce, key) ||
        memcmp(buf, ct, n) || memcmp(tag1, tag2, 16))
      err |= fail("secretbox detached in place", n);

    if (Hacl_NaCl_crypto_secretbox_open_detached(pt, ct, tag1, n, nonce, key) ||
        memcmp(pt, msg, n))
      err |= fail("secretbox open", n);
    if (Hacl_NaCl_crypto_secretbox_open_detached(buf, buf, tag1, n, nonce,
                                                 key) ||
        memcmp(buf, msg, n))
      err |= fail("secretbox open in place", n);

    memcpy(buf, ct, n);
    tag2[0] ^= 1;
    if (!Hacl_NaCl_crypto_secretbox_open_detached(buf, buf, tag2, n, nonce,
                                                  key))
      err |= fail("secretbox bad tag in place", n);
  }
  if (!err)
    printf("  ok   secretbox in place\n");
  return err;
}

static int test_box(void) {
  uint8_t sk1[32], sk2[32], pk1[32], pk2[32], nonce[24], k[32];
  static const uint8_t base[32] = {9};
  fill(sk1, 32, 6);
  fill(sk2, 32, 7);
  fill(nonce, 24, 8);
  Hacl_Curve25519_scalarmult(pk1, sk1, (uint8_t *)base);
  Hacl_Curve25519_scalarmult(pk2, sk2, (uint8_t *)base);
  int err = 0;
  if (Hacl_NaCl_crypto_box_beforenm(k, pk2, sk1))
    return fail("box beforenm", 0);
  for (size_t t = 0; t < sizeof lens / sizeof lens[0]; t++) {
    size_t n = lens[t];
    fill(msg, n, 300 + (uint32_t)n);
    if (Hacl_NaCl_crypto_box_detached(ct, tag1, msg, n, nonce, pk2, sk1))
      err |= fail("box detached", n);
    memcpy(buf, msg, n);
    if (Hacl_NaCl_crypto_box_detached(buf, tag2, buf, n, nonce, pk2, sk1) ||
        memcmp(buf, ct, n) || memcmp(tag1, tag2, 16))
      err |= fail("box detached in place", n);
    memcpy(buf, msg, n);
    if (Hacl_NaCl_crypto_box_detached_afternm(buf, tag2, buf, n, nonce, k) ||
        memcmp(buf, ct, n) || memcmp(tag1, tag2, 16))
      err |= fail("box detached_afternm in place", n);

    memcpy(buf, ct, n);
    if (Hacl_NaCl_crypto_box_open_detached(buf, buf, tag1, n, nonce, pk1,
                                           sk2) ||
        memcmp(buf, msg, n))
      err |= fail("box open in place", n);
    memcpy(buf, ct, n);
    if (Hacl_NaCl_crypto_box_open_detached_afternm(buf, buf, tag1, n, nonce,
                                                   k) ||
        memcmp(buf, msg, n))
      err |= fail("box open_afternm in place", n);
  }
  if (!err)
    printf("  ok   box in place\n");
  return err;
}

int main(void) {
  int err = 0;
  err |= test_chachapoly();
  err |= test_secretbox();
  err |= test_box();
  if (err) {
    printf("test_inplace: FAILED\n");
    return 1;
  }
  printf("test_inplace: all passed\n");
  return 0;
}
