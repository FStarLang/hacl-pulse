/* The axioms of lib/Hacl.Vec128.fst, checked against an independent AES.
 *
 * Every `assume val` in that module is a claim about a hardware instruction
 * that F* cannot check.  This test checks them: `aesenc` is claimed to be
 * `Spec.AES.round` and `aesenclast` to be `Spec.AES.last_round`, and the
 * reference below is a direct transcription of FIPS 197 -- its own S-box
 * table, its own ShiftRows, its own MixColumns -- written from the standard
 * rather than shared with anything in the library, so agreement is evidence
 * and not a tautology.
 *
 * It runs on a fixed set of edge cases and then on pseudo-random inputs, and
 * it is skipped, not failed, on a machine without the instructions.  The
 * other half of the evidence is tests/test_gcm.c: its 450 CAVP cases go
 * through cipher_ni on any machine that has AES-NI.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl_Vec128.h"
#include "test_util.h"

static const uint8_t sbox[256] = {
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b,
    0xfe, 0xd7, 0xab, 0x76, 0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0,
    0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0, 0xb7, 0xfd, 0x93, 0x26,
    0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2,
    0xeb, 0x27, 0xb2, 0x75, 0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0,
    0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84, 0x53, 0xd1, 0x00, 0xed,
    0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f,
    0x50, 0x3c, 0x9f, 0xa8, 0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5,
    0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2, 0xcd, 0x0c, 0x13, 0xec,
    0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14,
    0xde, 0x5e, 0x0b, 0xdb, 0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c,
    0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79, 0xe7, 0xc8, 0x37, 0x6d,
    0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f,
    0x4b, 0xbd, 0x8b, 0x8a, 0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e,
    0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e, 0xe1, 0xf8, 0x98, 0x11,
    0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f,
    0xb0, 0x54, 0xbb, 0x16,
};

static uint8_t xtime(uint8_t a) {
  return (uint8_t)((uint8_t)(a << 1) ^ (uint8_t)((a >> 7) * 0x1b));
}

/* Column-major, as in FIPS 197: byte 4*c + r is row r of column c. */
static void ref_round(uint8_t out[16], const uint8_t st[16],
                      const uint8_t k[16], bool last) {
  uint8_t s[16];
  for (int i = 0; i < 16; i++) s[i] = sbox[st[i]];

  uint8_t t[16];
  for (int c = 0; c < 4; c++)
    for (int r = 0; r < 4; r++) t[4 * c + r] = s[4 * ((c + r) % 4) + r];

  if (last) {
    memcpy(out, t, 16);
  } else {
    for (int c = 0; c < 4; c++) {
      const uint8_t *a = t + 4 * c;
      uint8_t *o = out + 4 * c;
      o[0] = (uint8_t)(xtime(a[0]) ^ (xtime(a[1]) ^ a[1]) ^ a[2] ^ a[3]);
      o[1] = (uint8_t)(a[0] ^ xtime(a[1]) ^ (xtime(a[2]) ^ a[2]) ^ a[3]);
      o[2] = (uint8_t)(a[0] ^ a[1] ^ xtime(a[2]) ^ (xtime(a[3]) ^ a[3]));
      o[3] = (uint8_t)((xtime(a[0]) ^ a[0]) ^ a[1] ^ a[2] ^ xtime(a[3]));
    }
  }
  for (int i = 0; i < 16; i++) out[i] ^= k[i];
}

static void ref_xor(uint8_t out[16], const uint8_t a[16], const uint8_t b[16]) {
  for (int i = 0; i < 16; i++) out[i] = (uint8_t)(a[i] ^ b[i]);
}

/* xorshift64*, so the inputs are reproducible and the same everywhere. */
static uint64_t rng_state = 0x2545f4914f6cdd1dULL;
static void fill(uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; i++) {
    rng_state ^= rng_state >> 12;
    rng_state ^= rng_state << 25;
    rng_state ^= rng_state >> 27;
    p[i] = (uint8_t)((rng_state * 0x2545f4914f6cdd1dULL) >> 56);
  }
}

/* The same rule the generated code obeys: a function that reaches an
   intrinsic wrapper must carry the wrapper's target attribute, or the
   compiler refuses to inline it.  See lib/Hacl.Vec128.fst. */
#if defined(__x86_64__) || defined(__i386__)
#define TEST_NI __attribute__((target("aes,pclmul,ssse3,sse4.1")))
#else
#define TEST_NI
#endif

TEST_NI static void vload_store(uint8_t *dst, const uint8_t *src) {
  Hacl_Vec128_store(dst, Hacl_Vec128_load((uint8_t *)src));
}

TEST_NI static void vzero(uint8_t *dst) {
  Hacl_Vec128_store(dst, Hacl_Vec128_zero());
}

TEST_NI static int one(const uint8_t st[16], const uint8_t k[16], const char *what) {
  uint8_t got[16], expected[16];
  int r = 0;

  Hacl_Vec128_store(got, Hacl_Vec128_aesenc(Hacl_Vec128_load((uint8_t *)st),
                                            Hacl_Vec128_load((uint8_t *)k)));
  ref_round(expected, st, k, false);
  if (memcmp(got, expected, 16) != 0) {
    r |= check(what, got, expected, 16);
  }

  Hacl_Vec128_store(got,
                    Hacl_Vec128_aesenclast(Hacl_Vec128_load((uint8_t *)st),
                                           Hacl_Vec128_load((uint8_t *)k)));
  ref_round(expected, st, k, true);
  if (memcmp(got, expected, 16) != 0) {
    r |= check(what, got, expected, 16);
  }

  Hacl_Vec128_store(got, Hacl_Vec128_xor(Hacl_Vec128_load((uint8_t *)st),
                                         Hacl_Vec128_load((uint8_t *)k)));
  ref_xor(expected, st, k);
  if (memcmp(got, expected, 16) != 0) {
    r |= check(what, got, expected, 16);
  }
  return r;
}

int main(void) {
  if (!Hacl_Vec128_supported()) {
    printf("  skip vec128: no AES instructions on this machine\n");
    return 0;
  }

  int r = 0;
  uint8_t st[16], k[16];

  /* Load and store must be the identity on the sixteen bytes in memory
     order, which is the assumption every other axiom is stated on top of. */
  fill(st, 16);
  vload_store(k, st);
  r |= check("vec128 load/store round trip", k, st, 16);

  memset(k, 0, 16);
  vzero(st);
  r |= check("vec128 zero", st, k, 16);

  memset(st, 0x00, 16);
  memset(k, 0x00, 16);
  r |= one(st, k, "vec128 AES round on zeroes");
  memset(st, 0xff, 16);
  memset(k, 0xff, 16);
  r |= one(st, k, "vec128 AES round on ones");
  for (int i = 0; i < 16; i++) {
    st[i] = (uint8_t)i;
    k[i] = (uint8_t)(0x0f - i);
  }
  r |= one(st, k, "vec128 AES round on a counting block");

  /* Every byte value has to go through the S-box at least once. */
  for (int b = 0; b < 256; b++) {
    memset(st, (uint8_t)b, 16);
    memset(k, 0, 16);
    r |= one(st, k, "vec128 AES round on a constant block");
  }

  for (int i = 0; i < 4096; i++) {
    fill(st, 16);
    fill(k, 16);
    r |= one(st, k, "vec128 AES round on random input");
  }

  if (r == 0) printf("all vec128 axioms agree with FIPS 197\n");
  return r;
}
