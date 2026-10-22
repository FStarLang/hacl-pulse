/* The axioms of lib/Hacl.Vec128.fst, checked against an independent AES.
 *
 * Every `assume val` in that module is a claim about a hardware instruction
 * that F* cannot check.  This test checks them: `aesenc` is claimed to be
 * `Spec.AES.round`, `aesenclast` to be `Spec.AES.last_round` and `subword`
 * to be four S-box lookups, and the reference below is a direct
 * transcription of FIPS 197 -- its own S-box table, its own ShiftRows, its
 * own MixColumns -- written from the standard rather than shared with
 * anything in the library, so agreement is evidence and not a tautology.
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

#if defined(__x86_64__)

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
#define TEST_NI __attribute__((target("aes,pclmul,ssse3,sse4.1")))

TEST_NI static void vload_store(uint8_t *dst, const uint8_t *src) {
  Hacl_Vec128_store(dst, Hacl_Vec128_load((uint8_t *)src));
}

TEST_NI static void vzero(uint8_t *dst) {
  Hacl_Vec128_store(dst, Hacl_Vec128_zero());
}

TEST_NI static void vreduction(uint8_t *dst) {
  Hacl_Vec128_store(dst, Hacl_Vec128_reduction());
}

TEST_NI static void vlane_one(uint8_t *dst) {
  Hacl_Vec128_store(dst, Hacl_Vec128_lane_one());
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

  /* [subword] is AESKEYGENASSIST with a zero round constant.  The axiom
     claims only that bytes eight to eleven of the result are the S-box
     applied to bytes twelve to fifteen of the argument, so only those four
     are compared; the rest of the expected block is copied from the result
     so that a failure prints the whole register. */
  Hacl_Vec128_store(got, Hacl_Vec128_subword(Hacl_Vec128_load((uint8_t *)st)));
  memcpy(expected, got, 16);
  for (int i = 0; i < 4; i++) expected[8 + i] = sbox[st[12 + i]];
  if (memcmp(got, expected, 16) != 0) {
    r |= check(what, got, expected, 16);
  }
  return r;
}


/* ---- the carry-less multiplier, the shifts and the byte reversal ----
 *
 * These axioms are stated in Hacl.Vec128 against Spec.CLMUL's little-endian
 * bit view: bit k of a register is bit k%8 of byte k/8.  The reference below
 * is that definition read literally -- one bit at a time, a convolution
 * written as a double loop -- which is slow and obviously right.
 */

static bool refbit(const uint8_t a[16], int k) {
  if (k < 0 || k >= 128) return false;
  return ((a[k / 8] >> (k % 8)) & 1) != 0;
}

static void refset(uint8_t a[16], int k, bool v) {
  if (v) a[k / 8] |= (uint8_t)(1u << (k % 8));
}

/* conv (lane a ha) (lane b hb) k, for every k in the register. */
static void ref_clmul(uint8_t out[16], const uint8_t a[16], const uint8_t b[16],
                      int ha, int hb) {
  memset(out, 0, 16);
  for (int k = 0; k < 128; k++) {
    bool acc = false;
    for (int i = 0; i < 64; i++)
      if (refbit(a, ha * 64 + i) && k - i >= 0 && k - i < 64 &&
          refbit(b, hb * 64 + k - i))
        acc = !acc;
    refset(out, k, acc);
  }
}

/* out bit k is a bit k - d, which for d a multiple of eight is a byte shift. */
static void ref_shift(uint8_t out[16], const uint8_t a[16], int d) {
  memset(out, 0, 16);
  for (int k = 0; k < 128; k++) refset(out, k, refbit(a, k - d));
}

/* The same within each 64-bit half. */
static void ref_lane_shift(uint8_t out[16], const uint8_t a[16], int d) {
  memset(out, 0, 16);
  for (int k = 0; k < 128; k++) {
    int r = k % 64;
    if (r - d >= 0 && r - d < 64) refset(out, k, refbit(a, k - d));
  }
}

static void ref_bswap(uint8_t out[16], const uint8_t a[16]) {
  for (int j = 0; j < 16; j++) out[j] = a[15 - j];
}

/* Quiet unless something is wrong: this runs a hundred-odd comparisons per
 * call and there are hundreds of calls. */
static int quiet(const char *what, const uint8_t got[16], const uint8_t exp[16]) {
  if (memcmp(got, exp, 16) == 0) return 0;
  return check(what, got, exp, 16);
}

TEST_NI static int one_clmul(const uint8_t a[16], const uint8_t b[16],
                             const char *what) {
  uint8_t got[16], expected[16];
  int r = 0;
  Hacl_Vec128_t va = Hacl_Vec128_load((uint8_t *)a);
  Hacl_Vec128_t vb = Hacl_Vec128_load((uint8_t *)b);

#define CLMUL_CASE(name, ha, hb)                                             \
  do {                                                                       \
    Hacl_Vec128_store(got, Hacl_Vec128_clmul_##name(va, vb));                \
    ref_clmul(expected, a, b, ha, hb);                                       \
    r |= quiet(what, got, expected);                                     \
  } while (0)
  CLMUL_CASE(ll, 0, 0);
  CLMUL_CASE(lh, 0, 1);
  CLMUL_CASE(hl, 1, 0);
  CLMUL_CASE(hh, 1, 1);
#undef CLMUL_CASE

#define SHIFT_CASE(name, d)                                                  \
  do {                                                                       \
    Hacl_Vec128_store(got, Hacl_Vec128_##name(va));                          \
    ref_shift(expected, a, d);                                               \
    r |= quiet(what, got, expected);                                     \
  } while (0)
  SHIFT_CASE(shift_left_bytes_4, 32);
  SHIFT_CASE(shift_right_bytes_4, -32);
  SHIFT_CASE(shift_left_bytes_8, 64);
  SHIFT_CASE(shift_right_bytes_8, -64);
#undef SHIFT_CASE

  for (uint32_t n = 0; n < 64; n++) {
    Hacl_Vec128_store(got, Hacl_Vec128_shift_left_lanes64(va, n));
    ref_lane_shift(expected, a, (int)n);
    r |= quiet(what, got, expected);
    Hacl_Vec128_store(got, Hacl_Vec128_shift_right_lanes64(va, n));
    ref_lane_shift(expected, a, -(int)n);
    r |= quiet(what, got, expected);
  }

  Hacl_Vec128_store(got, Hacl_Vec128_bswap(va));
  ref_bswap(expected, a);
  r |= quiet(what, got, expected);
  return r;
}


/* The SHA-256 axioms, against FIPS 180-4 transcribed here from the standard.
 *
 * A register is read as four 32-bit words, lane zero lowest in memory.  The
 * packing the instructions use is ABEF/CDGH, which is not the order the
 * standard writes the state in, so the reference below unpacks explicitly
 * rather than trusting the naming. */

static uint32_t lane(const uint8_t a[16], int i) {
  return (uint32_t)a[4 * i] | ((uint32_t)a[4 * i + 1] << 8) |
         ((uint32_t)a[4 * i + 2] << 16) | ((uint32_t)a[4 * i + 3] << 24);
}

static void setlane(uint8_t a[16], int i, uint32_t v) {
  a[4 * i] = (uint8_t)v;
  a[4 * i + 1] = (uint8_t)(v >> 8);
  a[4 * i + 2] = (uint8_t)(v >> 16);
  a[4 * i + 3] = (uint8_t)(v >> 24);
}

static uint32_t ror(uint32_t x, int n) {
  return (x >> n) | (uint32_t)(x << (32 - n));
}
static uint32_t big_s0(uint32_t x) { return ror(x, 2) ^ ror(x, 13) ^ ror(x, 22); }
static uint32_t big_s1(uint32_t x) { return ror(x, 6) ^ ror(x, 11) ^ ror(x, 25); }
static uint32_t sml_s0(uint32_t x) { return ror(x, 7) ^ ror(x, 18) ^ (x >> 3); }
static uint32_t sml_s1(uint32_t x) { return ror(x, 17) ^ ror(x, 19) ^ (x >> 10); }
static uint32_t ch(uint32_t x, uint32_t y, uint32_t z) {
  return (x & y) ^ (~x & z);
}
static uint32_t maj(uint32_t x, uint32_t y, uint32_t z) {
  return (x & y) ^ (x & z) ^ (y & z);
}

/* One round of the compression function on the eight words a..h. */
static void ref_sha_round(uint32_t s[8], uint32_t wk) {
  uint32_t t1 = s[7] + big_s1(s[4]) + ch(s[4], s[5], s[6]) + wk;
  uint32_t t2 = big_s0(s[0]) + maj(s[0], s[1], s[2]);
  s[7] = s[6]; s[6] = s[5]; s[5] = s[4]; s[4] = s[3] + t1;
  s[3] = s[2]; s[2] = s[1]; s[1] = s[0]; s[0] = t1 + t2;
}

static void ref_rnds2(uint8_t out[16], const uint8_t cdgh[16],
                      const uint8_t abef[16], const uint8_t k[16]) {
  uint32_t s[8];
  s[0] = lane(abef, 3); s[1] = lane(abef, 2);   /* A B */
  s[2] = lane(cdgh, 3); s[3] = lane(cdgh, 2);   /* C D */
  s[4] = lane(abef, 1); s[5] = lane(abef, 0);   /* E F */
  s[6] = lane(cdgh, 1); s[7] = lane(cdgh, 0);   /* G H */
  ref_sha_round(s, lane(k, 0));
  ref_sha_round(s, lane(k, 1));
  setlane(out, 3, s[0]); setlane(out, 2, s[1]);
  setlane(out, 1, s[4]); setlane(out, 0, s[5]);
}

static void ref_msg1(uint8_t out[16], const uint8_t a[16], const uint8_t b[16]) {
  for (int i = 0; i < 4; i++) {
    uint32_t nxt = i < 3 ? lane(a, i + 1) : lane(b, 0);
    setlane(out, i, lane(a, i) + sml_s0(nxt));
  }
}

static void ref_msg2(uint8_t out[16], const uint8_t a[16], const uint8_t b[16]) {
  uint32_t r0 = lane(a, 0) + sml_s1(lane(b, 2));
  uint32_t r1 = lane(a, 1) + sml_s1(lane(b, 3));
  uint32_t r2 = lane(a, 2) + sml_s1(r0);
  uint32_t r3 = lane(a, 3) + sml_s1(r1);
  setlane(out, 0, r0); setlane(out, 1, r1);
  setlane(out, 2, r2); setlane(out, 3, r3);
}

/* The SHA-1 instructions, against FIPS 180-4 section 6.1.2 and the
 * pseudocode of the Intel SDM.  The earliest state and message word is in
 * the high lane. */

static uint32_t rol(uint32_t x, int n) {
  return (uint32_t)(x << n) | (x >> (32 - n));
}

static uint32_t sha1_f(int q, uint32_t b, uint32_t c, uint32_t d) {
  return q == 0 ? ch(b, c, d) : q == 2 ? maj(b, c, d) : b ^ c ^ d;
}

static const uint32_t sha1_k[4] = {0x5a827999u, 0x6ed9eba1u, 0x8f1bbcdcu,
                                   0xca62c1d6u};

/* Four rounds of quarter q with e = 0: the first message word already has
   e added in, which is the instruction's contract. */
static void ref_sha1rnds4(uint8_t out[16], const uint8_t abcd[16],
                          const uint8_t w[16], int q) {
  uint32_t h[5] = {lane(abcd, 3), lane(abcd, 2), lane(abcd, 1), lane(abcd, 0),
                   0};
  for (int i = 0; i < 4; i++) {
    uint32_t t = rol(h[0], 5) + sha1_f(q, h[1], h[2], h[3]) + h[4] +
                 sha1_k[q] + lane(w, 3 - i);
    h[4] = h[3]; h[3] = h[2]; h[2] = rol(h[1], 30); h[1] = h[0]; h[0] = t;
  }
  for (int i = 0; i < 4; i++) setlane(out, 3 - i, h[i]);
}

static void ref_sha1nexte(uint8_t out[16], const uint8_t a[16],
                          const uint8_t b[16]) {
  memcpy(out, b, 16);
  setlane(out, 3, rol(lane(a, 3), 30) + lane(b, 3));
}

static void ref_sha1msg1(uint8_t out[16], const uint8_t a[16],
                         const uint8_t b[16]) {
  setlane(out, 3, lane(a, 1) ^ lane(a, 3));
  setlane(out, 2, lane(a, 0) ^ lane(a, 2));
  setlane(out, 1, lane(b, 3) ^ lane(a, 1));
  setlane(out, 0, lane(b, 2) ^ lane(a, 0));
}

static void ref_sha1msg2(uint8_t out[16], const uint8_t a[16],
                         const uint8_t b[16]) {
  uint32_t w16 = rol(lane(a, 3) ^ lane(b, 2), 1);
  uint32_t w17 = rol(lane(a, 2) ^ lane(b, 1), 1);
  uint32_t w18 = rol(lane(a, 1) ^ lane(b, 0), 1);
  uint32_t w19 = rol(lane(a, 0) ^ w16, 1);
  setlane(out, 3, w16); setlane(out, 2, w17);
  setlane(out, 1, w18); setlane(out, 0, w19);
}

/* Lane permutations, each written as the list of source lanes. */
static void ref_perm(uint8_t out[16], const uint8_t a[16], const uint8_t b[16],
                     const int src[4], const int from_b[4]) {
  for (int i = 0; i < 4; i++)
    setlane(out, i, lane(from_b[i] ? b : a, src[i]));
}

#define TEST_SHA __attribute__((target("ssse3,sse4.1,sha")))

TEST_SHA static int one_sha(const uint8_t a[16], const uint8_t b[16],
                            const char *what) {
  uint8_t got[16], expected[16];
  int r = 0;
  Hacl_Vec128_t va = Hacl_Vec128_load32((uint32_t *)(void *)a);
  Hacl_Vec128_t vb = Hacl_Vec128_load32((uint32_t *)(void *)b);

  Hacl_Vec128_store32((uint32_t *)(void *)got, va);
  r |= quiet(what, got, a);

  Hacl_Vec128_store32((uint32_t *)(void *)got, Hacl_Vec128_add32(va, vb));
  for (int i = 0; i < 4; i++) setlane(expected, i, lane(a, i) + lane(b, i));
  r |= quiet(what, got, expected);

  static const int zero[4] = {0, 0, 0, 0};

#define PERM1(fn, s0, s1, s2, s3)                                            \
  do {                                                                       \
    const int src[4] = {s0, s1, s2, s3};                                     \
    Hacl_Vec128_store32((uint32_t *)(void *)got, fn(va));                    \
    ref_perm(expected, a, b, src, zero);                                     \
    r |= quiet(what, got, expected);                                         \
  } while (0)
  PERM1(Hacl_Vec128_shuffle_swap_pairs, 1, 0, 3, 2);
  PERM1(Hacl_Vec128_shuffle_reverse, 3, 2, 1, 0);
  PERM1(Hacl_Vec128_shuffle_high_pair, 2, 3, 0, 0);
#undef PERM1

#define PERM2(fn, s0, w0, s1, w1, s2, w2, s3, w3)                            \
  do {                                                                       \
    const int src[4] = {s0, s1, s2, s3};                                     \
    const int wb[4] = {w0, w1, w2, w3};                                      \
    Hacl_Vec128_store32((uint32_t *)(void *)got, fn(va, vb));                \
    ref_perm(expected, a, b, src, wb);                                       \
    r |= quiet(what, got, expected);                                         \
  } while (0)
  /* align_right_4(a, b) is one word of a after three of b. */
  PERM2(Hacl_Vec128_align_right_4, 1, 1, 2, 1, 3, 1, 0, 0);
  PERM2(Hacl_Vec128_align_right_8, 2, 1, 3, 1, 0, 0, 1, 0);
  PERM2(Hacl_Vec128_blend_high, 0, 0, 1, 0, 2, 1, 3, 1);
#undef PERM2

  /* bswap32 reverses the bytes within each lane: lane i of the result is
     the big-endian reading of bytes 4i..4i+3 of the input. */
  Hacl_Vec128_store32((uint32_t *)(void *)got, Hacl_Vec128_bswap32(va));
  for (int i = 0; i < 4; i++)
    setlane(expected, i,
            ((uint32_t)a[4 * i] << 24) | ((uint32_t)a[4 * i + 1] << 16) |
                ((uint32_t)a[4 * i + 2] << 8) | (uint32_t)a[4 * i + 3]);
  r |= quiet(what, got, expected);

  /* load_be32 is the load and the shuffle together, which is the only way
     either is used. */
  Hacl_Vec128_store32((uint32_t *)(void *)got,
                      Hacl_Vec128_load_be32((uint8_t *)a));
  r |= quiet(what, got, expected);

  Hacl_Vec128_store32((uint32_t *)(void *)got, Hacl_Vec128_sha256msg1(va, vb));
  ref_msg1(expected, a, b);
  r |= quiet(what, got, expected);

  Hacl_Vec128_store32((uint32_t *)(void *)got, Hacl_Vec128_sha256msg2(va, vb));
  ref_msg2(expected, a, b);
  r |= quiet(what, got, expected);

  /* rnds2 takes three registers; the third is k + w, of which only the low
     two lanes are read, so b serves for both. */
  Hacl_Vec128_store32((uint32_t *)(void *)got,
                      Hacl_Vec128_sha256rnds2(va, vb, vb));
  ref_rnds2(expected, a, b, b);
  r |= quiet(what, got, expected);
  Hacl_Vec128_store32((uint32_t *)(void *)got,
                      Hacl_Vec128_sha256rnds2(vb, va, va));
  ref_rnds2(expected, b, a, a);
  r |= quiet(what, got, expected);

  Hacl_Vec128_store32((uint32_t *)(void *)got, Hacl_Vec128_xor32(va, vb));
  for (int i = 0; i < 4; i++) setlane(expected, i, lane(a, i) ^ lane(b, i));
  r |= quiet(what, got, expected);

  Hacl_Vec128_store32((uint32_t *)(void *)got,
                      Hacl_Vec128_high_lane(lane(b, 1)));
  memset(expected, 0, 16);
  setlane(expected, 3, lane(b, 1));
  r |= quiet(what, got, expected);
  if (Hacl_Vec128_get_high_lane(va) != lane(a, 3)) {
    printf("FAIL %s: get_high_lane\n", what);
    r = 1;
  }

  Hacl_Vec128_store32((uint32_t *)(void *)got, Hacl_Vec128_sha1nexte(va, vb));
  ref_sha1nexte(expected, a, b);
  r |= quiet(what, got, expected);
  Hacl_Vec128_store32((uint32_t *)(void *)got, Hacl_Vec128_sha1msg1(va, vb));
  ref_sha1msg1(expected, a, b);
  r |= quiet(what, got, expected);
  Hacl_Vec128_store32((uint32_t *)(void *)got, Hacl_Vec128_sha1msg2(va, vb));
  ref_sha1msg2(expected, a, b);
  r |= quiet(what, got, expected);

#define RNDS4(q)                                                             \
  do {                                                                       \
    Hacl_Vec128_store32((uint32_t *)(void *)got,                             \
                        Hacl_Vec128_sha1rnds4_##q(va, vb));                  \
    ref_sha1rnds4(expected, a, b, q);                                        \
    r |= quiet(what, got, expected);                                         \
  } while (0)
  RNDS4(0);
  RNDS4(1);
  RNDS4(2);
  RNDS4(3);
#undef RNDS4
  return r;
}

int main(void) {
  if (!Hacl_Vec128_supported()) {
    printf("  skip vec128: no AES instructions on this machine\n");
    return 0;
  }

  int r = 0;
  uint8_t st[16], k[16];

  /* The reduction constant is 0xe1 followed by fifteen zero bytes, which is
     Spec.GF128.r_block in memory order. */
  memset(k, 0, 16);
  k[0] = 0xe1;
  vreduction(st);
  r |= check("vec128 reduction constant", st, k, 16);

  /* And the counter-mode addend is one in lane zero, which little-endian
     puts in byte zero, and zero everywhere else. */
  memset(k, 0, 16);
  k[0] = 1;
  vlane_one(st);
  r |= check("vec128 lane_one constant", st, k, 16);

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


  /* The carry-less multiplier and its neighbours, on edge cases and then on
     pseudo-random input.  A one-bit operand checks the indexing, all-ones
     checks the carry-less part -- the answer has holes an integer multiply
     would not. */
  memset(st, 0, 16);
  memset(k, 0, 16);
  r |= one_clmul(st, k, "vec128 clmul on zeroes");
  memset(st, 0xff, 16);
  memset(k, 0xff, 16);
  r |= one_clmul(st, k, "vec128 clmul on ones");
  for (int bit = 0; bit < 128; bit++) {
    memset(st, 0, 16);
    memset(k, 0, 16);
    st[bit / 8] = (uint8_t)(1u << (bit % 8));
    k[(127 - bit) / 8] = (uint8_t)(1u << ((127 - bit) % 8));
    r |= one_clmul(st, k, "vec128 clmul on single bits");
  }
  for (int i = 0; i < 512; i++) {
    fill(st, 16);
    fill(k, 16);
    r |= one_clmul(st, k, "vec128 clmul on random input");
  }

  if (!Hacl_Vec128_sha_supported()) {
    printf("  skip vec128 SHA: no SHA instructions on this machine\n");
  } else {
    memset(st, 0, 16);
    memset(k, 0, 16);
    r |= one_sha(st, k, "vec128 sha on zeroes");
    memset(st, 0xff, 16);
    memset(k, 0xff, 16);
    r |= one_sha(st, k, "vec128 sha on ones");
    for (int bit = 0; bit < 128; bit++) {
      memset(st, 0, 16);
      memset(k, 0, 16);
      st[bit / 8] = (uint8_t)(1u << (bit % 8));
      k[(127 - bit) / 8] = (uint8_t)(1u << ((127 - bit) % 8));
      r |= one_sha(st, k, "vec128 sha on single bits");
    }
    for (int i = 0; i < 1024; i++) {
      fill(st, 16);
      fill(k, 16);
      r |= one_sha(st, k, "vec128 sha on random input");
    }
  }

  if (r == 0) printf("all vec128 axioms agree with FIPS 197 and with a bitwise reference\n");
  return r;
}

#else

int main(void) {
  printf("  skip vec128: not x86-64\n");
  return 0;
}

#endif
