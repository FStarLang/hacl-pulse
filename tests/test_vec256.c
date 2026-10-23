/* The axioms of lib/Hacl.Vec256.fst, checked against plain C.
 *
 * Every `assume val` in that module is a claim about an AVX2 instruction that
 * F* cannot check.  This test checks each of them, on edge cases and then on
 * pseudo-random inputs, against a scalar transcription of the axiom as
 * written there: lane i is bytes 4i .. 4i+3 little-endian, `add32` adds
 * modulo 2^32 lane by lane, a sixty-four-bit lane is two of those, low first, the unpacks and the 128-bit permutes take the
 * lanes the axiom lists.  Every rotation distance from 1 to 31 is tried,
 * not just the four ChaCha20 uses, because the axiom quantifies over all of
 * them.
 *
 * It is skipped, not failed, on a machine without AVX2.  The other half of
 * the evidence is tests/test_chacha20.c, tests/test_chacha20_vec.c,
 * tests/test_poly1305.c and tests/test_poly1305_vec.c, whose long messages go
 * through Hacl.Chacha20.Vec256 and Hacl.Poly1305.Vec256 on any machine with
 * AVX2.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl_Vec256.h"

#if defined(__x86_64__)

static int failures = 0;

static uint64_t prng = 0x9e3779b97f4a7c15ULL;

static uint32_t next32(void) {
  prng ^= prng << 13;
  prng ^= prng >> 7;
  prng ^= prng << 17;
  return (uint32_t)(prng >> 16);
}

static void fill(uint8_t *p, size_t n) {
  for (size_t i = 0; i < n; i++) p[i] = (uint8_t)next32();
}

static uint32_t lane(const uint8_t b[32], int i) {
  return (uint32_t)b[4 * i] | (uint32_t)b[4 * i + 1] << 8 |
         (uint32_t)b[4 * i + 2] << 16 | (uint32_t)b[4 * i + 3] << 24;
}

static uint64_t lane64(const uint8_t b[32], int i) {
  return (uint64_t)lane(b, 2 * i) | (uint64_t)lane(b, 2 * i + 1) << 32;
}

static uint32_t rotl32(uint32_t x, unsigned s) {
  return (x << s) | (x >> (32 - s));
}

static void report(const char *name, bool ok) {
  if (ok) {
    printf("  ok   %s\n", name);
  } else {
    printf("  FAIL %s\n", name);
    failures++;
  }
}


#define AVX2 __attribute__((target("avx2")))

/* The lanes each permutation axiom names, as indices into a ++ b: 0..7 are
   lanes of a, 8..15 lanes of b. */
static const int perm_lanes[6][8] = {
    {0, 8, 1, 9, 4, 12, 5, 13},       /* unpacklo32 */
    {2, 10, 3, 11, 6, 14, 7, 15},     /* unpackhi32 */
    {0, 1, 8, 9, 4, 5, 12, 13},       /* unpacklo64 */
    {2, 3, 10, 11, 6, 7, 14, 15},     /* unpackhi64 */
    {0, 1, 2, 3, 8, 9, 10, 11},       /* lo128 */
    {4, 5, 6, 7, 12, 13, 14, 15},     /* hi128 */
};

static const char *perm_names[6] = {"unpacklo32", "unpackhi32", "unpacklo64",
                                    "unpackhi64", "lo128",      "hi128"};

AVX2 static Hacl_Vec256_t perm(int k, Hacl_Vec256_t a, Hacl_Vec256_t b) {
  switch (k) {
  case 0: return Hacl_Vec256_unpacklo32(a, b);
  case 1: return Hacl_Vec256_unpackhi32(a, b);
  case 2: return Hacl_Vec256_unpacklo64(a, b);
  case 3: return Hacl_Vec256_unpackhi64(a, b);
  case 4: return Hacl_Vec256_lo128(a, b);
  default: return Hacl_Vec256_hi128(a, b);
  }
}

/* rotl is always_inline and each call site in the library passes a literal;
   a switch gives every distance its own literal call. */
AVX2 static Hacl_Vec256_t rotl_by(Hacl_Vec256_t a, unsigned s) {
  switch (s) {
#define R(n) case n: return Hacl_Vec256_rotl(a, n);
  R(1) R(2) R(3) R(4) R(5) R(6) R(7) R(8) R(9) R(10) R(11) R(12) R(13) R(14)
  R(15) R(16) R(17) R(18) R(19) R(20) R(21) R(22) R(23) R(24) R(25) R(26)
  R(27) R(28) R(29) R(30) R(31)
#undef R
  default: return a;
  }
}

AVX2 static void run(int rounds) {
  uint8_t a[32], b[32], r[32], buf[40];
  bool ok;

  /* load/store: bytes in memory order, at every misalignment. */
  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(buf, sizeof buf);
    for (int off = 0; off <= 8; off++) {
      uint8_t back[40];
      memset(back, 0xa5, sizeof back);
      Hacl_Vec256_store(back + off, Hacl_Vec256_load(buf + off));
      ok &= memcmp(back + off, buf + off, 32) == 0;
      for (int i = 0; i < off; i++) ok &= back[i] == 0xa5;
      for (int i = off + 32; i < 40; i++) ok &= back[i] == 0xa5;
    }
  }
  report("vec256 load/store", ok);

  Hacl_Vec256_store(r, Hacl_Vec256_zero());
  ok = true;
  for (int i = 0; i < 32; i++) ok &= r[i] == 0;
  report("vec256 zero", ok);

  Hacl_Vec256_store(r, Hacl_Vec256_iota());
  ok = true;
  for (int i = 0; i < 8; i++) ok &= lane(r, i) == (uint32_t)i;
  report("vec256 iota", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    uint32_t x = n == 0 ? 0 : n == 1 ? 0xffffffffu : next32();
    Hacl_Vec256_store(r, Hacl_Vec256_bcast(x));
    for (int i = 0; i < 8; i++) ok &= lane(r, i) == x;
  }
  report("vec256 bcast", ok);

  /* add32 carries must stop at lane boundaries. */
  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    fill(b, 32);
    if (n == 0) {
      memset(a, 0xff, 32);
      memset(b, 0, 32);
      b[0] = 1;
      b[16] = 1;
    }
    Hacl_Vec256_store(r, Hacl_Vec256_add32(Hacl_Vec256_load(a),
                                           Hacl_Vec256_load(b)));
    for (int i = 0; i < 8; i++) ok &= lane(r, i) == lane(a, i) + lane(b, i);
  }
  report("vec256 add32", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    fill(b, 32);
    Hacl_Vec256_store(r, Hacl_Vec256_xor(Hacl_Vec256_load(a),
                                         Hacl_Vec256_load(b)));
    for (int i = 0; i < 32; i++) ok &= r[i] == (uint8_t)(a[i] ^ b[i]);
  }
  report("vec256 xor", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    if (n == 0) memset(a, 0x80, 32);
    for (unsigned s = 1; s < 32; s++) {
      Hacl_Vec256_store(r, rotl_by(Hacl_Vec256_load(a), s));
      for (int i = 0; i < 8; i++) ok &= lane(r, i) == rotl32(lane(a, i), s);
    }
  }
  report("vec256 rotl, every distance", ok);

  for (int k = 0; k < 6; k++) {
    char name[64];
    ok = true;
    for (int n = 0; n < rounds; n++) {
      fill(a, 32);
      fill(b, 32);
      Hacl_Vec256_store(r, perm(k, Hacl_Vec256_load(a), Hacl_Vec256_load(b)));
      for (int i = 0; i < 8; i++) {
        int src = perm_lanes[k][i];
        uint32_t want = src < 8 ? lane(a, src) : lane(b, src - 8);
        ok &= lane(r, i) == want;
      }
    }
    snprintf(name, sizeof name, "vec256 %s", perm_names[k]);
    report(name, ok);
  }

  /* The sixty-four-bit lanes: lane i is lanes 2i and 2i+1, low first. */
  uint64_t w[4];
  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    fill(b, 32);
    if (n == 0) memset(a, 0xff, 32);
    Hacl_Vec256_store(r, Hacl_Vec256_add64(Hacl_Vec256_load(a),
                                           Hacl_Vec256_load(b)));
    for (int i = 0; i < 4; i++) ok &= lane64(r, i) == lane64(a, i) + lane64(b, i);
  }
  report("vec256 add64", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    fill(b, 32);
    if (n == 0) { memset(a, 0xff, 32); memset(b, 0xff, 32); }
    Hacl_Vec256_store(r, Hacl_Vec256_mul32(Hacl_Vec256_load(a),
                                           Hacl_Vec256_load(b)));
    for (int i = 0; i < 4; i++)
      ok &= lane64(r, i) == (uint64_t)(uint32_t)lane64(a, i) * (uint32_t)lane64(b, i);
  }
  report("vec256 mul32", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    if (n == 0) memset(a, 0xff, 32);
    for (unsigned s = 1; s < 64; s++) {
      Hacl_Vec256_store(r, Hacl_Vec256_shr64(Hacl_Vec256_load(a), s));
      for (int i = 0; i < 4; i++) ok &= lane64(r, i) == lane64(a, i) >> s;
      Hacl_Vec256_store(r, Hacl_Vec256_shl64(Hacl_Vec256_load(a), s));
      for (int i = 0; i < 4; i++) ok &= lane64(r, i) == lane64(a, i) << s;
    }
  }
  report("vec256 shr64 and shl64, every distance", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    if (n == 0) memset(a, 0xff, 32);
    Hacl_Vec256_store(r, Hacl_Vec256_mask26(Hacl_Vec256_load(a)));
    for (int i = 0; i < 4; i++) ok &= lane64(r, i) == (lane64(a, i) & 0x3ffffff);
  }
  report("vec256 mask26", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    uint64_t x[4];
    for (int i = 0; i < 4; i++) x[i] = lane64(a, i);
    Hacl_Vec256_store(r, Hacl_Vec256_bcast64(x[0]));
    for (int i = 0; i < 4; i++) ok &= lane64(r, i) == x[0];
    Hacl_Vec256_store(r, Hacl_Vec256_set64(x[0], x[1], x[2], x[3]));
    for (int i = 0; i < 4; i++) ok &= lane64(r, i) == x[i];
    Hacl_Vec256_store64(w, Hacl_Vec256_load(a));
    for (int i = 0; i < 4; i++) ok &= w[i] == x[i];
  }
  report("vec256 bcast64, set64 and store64", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    fill(b, 32);
    if (n == 0) { memset(a, 0xff, 32); memset(b, 0x5a, 32); }
    Hacl_Vec256_store(r, Hacl_Vec256_xor64(Hacl_Vec256_load(a), Hacl_Vec256_load(b)));
    for (int i = 0; i < 4; i++) ok &= lane64(r, i) == (lane64(a, i) ^ lane64(b, i));
    Hacl_Vec256_store(r, Hacl_Vec256_andnot64(Hacl_Vec256_load(a), Hacl_Vec256_load(b)));
    for (int i = 0; i < 4; i++) ok &= lane64(r, i) == (~lane64(a, i) & lane64(b, i));
  }
  report("vec256 xor64 and andnot64", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    if (n == 0) memset(a, 0xff, 32);
    for (unsigned s = 1; s < 64; s++) {
      Hacl_Vec256_store(r, Hacl_Vec256_rotl64(Hacl_Vec256_load(a), s));
      for (int i = 0; i < 4; i++)
        ok &= lane64(r, i) == ((lane64(a, i) << s) | (lane64(a, i) >> (64 - s)));
    }
  }
  report("vec256 rotl64, every distance", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    for (unsigned s = 1; s < 64; s++) {
      Hacl_Vec256_store(r, Hacl_Vec256_rotr64(Hacl_Vec256_load(a), s));
      for (int i = 0; i < 4; i++)
        ok &= lane64(r, i) == ((lane64(a, i) >> s) | (lane64(a, i) << (64 - s)));
    }
  }
  report("vec256 rotr64, every distance", ok);

  /* The SHA-512 schedule's lane moves. */
  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    fill(b, 32);
    Hacl_Vec256_t va = Hacl_Vec256_load(a), vb = Hacl_Vec256_load(b);
    Hacl_Vec256_store(r, Hacl_Vec256_window64(va, vb));
    for (int i = 0; i < 3; i++) ok &= lane64(r, i) == lane64(a, i + 1);
    ok &= lane64(r, 3) == lane64(b, 0);
    Hacl_Vec256_store(r, Hacl_Vec256_hi_to_lo64(va));
    ok &= lane64(r, 0) == lane64(a, 2) && lane64(r, 1) == lane64(a, 3) &&
          lane64(r, 2) == 0 && lane64(r, 3) == 0;
    Hacl_Vec256_store(r, Hacl_Vec256_lo_to_hi64(va));
    ok &= lane64(r, 2) == lane64(a, 0) && lane64(r, 3) == lane64(a, 1) &&
          lane64(r, 0) == 0 && lane64(r, 1) == 0;
    Hacl_Vec256_store(r, Hacl_Vec256_blend_lohi64(va, vb));
    ok &= lane64(r, 0) == lane64(a, 0) && lane64(r, 1) == lane64(a, 1) &&
          lane64(r, 2) == lane64(b, 2) && lane64(r, 3) == lane64(b, 3);
  }
  report("vec256 window64, hi_to_lo64, lo_to_hi64 and blend_lohi64", ok);

  uint64_t qbuf[12], qout[12];
  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill((uint8_t *)qbuf, sizeof qbuf);
    size_t at = (size_t)(next32() % 9);
    memcpy(qout, qbuf, sizeof qout);
    Hacl_Vec256_store(r, Hacl_Vec256_load64(qbuf, at));
    for (int i = 0; i < 4; i++) ok &= lane64(r, i) == qbuf[at + i];
    fill(a, 32);
    Hacl_Vec256_store64_at(qout, at, Hacl_Vec256_load(a));
    for (size_t k = 0; k < 12; k++)
      ok &= qout[k] == (at <= k && k < at + 4 ? lane64(a, (int)(k - at)) : qbuf[k]);
  }
  report("vec256 load64 and store64_at", ok);

  /* Hacl.Vec256.Lane32. */
  uint32_t wbuf[24], wout[24];
  ok = true;
  for (int n = 0; n < rounds; n++) {
    for (int i = 0; i < 24; i++) wbuf[i] = next32();
    size_t at = (size_t)(next32() % 17);
    memcpy(wout, wbuf, sizeof wout);
    Hacl_Vec256_store(r, Hacl_Vec256_load32(wbuf, at));
    for (int i = 0; i < 8; i++) ok &= lane(r, i) == wbuf[at + i];
    fill(a, 32);
    Hacl_Vec256_store32(wout, at, Hacl_Vec256_load(a));
    for (size_t k = 0; k < 24; k++)
      ok &= wout[k] == (at <= k && k < at + 8 ? lane(a, (int)(k - at)) : wbuf[k]);
  }
  report("vec256 load32 and store32", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    fill(b, 32);
    if (n == 0) { memset(a, 0xff, 32); memset(b, 0xff, 32); }
    if (n == 1) { memset(a, 0, 32); memset(b, 0xff, 32); }
    Hacl_Vec256_t x = Hacl_Vec256_load(a), y = Hacl_Vec256_load(b);
    uint8_t s[32], lo[32], hi[32], m[32];
    Hacl_Vec256_store(s, Hacl_Vec256_sub32(x, y));
    Hacl_Vec256_store(lo, Hacl_Vec256_mullo32(x, y));
    Hacl_Vec256_store(hi, Hacl_Vec256_mulhi32(x, y));
    Hacl_Vec256_store(m, Hacl_Vec256_minu32(x, y));
    for (int i = 0; i < 8; i++) {
      uint64_t p = (uint64_t)lane(a, i) * lane(b, i);
      ok &= lane(s, i) == lane(a, i) - lane(b, i);
      ok &= lane(lo, i) == (uint32_t)p;
      ok &= lane(hi, i) == (uint32_t)(p >> 32);
      ok &= lane(m, i) == (lane(a, i) <= lane(b, i) ? lane(a, i) : lane(b, i));
    }
  }
  report("vec256 sub32, mullo32, mulhi32 and minu32", ok);

  /* The index vectors the ML-DSA transforms use, and some others. */
  static const uint32_t perms[][8] = {
      {0, 0, 0, 0, 1, 1, 1, 1}, {0, 0, 2, 2, 1, 1, 3, 3},
      {0, 1, 4, 5, 2, 3, 6, 7}, {1, 1, 1, 1, 0, 0, 0, 0},
      {3, 3, 1, 1, 2, 2, 0, 0}, {7, 6, 3, 2, 5, 4, 1, 0},
      {0, 1, 2, 3, 4, 5, 6, 7}, {7, 7, 7, 7, 7, 7, 7, 7}};
  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 32);
    for (size_t k = 0; k < sizeof perms / sizeof perms[0]; k++) {
      const uint32_t *p = perms[k];
      Hacl_Vec256_store(r, Hacl_Vec256_perm32(Hacl_Vec256_load(a), p[0], p[1],
                                              p[2], p[3], p[4], p[5], p[6],
                                              p[7]));
      for (int i = 0; i < 8; i++) ok &= lane(r, i) == lane(a, (int)p[i]);
    }
  }
  report("vec256 perm32", ok);
}


int main(void) {
  if (!Hacl_Vec256_supported()) {
    printf("  skip vec256: no AVX2 on this machine\n");
    return 0;
  }
  run(1000);
  if (failures) {
    printf("%d vec256 check(s) failed\n", failures);
    return 1;
  }
  printf("all vec256 axioms agree with a scalar transcription\n");
  return 0;
}

#else

int main(void) {
  printf("  skip vec256: not x86-64\n");
  return 0;
}

#endif
