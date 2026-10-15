/* The axioms of lib/Hacl.Vec512.fst, checked against plain C.
 *
 * Every `assume val` in that module is a claim about an AVX-512F instruction
 * that F* cannot check.  This test checks each of them, on edge cases and
 * then on pseudo-random inputs, against a scalar transcription of the axiom
 * as written there: lane i is bytes 4i .. 4i+3 little-endian, `add32` adds
 * modulo 2^32 lane by lane, and the unpacks and group selections take the
 * lanes the axiom lists.  Every rotation distance from 1 to 31 is tried.
 *
 * It is skipped, not failed, on a machine without AVX-512F.  The other half
 * of the evidence is tests/test_chacha20.c and tests/test_chacha20_vec.c,
 * whose long messages go through Hacl.Chacha20.Vec512 on such a machine.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl_Vec512.h"

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

static uint32_t lane(const uint8_t b[64], int i) {
  return (uint32_t)b[4 * i] | (uint32_t)b[4 * i + 1] << 8 |
         (uint32_t)b[4 * i + 2] << 16 | (uint32_t)b[4 * i + 3] << 24;
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

#if defined(__x86_64__) || defined(__i386__)

#define AVX512 __attribute__((target("avx512f")))

/* The lanes each permutation axiom names, as indices into a ++ b: 0..15 are
   lanes of a, 16..31 lanes of b. */
static const int perm_lanes[8][16] = {
    {0, 16, 1, 17, 4, 20, 5, 21, 8, 24, 9, 25, 12, 28, 13, 29}, /* unpacklo32 */
    {2, 18, 3, 19, 6, 22, 7, 23, 10, 26, 11, 27, 14, 30, 15, 31}, /* unpackhi32 */
    {0, 1, 16, 17, 4, 5, 20, 21, 8, 9, 24, 25, 12, 13, 28, 29}, /* unpacklo64 */
    {2, 3, 18, 19, 6, 7, 22, 23, 10, 11, 26, 27, 14, 15, 30, 31}, /* unpackhi64 */
    {0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23}, /* sel_lo */
    {8, 9, 10, 11, 12, 13, 14, 15, 24, 25, 26, 27, 28, 29, 30, 31}, /* sel_hi */
    {0, 1, 2, 3, 8, 9, 10, 11, 16, 17, 18, 19, 24, 25, 26, 27}, /* sel_even */
    {4, 5, 6, 7, 12, 13, 14, 15, 20, 21, 22, 23, 28, 29, 30, 31}, /* sel_odd */
};

static const char *perm_names[8] = {"unpacklo32", "unpackhi32", "unpacklo64", "unpackhi64", "sel_lo", "sel_hi", "sel_even", "sel_odd"};

AVX512 static Hacl_Vec512_t perm(int k, Hacl_Vec512_t a, Hacl_Vec512_t b) {
  switch (k) {
  case 0: return Hacl_Vec512_unpacklo32(a, b);
  case 1: return Hacl_Vec512_unpackhi32(a, b);
  case 2: return Hacl_Vec512_unpacklo64(a, b);
  case 3: return Hacl_Vec512_unpackhi64(a, b);
  case 4: return Hacl_Vec512_sel_lo(a, b);
  case 5: return Hacl_Vec512_sel_hi(a, b);
  case 6: return Hacl_Vec512_sel_even(a, b);
  default: return Hacl_Vec512_sel_odd(a, b);
  }
}

/* rotl is always_inline and each call site in the library passes a literal;
   a switch gives every distance its own literal call. */
AVX512 static Hacl_Vec512_t rotl_by(Hacl_Vec512_t a, unsigned s) {
  switch (s) {
#define R(n) case n: return Hacl_Vec512_rotl(a, n);
  R(1) R(2) R(3) R(4) R(5) R(6) R(7) R(8) R(9) R(10) R(11) R(12) R(13) R(14)
  R(15) R(16) R(17) R(18) R(19) R(20) R(21) R(22) R(23) R(24) R(25) R(26)
  R(27) R(28) R(29) R(30) R(31)
#undef R
  default: return a;
  }
}

/* The same, but with a distance the compiler cannot see, to exercise the
   variable-count fallback. */
AVX512 __attribute__((noinline)) static Hacl_Vec512_t
rotl_var(Hacl_Vec512_t a, volatile unsigned *s) {
  return Hacl_Vec512_rotl(a, *s);
}

AVX512 static void run(int rounds) {
  uint8_t a[64], b[64], r[64], buf[80];
  bool ok;

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(buf, sizeof buf);
    for (int off = 0; off <= 16; off++) {
      uint8_t back[80];
      memset(back, 0xa5, sizeof back);
      Hacl_Vec512_store(back + off, Hacl_Vec512_load(buf + off));
      ok &= memcmp(back + off, buf + off, 64) == 0;
      for (int i = 0; i < off; i++) ok &= back[i] == 0xa5;
      for (int i = off + 64; i < 80; i++) ok &= back[i] == 0xa5;
    }
  }
  report("vec512 load/store", ok);

  Hacl_Vec512_store(r, Hacl_Vec512_zero());
  ok = true;
  for (int i = 0; i < 64; i++) ok &= r[i] == 0;
  report("vec512 zero", ok);

  Hacl_Vec512_store(r, Hacl_Vec512_iota());
  ok = true;
  for (int i = 0; i < 16; i++) ok &= lane(r, i) == (uint32_t)i;
  report("vec512 iota", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    uint32_t x = n == 0 ? 0 : n == 1 ? 0xffffffffu : next32();
    Hacl_Vec512_store(r, Hacl_Vec512_bcast(x));
    for (int i = 0; i < 16; i++) ok &= lane(r, i) == x;
  }
  report("vec512 bcast", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 64);
    fill(b, 64);
    if (n == 0) {
      memset(a, 0xff, 64);
      memset(b, 0, 64);
      for (int i = 0; i < 64; i += 4) b[i] = 1;
    }
    Hacl_Vec512_store(r, Hacl_Vec512_add32(Hacl_Vec512_load(a),
                                           Hacl_Vec512_load(b)));
    for (int i = 0; i < 16; i++) ok &= lane(r, i) == lane(a, i) + lane(b, i);
  }
  report("vec512 add32", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 64);
    fill(b, 64);
    Hacl_Vec512_store(r, Hacl_Vec512_xor(Hacl_Vec512_load(a),
                                         Hacl_Vec512_load(b)));
    for (int i = 0; i < 64; i++) ok &= r[i] == (uint8_t)(a[i] ^ b[i]);
  }
  report("vec512 xor", ok);

  ok = true;
  for (int n = 0; n < rounds; n++) {
    fill(a, 64);
    if (n == 0) memset(a, 0x80, 64);
    for (unsigned s = 1; s < 32; s++) {
      volatile unsigned vs = s;
      Hacl_Vec512_store(r, rotl_by(Hacl_Vec512_load(a), s));
      for (int i = 0; i < 16; i++) ok &= lane(r, i) == rotl32(lane(a, i), s);
      Hacl_Vec512_store(r, rotl_var(Hacl_Vec512_load(a), &vs));
      for (int i = 0; i < 16; i++) ok &= lane(r, i) == rotl32(lane(a, i), s);
    }
  }
  report("vec512 rotl, every distance", ok);

  for (int k = 0; k < 8; k++) {
    char name[64];
    ok = true;
    for (int n = 0; n < rounds; n++) {
      fill(a, 64);
      fill(b, 64);
      Hacl_Vec512_store(r, perm(k, Hacl_Vec512_load(a), Hacl_Vec512_load(b)));
      for (int i = 0; i < 16; i++) {
        int src = perm_lanes[k][i];
        uint32_t want = src < 16 ? lane(a, src) : lane(b, src - 16);
        ok &= lane(r, i) == want;
      }
    }
    snprintf(name, sizeof name, "vec512 %s", perm_names[k]);
    report(name, ok);
  }
}

#endif

int main(void) {
  if (!Hacl_Vec512_supported()) {
    printf("  skip vec512: no AVX-512F on this machine\n");
    return 0;
  }
#if defined(__x86_64__) || defined(__i386__)
  run(1000);
#endif
  if (failures) {
    printf("%d vec512 check(s) failed\n", failures);
    return 1;
  }
  printf("all vec512 axioms agree with a scalar transcription\n");
  return 0;
}
