/* The axioms of lib/Hacl.Carry64.fst, checked against __int128 arithmetic.
 *
 * `addc` is claimed to satisfy s + 2^64 c' == a + b + c with c' a bit, and
 * `subb` to satisfy s - 2^64 c' == a - b - c.  Both are checked on every
 * combination of a handful of edge values and then on pseudo-random words,
 * for both values of the incoming carry.
 */
#include <stdint.h>
#include <stdio.h>

#include "Hacl_Carry64.h"

static uint64_t rnd_state = 0x0123456789abcdefULL;
static uint64_t rnd(void) {
  rnd_state = rnd_state * 6364136223846793005ULL + 1442695040888963407ULL;
  uint64_t x = rnd_state;
  x ^= x >> 29;
  x *= 0xbf58476d1ce4e5b9ULL;
  return x ^ (x >> 32);
}

static int check1(uint64_t c, uint64_t a, uint64_t b) {
  uint64_t s, k;
  unsigned __int128 want = (unsigned __int128)a + b + c;
  k = Hacl_Carry64_addc(c, a, b, &s);
  if (k > 1 || s + ((unsigned __int128)k << 64) != want) {
    printf("  FAIL addc(%llu, %016llx, %016llx)\n", (unsigned long long)c,
           (unsigned long long)a, (unsigned long long)b);
    return 1;
  }
  /* s - 2^64 k == a - b - c, i.e. s == a - b - c + 2^64 k, in Z. */
  k = Hacl_Carry64_subb(c, a, b, &s);
  __int128 lhs = (__int128)s - ((__int128)k << 64);
  __int128 rhs = (__int128)a - (__int128)b - (__int128)c;
  if (k > 1 || lhs != rhs) {
    printf("  FAIL subb(%llu, %016llx, %016llx)\n", (unsigned long long)c,
           (unsigned long long)a, (unsigned long long)b);
    return 1;
  }
  return 0;
}

int main(void) {
  static const uint64_t edge[] = {0, 1, 2, 0x7fffffffffffffffULL,
                                  0x8000000000000000ULL,
                                  0xfffffffffffffffeULL,
                                  0xffffffffffffffffULL};
  const int ne = sizeof edge / sizeof edge[0];
  int r = 0;
  for (int c = 0; c < 2; c++)
    for (int i = 0; i < ne; i++)
      for (int j = 0; j < ne; j++)
        r |= check1(c, edge[i], edge[j]);
  for (int t = 0; t < 1000000; t++)
    r |= check1(t & 1, rnd(), rnd());
  printf(r ? "  FAIL carry64\n" : "  ok   carry64 addc/subb (edge + 1000000 random)\n");
  return r;
}
