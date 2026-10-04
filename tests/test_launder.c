/* The value barrier, and the constant-time table read that depends on it.
 *
 * Two different things are checked here.
 *
 * The first is an axiom.  `Hacl_Launder_u64` is hand-written C realizing the
 * `assume val` in lib/Hacl.Launder.fst, whose postcondition says the result
 * equals the argument; nothing in the F* development checks that the C
 * agrees, so this file does, on a spread of values including the ones most
 * likely to be special-cased.
 *
 * The second is the property the barrier exists for, and it is not a
 * property of a value at all, so it cannot be stated in F*: that
 * `Hacl_Bignum_Base_table_select` takes the same time whichever entry is
 * asked for.  That function reads one of sixteen table entries at an index
 * which, at every call site in the library, is four bits of a secret scalar
 * or exponent.  It is written to touch all sixteen and discard fifteen.
 *
 * Whether the emitted code actually does that is up to the C compiler, and
 * at one point it did not: with the masks computed inline, clang -O3
 * unrolled the loop, recognised the sixteen comparisons of the index against
 * the constants zero through fifteen, and emitted a cascade of branches on
 * the secret.  The lookup's running time then rose monotonically with the
 * index, from 3.7ns at zero to 8.9ns at fifteen -- a 158% spread, which is
 * the entire four-bit digit observable from outside.  Laundering each mask
 * takes that spread to about 2%.
 *
 * So the test below times the real shipped function once per index and fails
 * if the spread is large.  The threshold is deliberately loose.  A timing
 * test cannot be made perfectly reliable on a shared machine, but the two
 * regimes it is distinguishing are two orders of magnitude apart, and the
 * measurement takes the minimum over repetitions, which noise can only push
 * upwards.
 */
/* clock_gettime; _DEFAULT_SOURCE first, or karamel's endianness header
 * loses le64toh under a bare _POSIX_C_SOURCE. */
#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 199309L

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "Hacl.h"
#include "Hacl_Launder.h"

#define NLIMB 5
#define NENTRY 16

static double now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

/* The barrier is the identity. */
static int test_identity(void) {
  static const uint64_t vs[] = {
      0u,
      1u,
      2u,
      0xffffffffffffffffu,
      0xfffffffffffffffeu,
      0x8000000000000000u,
      0x7fffffffffffffffu,
      0x0123456789abcdefu,
      0xdeadbeefcafebabeu,
  };
  int bad = 0;
  for (size_t i = 0; i < sizeof(vs) / sizeof(vs[0]); i++) {
    uint64_t got = Hacl_Launder_u64(vs[i]);
    if (got != vs[i]) {
      printf("  FAIL launder identity at %016" PRIx64 " -> %016" PRIx64 "\n",
             vs[i], got);
      bad = 1;
    }
  }
  /* And over a wider sweep, so a barrier that mangled some bit pattern
   * could not slip through the list above. */
  uint64_t x = 0x9e3779b97f4a7c15u;
  for (int i = 0; i < 100000; i++) {
    if (Hacl_Launder_u64(x) != x) {
      printf("  FAIL launder identity at %016" PRIx64 "\n", x);
      bad = 1;
      break;
    }
    x = x * 6364136223846793005u + 1442695040888963407u;
  }
  if (!bad)
    printf("  ok   launder is the identity\n");
  return bad;
}

/* The table read returns the entry it was asked for. */
static int test_select_value(uint64_t *tbl) {
  int bad = 0;
  uint64_t res[NLIMB];
  for (uint64_t d = 0; d < NENTRY; d++) {
    memset(res, 0, sizeof(res));
    Hacl_Bignum_Base_table_select(res, tbl, NLIMB, d);
    if (memcmp(res, tbl + d * NLIMB, sizeof(res)) != 0) {
      printf("  FAIL table_select entry %" PRIu64 "\n", d);
      bad = 1;
    }
  }
  if (!bad)
    printf("  ok   table_select reads the right entry\n");
  return bad;
}

/* The table read takes the same time whichever entry it was asked for. */
static int test_select_timing(uint64_t *tbl) {
  enum { REPS = 7, ITERS = 200000 };
  double best[NENTRY];
  uint64_t res[NLIMB];
  uint64_t sink = 0;

  for (int rep = 0; rep < REPS; rep++) {
    for (uint64_t d = 0; d < NENTRY; d++) {
      Hacl_Bignum_Base_table_select(res, tbl, NLIMB, d);
      double t0 = now_ns();
      for (int i = 0; i < ITERS; i++) {
        Hacl_Bignum_Base_table_select(res, tbl, NLIMB, d);
        sink ^= res[0];
      }
      double per = (now_ns() - t0) / (double)ITERS;
      if (rep == 0 || per < best[d])
        best[d] = per;
    }
  }

  double lo = best[0], hi = best[0];
  for (int d = 0; d < NENTRY; d++) {
    if (best[d] < lo)
      lo = best[d];
    if (best[d] > hi)
      hi = best[d];
  }
  double spread = (lo > 0.0) ? 100.0 * (hi - lo) / lo : 0.0;

  /* 158% when the barrier was missing, about 2% with it.  Anything under
   * this is noise; anything over it is the compiler having turned the mask
   * arithmetic back into a branch. */
  const double limit = 75.0;
  if (spread > limit) {
    printf("  FAIL table_select timing depends on the index\n");
    for (int d = 0; d < NENTRY; d++)
      printf("         d=%2d  %6.2f ns\n", d, best[d]);
    printf("         spread %.1f%% (limit %.1f%%)\n", spread, limit);
    return 1;
  }
  printf("  ok   table_select timing is flat (spread %.1f%%, limit %.1f%%)\n",
         spread, limit);
  if (sink == 0x5ca1ab1eu)
    printf("  (unreachable; keeps the loop from being elided)\n");
  return 0;
}

int main(void) {
  uint64_t tbl[NENTRY * NLIMB];
  for (size_t i = 0; i < NENTRY * NLIMB; i++)
    tbl[i] = i * 0x9e3779b97f4a7c15u + 0x0123456789abcdefu;

  int bad = 0;
  bad |= test_identity();
  bad |= test_select_value(tbl);
  bad |= test_select_timing(tbl);

  if (bad) {
    printf("launder: failure(s)\n");
    return 1;
  }
  printf("all launder checks pass\n");
  return 0;
}
