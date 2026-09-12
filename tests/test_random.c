/* The platform entropy shim.
 *
 * There is nothing here that could establish the quality of the operating
 * system's generator, and nothing here tries to: these are the checks that
 * catch a *broken* shim -- one that writes nothing, writes past the end of
 * the buffer, or returns the same bytes twice.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl_Random.h"

#define N 4096

static uint8_t a[N + 2], b[N + 2];

int main(void) {
  int failures = 0;

  /* Guard bytes at both ends of the requested range. */
  memset(a, 0xaa, sizeof a);
  memset(b, 0xaa, sizeof b);

  if (!Hacl_Random_bytes(a + 1, N) || !Hacl_Random_bytes(b + 1, N)) {
    printf("  FAIL random: Hacl_Random_bytes failed\n");
    return 1;
  }
  printf("  ok   random: two calls of %d bytes\n", N);

  if (a[0] != 0xaa || a[N + 1] != 0xaa || b[0] != 0xaa || b[N + 1] != 0xaa) {
    printf("  FAIL random: wrote outside the buffer\n");
    failures++;
  } else {
    printf("  ok   random: stayed inside the buffer\n");
  }

  if (memcmp(a + 1, b + 1, N) == 0) {
    printf("  FAIL random: two calls returned the same bytes\n");
    failures++;
  } else {
    printf("  ok   random: two calls differ\n");
  }

  /* Every byte value should appear in 4096 random bytes; the chance that any
   * one does not is about 1 in 10^7, and that none of the 256 do is about 1
   * in 40000.  A shim that returns a short buffer, a constant, or ASCII
   * fails this; a working one effectively never does. */
  {
    int seen[256] = { 0 }, missing = 0;
    for (int i = 1; i <= N; i++)
      seen[a[i]] = 1;
    for (int i = 0; i < 256; i++)
      missing += !seen[i];
    if (missing > 8) {
      printf("  FAIL random: %d of 256 byte values never occurred\n", missing);
      failures++;
    } else {
      printf("  ok   random: byte values are spread out\n");
    }
  }

  /* A zero-length request must be harmless. */
  if (!Hacl_Random_bytes(a, 0)) {
    printf("  FAIL random: zero-length request failed\n");
    failures++;
  } else {
    printf("  ok   random: zero-length request\n");
  }

  if (failures == 0)
    printf("test_random: all checks passed\n");
  return failures != 0;
}
