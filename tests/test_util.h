/* Shared helpers for the C test suite.
 *
 * Everything here is static: the tests are separate translation units linked
 * into one binary, and a header-only helper keeps them independent. */

#ifndef HACL_TEST_UTIL_H
#define HACL_TEST_UTIL_H

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static void hex_of(char *dst, const uint8_t *src, size_t n) {
  static const char digits[] = "0123456789abcdef";
  for (size_t i = 0; i < n; i++) {
    dst[2 * i] = digits[src[i] >> 4];
    dst[2 * i + 1] = digits[src[i] & 0xf];
  }
  dst[2 * n] = '\0';
}

/* Returns nonzero on mismatch, so a caller can accumulate with |=. */
static int check(const char *name, const uint8_t *got, const uint8_t *expected,
                 size_t n) {
  if (memcmp(got, expected, n) != 0) {
    char g[131], e[131];
    hex_of(g, got, n);
    hex_of(e, expected, n);
    printf("  FAIL %s\n    got      %s\n    expected %s\n", name, g, e);
    return 1;
  }
  printf("  ok   %s\n", name);
  return 0;
}

#endif
