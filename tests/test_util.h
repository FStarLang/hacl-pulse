/* Shared helpers for the C test suite.
 *
 * Everything here is static: the tests are separate translation units linked
 * into one binary, and a header-only helper keeps them independent. */

#ifndef HACL_TEST_UTIL_H
#define HACL_TEST_UTIL_H

#include <stdint.h>
#include <stdio.h>
#include <string.h>

static void print_hex(const uint8_t *src, size_t n) {
  for (size_t i = 0; i < n; i++)
    printf("%02x", src[i]);
}

/* Returns nonzero on mismatch, so a caller can accumulate with |=. */
static int check(const char *name, const uint8_t *got, const uint8_t *expected,
                 size_t n) {
  if (memcmp(got, expected, n) != 0) {
    printf("  FAIL %s\n    got      ", name);
    print_hex(got, n);
    printf("\n    expected ");
    print_hex(expected, n);
    printf("\n");
    return 1;
  }
  printf("  ok   %s\n", name);
  return 0;
}

#endif
