/*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*/

/* SHA-1 against FIPS 180-2 appendix A and a few lengths that exercise the
   padding boundaries.

   The interesting cases are the lengths, not the messages: 55 bytes is the
   last one whose padding still fits in the block, 56 the first that needs a
   second block, and 64 a whole block with an entirely separate padding
   block.  Those three are where a hash implementation goes wrong. */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "Hacl.h"

static int failures = 0;

static void check(const char *name, const uint8_t *msg, size_t len,
                  const char *expected_hex) {
  uint8_t got[20];
  char hex[41];
  Hacl_Hash_SHA1_sha1(got, (uint8_t *)msg, len);
  for (size_t i = 0; i < 20; i++)
    sprintf(hex + 2 * i, "%02x", got[i]);
  hex[40] = 0;
  if (strcmp(hex, expected_hex) != 0) {
    printf("  FAIL %s\n    got      %s\n    expected %s\n", name, hex, expected_hex);
    failures++;
  }
}

int main(void) {
  printf("SHA-1\n");

  /* FIPS 180-2 appendix A.1: "abc". */
  check("abc", (const uint8_t *)"abc", 3,
        "a9993e364706816aba3e25717850c26c9cd0d89d");

  /* FIPS 180-2 appendix A.2: the 448-bit two-block message. */
  check("448-bit",
        (const uint8_t *)"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq", 56,
        "84983e441c3bd26ebaae4aa1f95129e5e54670f1");

  /* The empty message: one block that is nothing but padding. */
  check("empty", (const uint8_t *)"", 0,
        "da39a3ee5e6b4b0d3255bfef95601890afd80709");

  /* Padding boundaries, 'a' repeated. */
  {
    uint8_t a[64];
    memset(a, 'a', sizeof a);
    /* 55: the last length whose 0x80 and length field still fit. */
    check("55 x a", a, 55, "c1c8bbdc22796e28c0e15163d20899b65621d65a");
    /* 56: the first length that forces a second padding block. */
    check("56 x a", a, 56, "c2db330f6083854c99d4b5bfb6e8f29f201be699");
    /* 63, 64: a block boundary. */
    check("63 x a", a, 63, "03f09f5b158a7a8cdad920bddc29b81c18a551f5");
    check("64 x a", a, 64, "0098ba824b5c16427bd7a1122a5a442a25ec644d");
  }

  /* FIPS 180-2 appendix A.3: a million 'a's. */
  {
    size_t n = 1000000;
    uint8_t *big = malloc(n);
    if (big == NULL) { printf("  FAIL out of memory\n"); return 1; }
    memset(big, 'a', n);
    check("1e6 x a", big, n, "34aa973cd4c4daa4f61eeb2bdbad27316534016f");
    free(big);
  }

  /* A long message whose every byte differs, so that a schedule bug that
     happens to be symmetric in the block still shows up. */
  {
    size_t n = 1000;
    uint8_t *m = malloc(n);
    if (m == NULL) { printf("  FAIL out of memory\n"); return 1; }
    for (size_t i = 0; i < n; i++)
      m[i] = (uint8_t)((i * 37 + (i >> 3)) & 0xff);
    check("1000 mixed", m, n, "a3b58e6b754fde166bccaf50111b206ac0e365a0");
    free(m);
  }

  if (failures == 0) {
    printf("  all SHA-1 tests passed\n");
    return 0;
  }
  printf("  %d SHA-1 failures\n", failures);
  return 1;
}
