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

/* MD5 against RFC 1321 appendix A.5 and the padding boundaries.

   MD5 is little-endian in three separate places -- the sixteen block words,
   the four digest words, and the sixty-four-bit length -- and getting any one
   of them backwards still passes a test on a symmetric message.  The "mixed"
   case at the end is there for that reason, and the 55/56/63/64 lengths are
   there because that is where the padding either does or does not need a
   second block. */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "Hacl.h"

static int failures = 0;

static void check(const char *name, const uint8_t *msg, size_t len,
                  const char *expected_hex) {
  uint8_t got[16];
  char hex[33];
  Hacl_Hash_MD5_md5(got, (uint8_t *)msg, len);
  for (size_t i = 0; i < 16; i++)
    sprintf(hex + 2 * i, "%02x", got[i]);
  hex[32] = 0;
  if (strcmp(hex, expected_hex) != 0) {
    printf("  FAIL %s\n    got      %s\n    expected %s\n", name, hex, expected_hex);
    failures++;
  }
}

int main(void) {
  printf("MD5\n");

  /* RFC 1321 appendix A.5, all seven of them. */
  check("empty", (const uint8_t *)"", 0,
        "d41d8cd98f00b204e9800998ecf8427e");
  check("a", (const uint8_t *)"a", 1,
        "0cc175b9c0f1b6a831c399e269772661");
  check("abc", (const uint8_t *)"abc", 3,
        "900150983cd24fb0d6963f7d28e17f72");
  check("message digest", (const uint8_t *)"message digest", 14,
        "f96b697d7cb7938d525a2f31aaf161d0");
  check("a..z", (const uint8_t *)"abcdefghijklmnopqrstuvwxyz", 26,
        "c3fcd3d76192e4007dfb496cca67e13b");
  check("A..Za..z0..9",
        (const uint8_t *)"ABCDEFGHIJKLMNOPQRSTUVWXYZ"
                         "abcdefghijklmnopqrstuvwxyz0123456789", 62,
        "d174ab98d277d9f5a5611c2c9f419d9f");
  check("8 x 1234567890",
        (const uint8_t *)"1234567890123456789012345678901234567890"
                         "1234567890123456789012345678901234567890", 80,
        "57edf4a22be3c955ac49da2e2107b67a");

  /* Padding boundaries, 'a' repeated. */
  {
    uint8_t a[64];
    memset(a, 'a', sizeof a);
    check("55 x a", a, 55, "ef1772b6dff9a122358552954ad0df65");
    check("56 x a", a, 56, "3b0c8ac703f828b04c6c197006d17218");
    check("63 x a", a, 63, "b06521f39153d618550606be297466d5");
    check("64 x a", a, 64, "014842d480b571495a4a0363793f7367");
  }

  /* A million 'a's: many blocks, and a length that needs more than sixteen
     bits of the length field. */
  {
    size_t n = 1000000;
    uint8_t *big = malloc(n);
    if (big == NULL) { printf("  FAIL out of memory\n"); return 1; }
    memset(big, 'a', n);
    check("1e6 x a", big, n, "7707d6ae4e027c70eea2a935c2296f21");
    free(big);
  }

  /* Every byte different, so a byte-order mistake cannot cancel out. */
  {
    size_t n = 1000;
    uint8_t *m = malloc(n);
    if (m == NULL) { printf("  FAIL out of memory\n"); return 1; }
    for (size_t i = 0; i < n; i++)
      m[i] = (uint8_t)((i * 37 + (i >> 3)) & 0xff);
    check("1000 mixed", m, n, "fa9013b8d0b15a500bdc7bb700266a26");
    free(m);
  }

  if (failures == 0) {
    printf("  all MD5 tests passed\n");
    return 0;
  }
  printf("  %d MD5 failures\n", failures);
  return 1;
}
