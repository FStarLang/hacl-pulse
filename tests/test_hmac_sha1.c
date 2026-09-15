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

/* HMAC-SHA1 against RFC 2202.

   The key length is where HMAC implementations go wrong, so the vectors span
   all three cases: shorter than a block, exactly a block, and longer than a
   block (where the key is hashed first).  The last two are RFC 2202's cases 6
   and 7; the exact-block case is not in the RFC, so it is computed here and
   included because it is the boundary of the branch. */

#include <stdio.h>
#include <string.h>

#include "Hacl.h"

static int failures = 0;

static void check(const char *name, const uint8_t *key, size_t key_len,
                  const uint8_t *msg, size_t msg_len, const char *expected) {
  uint8_t out[20];
  char got[41];
  Hacl_HMAC_SHA1_hmac_sha1(out, (uint8_t *)key, key_len, (uint8_t *)msg, msg_len);
  for (size_t i = 0; i < 20; i++) sprintf(got + 2 * i, "%02x", out[i]);
  got[40] = 0;
  if (strcmp(got, expected) != 0) {
    printf("  FAIL %s\n    got      %s\n    expected %s\n", name, got, expected);
    failures++;
  }
}

int main(void) {
  printf("HMAC-SHA1\n");

  uint8_t k[80], d[80];

  /* RFC 2202 case 1. */
  memset(k, 0x0b, 20);
  check("rfc2202-1", k, 20, (const uint8_t *)"Hi There", 8,
        "b617318655057264e28bc0b6fb378c8ef146be00");

  /* RFC 2202 case 2: a key shorter than the digest. */
  check("rfc2202-2", (const uint8_t *)"Jefe", 4,
        (const uint8_t *)"what do ya want for nothing?", 28,
        "effcdf6ae5eb2fa2d27416d5f184df9c259a7c79");

  /* RFC 2202 case 3. */
  memset(k, 0xaa, 20);
  memset(d, 0xdd, 50);
  check("rfc2202-3", k, 20, d, 50, "125d7342b9ac11cd91a39af48aa17b4f63f175d3");

  /* RFC 2202 case 4. */
  for (int i = 0; i < 25; i++) k[i] = (uint8_t)(i + 1);
  memset(d, 0xcd, 50);
  check("rfc2202-4", k, 25, d, 50, "4c9007f4026250c6bc8414f9bf50c86c2d7235da");

  /* RFC 2202 case 5. */
  memset(k, 0x0c, 20);
  check("rfc2202-5", k, 20, (const uint8_t *)"Test With Truncation", 20,
        "4c1a03424b55e07fe7f27be1d58bb9324a9a5a04");

  /* RFC 2202 cases 6 and 7: a key longer than a block, so it is hashed. */
  memset(k, 0xaa, 80);
  check("rfc2202-6", k, 80,
        (const uint8_t *)"Test Using Larger Than Block-Size Key - Hash Key First", 54,
        "aa4ae5e15272d00e95705637ce8a3b55ed402112");
  check("rfc2202-7", k, 80,
        (const uint8_t *)"Test Using Larger Than Block-Size Key and Larger Than One Block-Size Data",
        73, "e8e99d0f45237d786d6bbaa7965c7808bbff1a91");

  /* The empty key and the empty message. */
  check("empty", k, 0, (const uint8_t *)"", 0,
        "fbdb1d1b18aa6c08324b7d64b71fb76370690e1d");

  /* A key of exactly one block: the boundary of the "hash the key" branch. */
  memset(k, 0xaa, 64);
  check("64-byte key", k, 64, (const uint8_t *)"exactly one block key", 21,
        "a0536a29b44dfd43fec53728c5e013747217f4c6");

  if (failures == 0) {
    printf("  all HMAC-SHA1 tests passed\n");
    return 0;
  }
  printf("  %d HMAC-SHA1 failures\n", failures);
  return 1;
}
