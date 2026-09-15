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

/* Incremental MD5.

   Two things are checked.  Against the FIPS vectors, that feeding a message
   in chunks gives the documented digest -- for a range of chunk sizes chosen
   around the block boundary, which is where the buffering logic lives.  And
   against the one-shot entry point, that an *arbitrary* split of an arbitrary
   message agrees, which is the property that actually matters: the streaming
   state machine must not care where the caller's calls fall. */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "Hacl.h"

static int failures = 0;

typedef struct {
  uint32_t acc[4];
  uint8_t buf[64];
  size_t tot;
} state;

static void hash_in_chunks(state *st, const uint8_t *msg, size_t len,
                           size_t chunk, uint8_t *out) {
  Hacl_Streaming_MD5_md5_init(st->acc, st->buf, &st->tot);
  for (size_t i = 0; i < len; ) {
    size_t n = len - i < chunk ? len - i : chunk;
    Hacl_Streaming_MD5_md5_update(st->acc, st->buf, &st->tot,
                                    (uint8_t *)msg + i, n);
    i += n;
  }
  Hacl_Streaming_MD5_md5_digest(st->acc, st->buf, &st->tot, out);
}

static void hex(const uint8_t *d, char *s) {
  for (size_t i = 0; i < 16; i++) sprintf(s + 2 * i, "%02x", d[i]);
  s[32] = 0;
}

static void check(const char *what, const uint8_t *msg, size_t len,
                  size_t chunk, const char *expected) {
  state st;
  uint8_t out[16];
  char got[33];
  hash_in_chunks(&st, msg, len, chunk, out);
  hex(out, got);
  if (strcmp(got, expected) != 0) {
    printf("  FAIL %s chunk=%zu\n    got      %s\n    expected %s\n",
           what, chunk, got, expected);
    failures++;
  }
}

static const size_t chunks[] = {1, 2, 3, 31, 63, 64, 65, 127, 128, 129, 1000};
#define NCHUNKS (sizeof chunks / sizeof chunks[0])

static void check_all_chunks(const char *what, const uint8_t *msg, size_t len,
                             const char *expected) {
  for (size_t c = 0; c < NCHUNKS; c++)
    check(what, msg, len, chunks[c], expected);
  printf("  ok   %s (%zu chunk sizes)\n", what, NCHUNKS);
}

/* xorshift64*, so the random splits are the same on every machine. */
static uint64_t rng_state = 0x9e3779b97f4a7c15ULL;
static uint64_t rng(void) {
  rng_state ^= rng_state >> 12;
  rng_state ^= rng_state << 25;
  rng_state ^= rng_state >> 27;
  return rng_state * 0x2545f4914f6cdd1dULL;
}

int main(void) {
  printf("MD5 (incremental)\n");

  check_all_chunks("empty", (const uint8_t *)"", 0,
                   "d41d8cd98f00b204e9800998ecf8427e");
  check_all_chunks("abc", (const uint8_t *)"abc", 3,
                   "900150983cd24fb0d6963f7d28e17f72");
  check_all_chunks("448-bit",
                   (const uint8_t *)"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
                   56, "8215ef0796a20bcaaae116d3876c664a");

  /* A block boundary reached exactly, then nothing more. */
  {
    uint8_t a[64];
    memset(a, 'a', sizeof a);
    check_all_chunks("64 x a", a, 64, "014842d480b571495a4a0363793f7367");
  }

  /* Arbitrary splits of arbitrary messages, against the one-shot hash. */
  {
    size_t n = 4096;
    uint8_t *msg = malloc(n);
    if (msg == NULL) { printf("  FAIL out of memory\n"); return 1; }
    for (size_t i = 0; i < n; i++) msg[i] = (uint8_t)rng();

    int mismatches = 0;
    for (int trial = 0; trial < 500; trial++) {
      size_t len = (size_t)(rng() % (n + 1));
      uint8_t want[16], got[16];
      state st;
      Hacl_Hash_MD5_md5(want, msg, len);

      Hacl_Streaming_MD5_md5_init(st.acc, st.buf, &st.tot);
      for (size_t i = 0; i < len; ) {
        size_t n2 = (size_t)(rng() % 200);
        if (n2 > len - i) n2 = len - i;
        Hacl_Streaming_MD5_md5_update(st.acc, st.buf, &st.tot, msg + i, n2);
        i += n2;
      }
      Hacl_Streaming_MD5_md5_digest(st.acc, st.buf, &st.tot, got);
      if (memcmp(want, got, 16) != 0) mismatches++;
    }
    if (mismatches != 0) {
      printf("  FAIL %d of 500 random splits disagreed with the one-shot hash\n",
             mismatches);
      failures++;
    } else {
      printf("  ok   500 random splits agree with the one-shot hash\n");
    }

    /* The state is left usable: two digests in a row, and an update in
       between, behave as if the digest had not happened. */
    {
      state st;
      uint8_t d1[16], d2[16], d3[16], want[16];
      Hacl_Streaming_MD5_md5_init(st.acc, st.buf, &st.tot);
      Hacl_Streaming_MD5_md5_update(st.acc, st.buf, &st.tot, msg, 100);
      Hacl_Streaming_MD5_md5_digest(st.acc, st.buf, &st.tot, d1);
      Hacl_Streaming_MD5_md5_digest(st.acc, st.buf, &st.tot, d2);
      Hacl_Streaming_MD5_md5_update(st.acc, st.buf, &st.tot, msg + 100, 900);
      Hacl_Streaming_MD5_md5_digest(st.acc, st.buf, &st.tot, d3);
      Hacl_Hash_MD5_md5(want, msg, 100);
      if (memcmp(d1, d2, 16) != 0 || memcmp(d1, want, 16) != 0) {
        printf("  FAIL digest is not idempotent\n");
        failures++;
      }
      Hacl_Hash_MD5_md5(want, msg, 1000);
      if (memcmp(d3, want, 16) != 0) {
        printf("  FAIL the state was not usable after a digest\n");
        failures++;
      }
      if (failures == 0)
        printf("  ok   digest leaves the state usable\n");
    }
    free(msg);
  }

  if (failures == 0) {
    printf("  all incremental MD5 tests passed\n");
    return 0;
  }
  printf("  %d incremental MD5 failures\n", failures);
  return 1;
}
