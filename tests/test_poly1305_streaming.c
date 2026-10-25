/* The incremental Poly1305 interface.
 *
 * Every vector of test_poly1305.c -- RFC 8439 section 2.5.2, all of appendix
 * A.3, and the generated sweep around the block boundary -- is run again
 * through the streaming API, fed in each of a set of chunk sizes that
 * straddle the sixteen-byte block from both sides.  That file is included
 * with Hacl_Poly1305_mac redirected to stream_mac below, so the vectors live
 * in one place.  stream_mac checks every chunking against the one-shot MAC
 * and hands the first back for test_poly1305.c's own comparison with the
 * published tag.
 *
 * Then the state's life cycle: digesting does not consume it, so digesting
 * twice must agree and absorbing may continue afterwards; init resets it;
 * and wipe leaves every byte of it zero.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl.h"

/* The whole state: r and its multiples by five, the accumulator, the key
 * (s is read from it at the end), one block of buffered bytes, and how many
 * of those are in use. */
typedef struct {
  uint64_t r[9];
  uint64_t acc[5];
  uint8_t kb[32];
  uint8_t buf[16];
  size_t pos[1];
} poly1305_state;

static void st_init(poly1305_state *s, const uint8_t *key) {
  Hacl_Streaming_Poly1305_poly1305_init(s->r, s->acc, s->kb, s->buf, s->pos,
                                        (uint8_t *)key);
}

static void st_update(poly1305_state *s, const uint8_t *data, size_t len) {
  Hacl_Streaming_Poly1305_poly1305_update(s->r, s->acc, s->buf, s->pos,
                                          (uint8_t *)data, len);
}

static void st_digest(poly1305_state *s, uint8_t *out) {
  Hacl_Streaming_Poly1305_poly1305_digest(s->r, s->acc, s->kb, s->buf, s->pos,
                                          out);
}

static void st_wipe(poly1305_state *s) {
  Hacl_Streaming_Poly1305_poly1305_wipe(s->r, s->acc, s->kb, s->buf, s->pos);
}

static const size_t chunk_sizes[] = {1,  7,   15,  16,  17,  31,  32,  33,
                                     63, 64,  65,  127, 128, 129, 1000};
#define N_CHUNKS (sizeof chunk_sizes / sizeof chunk_sizes[0])

static int stream_failures = 0;

static void stream_with(uint8_t *tag, const uint8_t *msg, size_t len,
                        const uint8_t *key, size_t chunk) {
  poly1305_state s;
  st_init(&s, key);
  /* An empty update is legal anywhere; put one at the very start. */
  st_update(&s, msg, 0);
  for (size_t off = 0; off < len; off += chunk) {
    size_t n = len - off < chunk ? len - off : chunk;
    st_update(&s, msg + off, n);
  }
  st_digest(&s, tag);
  st_wipe(&s);
}

static void stream_mac(uint8_t *tag, uint8_t *msg, size_t len, uint8_t *key) {
  uint8_t oneshot[16], got[16];
  Hacl_Poly1305_mac(oneshot, msg, len, key);
  for (size_t i = 0; i < N_CHUNKS; i++) {
    stream_with(got, msg, len, key, chunk_sizes[i]);
    if (memcmp(got, oneshot, 16) != 0) {
      printf("FAIL streaming len %zu chunk %zu disagrees with one-shot\n", len,
             chunk_sizes[i]);
      stream_failures++;
    }
  }
  stream_with(tag, msg, len, key, 1);
}

#define Hacl_Poly1305_mac stream_mac
#define main poly1305_vectors
#include "test_poly1305.c"
#undef main
#undef Hacl_Poly1305_mac

static int lifecycle(void) {
  int bad = 0;
  uint8_t key[32], msg[300], t1[16], t2[16], want[16];
  for (size_t i = 0; i < sizeof key; i++) key[i] = (uint8_t)(3 * i + 1);
  for (size_t i = 0; i < sizeof msg; i++) msg[i] = (uint8_t)(7 * i + 5);

  poly1305_state s;
  st_init(&s, key);
  st_update(&s, msg, 37);
  st_digest(&s, t1);
  st_digest(&s, t2);
  Hacl_Poly1305_mac(want, msg, 37, key);
  if (memcmp(t1, want, 16) || memcmp(t2, want, 16)) {
    printf("FAIL digest is not repeatable\n");
    bad = 1;
  }

  /* Continue after a digest. */
  st_update(&s, msg + 37, 300 - 37);
  st_digest(&s, t1);
  Hacl_Poly1305_mac(want, msg, 300, key);
  if (memcmp(t1, want, 16)) {
    printf("FAIL update after digest\n");
    bad = 1;
  }

  /* Re-init under another key forgets everything. */
  key[0] ^= 0xff;
  st_init(&s, key);
  st_update(&s, msg, 5);
  st_digest(&s, t1);
  Hacl_Poly1305_mac(want, msg, 5, key);
  if (memcmp(t1, want, 16)) {
    printf("FAIL re-init\n");
    bad = 1;
  }

  /* Wipe zeroes the whole state, key copy included. */
  st_wipe(&s);
  static const poly1305_state zero;
  if (memcmp(s.r, zero.r, sizeof s.r) || memcmp(s.acc, zero.acc, sizeof s.acc) ||
      memcmp(s.kb, zero.kb, sizeof s.kb) || memcmp(s.buf, zero.buf, sizeof s.buf) ||
      s.pos[0] != 0) {
    printf("FAIL wipe left state behind\n");
    bad = 1;
  }
  return bad;
}

int main(void) {
  int bad = poly1305_vectors();
  bad |= stream_failures != 0;
  bad |= lifecycle();
  if (bad) {
    printf("test_poly1305_streaming: FAILED (%d chunking mismatches)\n",
           stream_failures);
    return 1;
  }
  printf("test_poly1305_streaming: all vectors x %zu chunkings, life cycle ok\n",
         (size_t)N_CHUNKS);
  return 0;
}
