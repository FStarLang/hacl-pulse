/* The incremental HMAC interface.
 *
 * Two things need checking.  First that the streaming answer is the one-shot
 * answer -- the one-shot code is checked against RFC 4231 in test_hmac.c, so
 * it serves as the oracle here, and this file only anchors one RFC vector
 * directly so that a shared bug in both would still be caught.  Second that
 * the state behaves: the digest does not consume it, so digesting twice must
 * agree and absorbing may continue afterwards.
 *
 * The message is fed in chunk sizes chosen to straddle the block boundary
 * from both sides, since that is where update_impl branches.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl.h"
#include "test_util.h"

/* RFC 4231 case 1, as an anchor. */
static uint8_t rfc_key[20] = {
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
    0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b, 0x0b,
};

static uint8_t rfc_msg[8] = {
    0x48, 0x69, 0x20, 0x54, 0x68, 0x65, 0x72, 0x65,
};

static uint8_t rfc_sha256[32] = {
    0xb0, 0x34, 0x4c, 0x61, 0xd8, 0xdb, 0x38, 0x53, 0x5c, 0xa8, 0xaf, 0xce,
    0xaf, 0x0b, 0xf1, 0x2b, 0x88, 0x1d, 0xc2, 0x00, 0xc9, 0x83, 0x3d, 0xa7,
    0x26, 0xe9, 0x37, 0x6c, 0x2e, 0x32, 0xcf, 0xf7,
};

/* One state per digest width.  The four arrays are the whole state: the
 * accumulator, one block of buffered bytes, the byte count, and the saved
 * K0 ^ opad block. */
#define DEFINE_ALG(NAME, WORD, ACCT, BLK, OLEN)                                \
  typedef struct {                                                             \
    ACCT acc[8];                                                               \
    uint8_t buf[BLK];                                                          \
    size_t tot[1];                                                             \
    uint8_t opadb[BLK];                                                        \
  } st_##NAME;                                                                 \
                                                                               \
  static void init_##NAME(st_##NAME *s, const uint8_t *key, size_t klen) {     \
    Hacl_Streaming_HMAC_hmac_##NAME##_init(s->acc, s->buf, s->tot, s->opadb,   \
                                           (uint8_t *)key, klen);              \
  }                                                                            \
  static void update_##NAME(st_##NAME *s, const uint8_t *d, size_t n) {        \
    Hacl_Streaming_HMAC_hmac_##NAME##_update(s->acc, s->buf, s->tot,           \
                                             (uint8_t *)d, n);                 \
  }                                                                            \
  static void digest_##NAME(st_##NAME *s, uint8_t *out) {                      \
    Hacl_Streaming_HMAC_hmac_##NAME##_digest(s->acc, s->buf, s->tot, s->opadb, \
                                             out);                             \
  }                                                                            \
  static void oneshot_##NAME(uint8_t *out, const uint8_t *key, size_t klen,    \
                             const uint8_t *msg, size_t mlen) {                \
    Hacl_HMAC_hmac_##NAME(out, (uint8_t *)key, klen, (uint8_t *)msg, mlen);    \
  }

DEFINE_ALG(sha224, 32, uint32_t, 64, 28)
DEFINE_ALG(sha256, 32, uint32_t, 64, 32)
DEFINE_ALG(sha384, 64, uint64_t, 128, 48)
DEFINE_ALG(sha512, 64, uint64_t, 128, 64)

static const size_t chunks[] = {1, 7, 31, 32, 63, 64, 65, 127, 128, 129, 1000};
#define NCHUNKS (sizeof chunks / sizeof chunks[0])

/* Feed [msg] in fixed-size pieces and compare against the one-shot answer. */
#define CHUNKED_TEST(NAME, OLEN)                                               \
  static int chunked_##NAME(const char *what, const uint8_t *key, size_t klen, \
                            const uint8_t *msg, size_t mlen) {                 \
    uint8_t want[OLEN], got[OLEN];                                             \
    char label[128];                                                           \
    st_##NAME s;                                                               \
    int bad = 0;                                                               \
    oneshot_##NAME(want, key, klen, msg, mlen);                                \
    for (size_t c = 0; c < NCHUNKS; c++) {                                     \
      init_##NAME(&s, key, klen);                                              \
      for (size_t off = 0; off < mlen;) {                                      \
        size_t n = chunks[c];                                                  \
        if (n > mlen - off)                                                    \
          n = mlen - off;                                                      \
        update_##NAME(&s, msg + off, n);                                       \
        off += n;                                                              \
      }                                                                        \
      digest_##NAME(&s, got);                                                  \
      if (memcmp(got, want, OLEN) != 0) {                                      \
        snprintf(label, sizeof label, "%s %s chunk %zu", #NAME, what,          \
                 chunks[c]);                                                   \
        bad |= check(label, got, want, OLEN);                                  \
      }                                                                        \
    }                                                                          \
    snprintf(label, sizeof label, "%s %s (%zu chunk sizes)", #NAME, what,      \
             NCHUNKS);                                                         \
    if (!bad)                                                                  \
      printf("  ok   %s\n", label);                                            \
    return bad;                                                                \
  }

CHUNKED_TEST(sha224, 28)
CHUNKED_TEST(sha256, 32)
CHUNKED_TEST(sha384, 48)
CHUNKED_TEST(sha512, 64)

/* Digest twice, then keep absorbing: the state must survive both. */
#define LIFECYCLE_TEST(NAME, OLEN)                                             \
  static int lifecycle_##NAME(const uint8_t *key, size_t klen,                 \
                              const uint8_t *msg, size_t mlen) {               \
    uint8_t a[OLEN], b[OLEN], c[OLEN], want[OLEN];                             \
    st_##NAME s;                                                               \
    int bad = 0;                                                               \
    size_t half = mlen / 2;                                                    \
    init_##NAME(&s, key, klen);                                                \
    update_##NAME(&s, msg, half);                                              \
    digest_##NAME(&s, a);                                                      \
    digest_##NAME(&s, b);                                                      \
    oneshot_##NAME(want, key, klen, msg, half);                                \
    bad |= check(#NAME " digest of a prefix", a, want, OLEN);                  \
    bad |= check(#NAME " digest is idempotent", b, a, OLEN);                   \
    update_##NAME(&s, msg + half, mlen - half);                                \
    digest_##NAME(&s, c);                                                      \
    oneshot_##NAME(want, key, klen, msg, mlen);                                \
    bad |= check(#NAME " absorb continues after digest", c, want, OLEN);       \
    return bad;                                                                \
  }

LIFECYCLE_TEST(sha224, 28)
LIFECYCLE_TEST(sha256, 32)
LIFECYCLE_TEST(sha384, 48)
LIFECYCLE_TEST(sha512, 64)

int main(void) {
  int bad = 0;

  /* A key shorter than a block, a key of exactly one block, and a key long
   * enough that it must itself be hashed: the three branches of key_block. */
  static uint8_t k_short[20], k_exact[128], k_long[200], msg[4096];
  for (size_t i = 0; i < sizeof k_short; i++)
    k_short[i] = (uint8_t)(0x0b + i);
  for (size_t i = 0; i < sizeof k_exact; i++)
    k_exact[i] = (uint8_t)i;
  for (size_t i = 0; i < sizeof k_long; i++)
    k_long[i] = (uint8_t)(0xaa ^ i);
  for (size_t i = 0; i < sizeof msg; i++)
    msg[i] = (uint8_t)(i * 7 + 3);

  {
    st_sha256 s;
    uint8_t got[32];
    init_sha256(&s, rfc_key, sizeof rfc_key);
    update_sha256(&s, rfc_msg, 3);
    update_sha256(&s, rfc_msg + 3, sizeof rfc_msg - 3);
    digest_sha256(&s, got);
    bad |= check("RFC 4231 case 1, HMAC-SHA-256, in two pieces", got,
                 rfc_sha256, 32);
  }

  /* Message lengths on either side of one and two blocks of each width. */
  static const size_t lens[] = {0, 1, 55, 56, 63, 64, 65, 111, 112,
                                127, 128, 129, 255, 256, 1000, 4096};
  for (size_t i = 0; i < sizeof lens / sizeof lens[0]; i++) {
    char what[64];
    snprintf(what, sizeof what, "%zu-byte message", lens[i]);
    bad |= chunked_sha256(what, k_short, sizeof k_short, msg, lens[i]);
    bad |= chunked_sha512(what, k_short, sizeof k_short, msg, lens[i]);
  }

  bad |= chunked_sha224("short key", k_short, sizeof k_short, msg, 1000);
  bad |= chunked_sha256("short key", k_short, sizeof k_short, msg, 1000);
  bad |= chunked_sha384("short key", k_short, sizeof k_short, msg, 1000);
  bad |= chunked_sha512("short key", k_short, sizeof k_short, msg, 1000);

  bad |= chunked_sha224("block-length key", k_exact, 64, msg, 1000);
  bad |= chunked_sha256("block-length key", k_exact, 64, msg, 1000);
  bad |= chunked_sha384("block-length key", k_exact, 128, msg, 1000);
  bad |= chunked_sha512("block-length key", k_exact, 128, msg, 1000);

  bad |= chunked_sha224("oversize key", k_long, sizeof k_long, msg, 1000);
  bad |= chunked_sha256("oversize key", k_long, sizeof k_long, msg, 1000);
  bad |= chunked_sha384("oversize key", k_long, sizeof k_long, msg, 1000);
  bad |= chunked_sha512("oversize key", k_long, sizeof k_long, msg, 1000);

  bad |= chunked_sha256("empty key", k_short, 0, msg, 1000);
  bad |= chunked_sha512("empty key", k_short, 0, msg, 1000);

  bad |= lifecycle_sha224(k_short, sizeof k_short, msg, 1000);
  bad |= lifecycle_sha256(k_short, sizeof k_short, msg, 1000);
  bad |= lifecycle_sha384(k_long, sizeof k_long, msg, 1000);
  bad |= lifecycle_sha512(k_exact, 128, msg, 1000);

  if (bad) {
    printf("streaming HMAC tests FAILED\n");
    return 1;
  }
  printf("all streaming HMAC tests passed\n");
  return 0;
}
