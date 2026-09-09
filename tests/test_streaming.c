/* The incremental hash.
 *
 * The one-shot interface is checked against FIPS 180-4 in test_sha2.c, so what
 * matters here is that feeding a message in pieces gives the same answer as
 * feeding it whole, whatever the pieces are.  We therefore run the same
 * messages through the streaming interface in a range of chunk sizes chosen to
 * straddle the block boundary from both sides -- 1, 3, 63, 64, 65, 127, 128,
 * 129 and 1000 bytes -- and compare against the published digest.
 *
 * We also check the two lifecycle properties the interface promises: digest
 * does not consume the state, so calling it twice gives the same answer and
 * updating after it continues the same message. */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_Streaming_SHA2_Ptr.h"

static int failures = 0;

static void hex(char *dst, const uint8_t *src, size_t n) {
  for (size_t i = 0; i < n; i++)
    sprintf(dst + 2 * i, "%02x", src[i]);
}

/* One algorithm's three entry points, plus its shapes. */
typedef struct {
  const char *name;
  size_t word_bytes;  /* 4 or 8 */
  size_t block_len;   /* 64 or 128 */
  size_t digest_len;
  void (*init)(void *acc, uint8_t *buf, size_t *tot);
  void (*update)(void *acc, uint8_t *buf, size_t *tot, uint8_t *data,
                 size_t data_len);
  void (*digest)(void *acc, uint8_t *buf, size_t *tot, uint8_t *out);
} alg;

/* The generated prototypes take a pointer to uint32_t or to uint64_t for the
 * accumulator; the table above erases that to void * so the four algorithms fit
 * one shape.  The
 * casts are the usual C function-pointer casts and are safe here because the
 * pointer representation is the same. */
#define ALG(nm, wb, bl, dl, pfx)                                               \
  {                                                                            \
    nm, wb, bl, dl, (void (*)(void *, uint8_t *, size_t *))pfx##_init,         \
        (void (*)(void *, uint8_t *, size_t *, uint8_t *, size_t))pfx##_update,\
        (void (*)(void *, uint8_t *, size_t *, uint8_t *))pfx##_digest         \
  }

static const alg algs[4] = {
    ALG("SHA-224", 4, 64, 28, Hacl_Streaming_SHA2_Ptr_sha224),
    ALG("SHA-256", 4, 64, 32, Hacl_Streaming_SHA2_Ptr_sha256),
    ALG("SHA-384", 8, 128, 48, Hacl_Streaming_SHA2_Ptr_sha384),
    ALG("SHA-512", 8, 128, 64, Hacl_Streaming_SHA2_Ptr_sha512),
};

/* A state, big enough for either family. */
typedef struct {
  uint64_t acc[8];
  uint8_t buf[128];
  size_t tot;
} state;

static void hash_in_chunks(const alg *a, state *st, const uint8_t *msg,
                           size_t msg_len, size_t chunk, uint8_t *out) {
  a->init(st->acc, st->buf, &st->tot);
  size_t i = 0;
  while (i < msg_len) {
    size_t n = msg_len - i < chunk ? msg_len - i : chunk;
    a->update(st->acc, st->buf, &st->tot, (uint8_t *)msg + i, n);
    i += n;
  }
  a->digest(st->acc, st->buf, &st->tot, out);
}

static void check(const char *what, const alg *a, const uint8_t *msg,
                  size_t msg_len, size_t chunk, const char *expected) {
  state st;
  uint8_t out[64];
  char got[129];

  memset(&st, 0, sizeof st);
  memset(out, 0, sizeof out);
  hash_in_chunks(a, &st, msg, msg_len, chunk, out);
  hex(got, out, a->digest_len);

  if (strcmp(got, expected) != 0) {
    printf("  FAIL %s %s chunk=%zu\n    got      %s\n    expected %s\n",
           a->name, what, chunk, got, expected);
    failures++;
  }
}

static const size_t chunks[] = {1, 3, 63, 64, 65, 127, 128, 129, 1000};
#define NCHUNKS (sizeof chunks / sizeof chunks[0])

static void check_all_chunks(const char *what, const uint8_t *msg,
                             size_t msg_len, const char *const *expected) {
  for (int k = 0; k < 4; k++) {
    for (size_t c = 0; c < NCHUNKS; c++)
      check(what, &algs[k], msg, msg_len, chunks[c], expected[k]);
    printf("  ok   %s %s (%zu chunk sizes)\n", algs[k].name, what, NCHUNKS);
  }
}

#define ABC "abc"
#define S448 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
#define S896                                                                   \
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjk" \
  "lmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"

static const char *const empty_d[4] = {
    "d14a028c2a3a2bc9476102bb288234c415a2b01f828ea62ac5b3e42f",
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
    "38b060a751ac96384cd9327eb1b1e36a21fdb71114be07434c0cc7bf63f6e1da"
    "274edebfe76f65fbd51ad2f14898b95b",
    "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce"
    "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
};

static const char *const abc_d[4] = {
    "23097d223405d8228642a477bda255b32aadbce4bda0b3f7e36c9da7",
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
    "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed"
    "8086072ba1e7cc2358baeca134c825a7",
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
    "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
};

static const char *const s448_d[4] = {
    "75388b16512776cc5dba5da1fd890150b0c6455cb4f58b1952522525",
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
    "3391fdddfc8dc7393707a65b1b4709397cf8b1d162af05abfe8f450de5f36bc6"
    "b0455a8520bc4e6f5fe95b1fe3c8452b",
    "204a8fc6dda82f0a0ced7beb8e08a41657c16ef468b228a8279be331a703c335"
    "96fd15c13b1b07f9aa1d3bea57789ca031ad85c7a71dd70354ec631238ca3445",
};

static const char *const s896_d[4] = {
    "c97ca9a559850ce97a04a96def6d99a9e0e0e2ab14e6b8df265fc0b3",
    "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1",
    "09330c33f71147e83d192fc782cd1b4753111b173b3b05d22fa08086e3b0f712"
    "fcc7c71a557e2db966c3e9fa91746039",
    "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018"
    "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909",
};

static const char *const million_a_d[4] = {
    "20794655980c91d8bbb4c1ea97618a4bf03f42581948b2ee4ee7ad67",
    "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0",
    "9d0e1809716474cb086e834e310a4a1ced149e9c00f248527972cec5704c2a5b"
    "07b8b3dc38ecc4ebae97ddd87f3d8985",
    "e718483d0ce769644e2e42c7bc15b4638e1f98b13b2044285632a803afa973eb"
    "de0ff244877ea60a4cb0432ce577c31beb009c5c2c49aa2e4eadb217ad8cc09b",
};

/* digest leaves the state usable: two digests agree, and an update after a
 * digest continues the same message. */
static void check_lifecycle(void) {
  for (int k = 0; k < 4; k++) {
    const alg *a = &algs[k];
    state st;
    uint8_t d1[64], d2[64], d3[64], ref[64];
    char got[129], want[129];

    memset(&st, 0, sizeof st);
    a->init(st.acc, st.buf, &st.tot);
    a->update(st.acc, st.buf, &st.tot, (uint8_t *)ABC, strlen(ABC));
    a->digest(st.acc, st.buf, &st.tot, d1);
    a->digest(st.acc, st.buf, &st.tot, d2);

    if (memcmp(d1, d2, a->digest_len) != 0) {
      printf("  FAIL %s digest is not idempotent\n", a->name);
      failures++;
      continue;
    }
    hex(got, d1, a->digest_len);
    if (strcmp(got, abc_d[k]) != 0) {
      printf("  FAIL %s digest after \"abc\"\n    got      %s\n"
             "    expected %s\n",
             a->name, got, abc_d[k]);
      failures++;
      continue;
    }

    /* Carry on with the rest of S448 and compare with hashing it whole. */
    a->update(st.acc, st.buf, &st.tot, (uint8_t *)S448 + strlen(ABC),
              strlen(S448) - strlen(ABC));
    a->digest(st.acc, st.buf, &st.tot, d3);

    memset(&st, 0, sizeof st);
    hash_in_chunks(a, &st, (const uint8_t *)S448, strlen(S448), strlen(S448),
                   ref);

    hex(got, d3, a->digest_len);
    hex(want, ref, a->digest_len);
    if (strcmp(got, want) != 0) {
      printf("  FAIL %s update after digest\n    got      %s\n"
             "    expected %s\n",
             a->name, got, want);
      failures++;
      continue;
    }
    printf("  ok   %s lifecycle\n", a->name);
  }
}

int main(void) {
  /* S448 is 55 bytes, one short of a block; S896 is 112, one short of two. */
  check_all_chunks("empty", (const uint8_t *)"", 0, empty_d);
  check_all_chunks("abc", (const uint8_t *)ABC, strlen(ABC), abc_d);
  check_all_chunks("448-bit", (const uint8_t *)S448, strlen(S448), s448_d);
  check_all_chunks("896-bit", (const uint8_t *)S896, strlen(S896), s896_d);

  {
    size_t n = 1000000;
    uint8_t *big = malloc(n);
    if (big == NULL) {
      printf("  FAIL out of memory\n");
      return 1;
    }
    memset(big, 'a', n);
    /* Only the larger chunk sizes, or this takes a while. */
    for (int k = 0; k < 4; k++) {
      check("a million 'a'", &algs[k], big, n, 1000, million_a_d[k]);
      check("a million 'a'", &algs[k], big, n, 128, million_a_d[k]);
      printf("  ok   %s a million 'a'\n", algs[k].name);
    }
    free(big);
  }

  check_lifecycle();

  if (failures != 0) {
    printf("%d failure(s)\n", failures);
    return 1;
  }
  printf("all streaming vectors pass\n");
  return 0;
}
