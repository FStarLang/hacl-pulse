/* The incremental sponge.
 *
 * The one-shot interface is checked against FIPS 202 in test_sha3.c, so what
 * matters here is that feeding a message in pieces gives the same answer as
 * feeding it whole, whatever the pieces are.  The rates in play are 168, 144,
 * 136, 104 and 72 bytes, so the chunk sizes below straddle all of them from
 * both sides.
 *
 * We also check the three lifecycle properties the interface promises: digest
 * does not consume the state, so calling it twice gives the same answer, an
 * update after a digest continues the same message, and a SHAKE state can be
 * squeezed at two different lengths (the shorter output being a prefix of the
 * longer). */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl.h"

static int failures = 0;

static void hex(char *dst, const uint8_t *src, size_t n) {
  for (size_t i = 0; i < n; i++)
    sprintf(dst + 2 * i, "%02x", src[i]);
}

/* A state, big enough for any of the six: twenty-five lanes, one rate's worth
 * of buffer (168 at most) and the byte count. */
typedef struct {
  uint64_t acc[25];
  uint8_t buf[168];
  size_t tot;
} state;

typedef void (*init_f)(uint64_t *, uint8_t *, size_t *);
typedef void (*update_f)(uint64_t *, uint8_t *, size_t *, uint8_t *, size_t);
typedef void (*digest_f)(uint64_t *, uint8_t *, size_t *, uint8_t *);
typedef void (*xdigest_f)(uint64_t *, uint8_t *, size_t *, uint8_t *, size_t);

typedef struct {
  const char *name;
  size_t rate;
  size_t digest_len;
  init_f init;
  update_f update;
  digest_f digest;   /* fixed-length algorithms */
  xdigest_f xdigest; /* the two XOFs */
} alg;

#define SHA3(nm, r, dl, pfx)                                                   \
  { nm, r, dl, pfx##_init, pfx##_update, pfx##_digest, NULL }
#define SHAKE(nm, r, dl, pfx)                                                  \
  { nm, r, dl, pfx##_init, pfx##_update, NULL, pfx##_digest }

static const alg algs[6] = {
    SHA3("SHA3-224", 144, 28, Hacl_Streaming_SHA3_sha3_224),
    SHA3("SHA3-256", 136, 32, Hacl_Streaming_SHA3_sha3_256),
    SHA3("SHA3-384", 104, 48, Hacl_Streaming_SHA3_sha3_384),
    SHA3("SHA3-512", 72, 64, Hacl_Streaming_SHA3_sha3_512),
    SHAKE("SHAKE128", 168, 64, Hacl_Streaming_SHA3_shake128),
    SHAKE("SHAKE256", 136, 64, Hacl_Streaming_SHA3_shake256),
};

static void squeeze(const alg *a, state *st, uint8_t *out, size_t out_len) {
  if (a->xdigest)
    a->xdigest(st->acc, st->buf, &st->tot, out, out_len);
  else
    a->digest(st->acc, st->buf, &st->tot, out);
}

static void hash_in_chunks(const alg *a, state *st, const uint8_t *msg,
                           size_t msg_len, size_t chunk, uint8_t *out,
                           size_t out_len) {
  a->init(st->acc, st->buf, &st->tot);
  size_t i = 0;
  while (i < msg_len) {
    size_t n = msg_len - i < chunk ? msg_len - i : chunk;
    a->update(st->acc, st->buf, &st->tot, (uint8_t *)msg + i, n);
    i += n;
  }
  squeeze(a, st, out, out_len);
}

static void check(const char *what, const alg *a, const uint8_t *msg,
                  size_t msg_len, size_t chunk, const char *expected) {
  state st;
  uint8_t out[64];
  char got[129];

  memset(&st, 0, sizeof st);
  memset(out, 0, sizeof out);
  hash_in_chunks(a, &st, msg, msg_len, chunk, out, a->digest_len);
  hex(got, out, a->digest_len);

  if (strcmp(got, expected) != 0) {
    printf("  FAIL %s %s chunk=%zu\n    got      %s\n    expected %s\n",
           a->name, what, chunk, got, expected);
    failures++;
  }
}

/* Sizes that straddle every rate from both sides, plus one that swallows the
 * whole message at once. */
static const size_t chunks[] = {1,   3,   71,  72,  73,  103, 104, 105,
                                135, 136, 137, 143, 144, 145, 167, 168,
                                169, 200, 1000};
#define NCHUNKS (sizeof chunks / sizeof chunks[0])

static void check_all_chunks(const char *what, const uint8_t *msg,
                             size_t msg_len, const char *const *digests,
                             const char *const *xofs) {
  for (int k = 0; k < 6; k++) {
    const char *expected = k < 4 ? digests[k] : xofs[k - 4];
    for (size_t c = 0; c < NCHUNKS; c++)
      check(what, &algs[k], msg, msg_len, chunks[c], expected);
    printf("  ok   %s %s (%zu chunk sizes)\n", algs[k].name, what, NCHUNKS);
  }
}

#define S448 "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
#define S896                                                                   \
  "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjk" \
  "lmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"

static const char *const empty_d[4] = {
    "6b4e03423667dbb73b6e15454f0eb1abd4597f9a1b078e3f5b5a6bc7",
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a",
    "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2a"
    "c3713831264adb47fb6bd1e058d5f004",
    "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a6"
    "15b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26",
};
static const char *const empty_x[2] = {
    "7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26"
    "3cb1eea988004b93103cfb0aeefd2a686e01fa4a58e8a3639ca8a1e3f9ae57e2",
    "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f"
    "d75dc4ddd8c0f200cb05019d67b592f6fc821c49479ab48640292eacb3b7c4be",
};
static const char *const abc_d[4] = {
    "e642824c3f8cf24ad09234ee7d3c766fc9a3a5168d0c94ad73b46fdf",
    "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532",
    "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b2"
    "98d88cea927ac7f539f1edf228376d25",
    "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e"
    "10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0",
};
static const char *const abc_x[2] = {
    "5881092dd818bf5cf8a3ddb793fbcba74097d5c526a6d35f97b83351940f2cc8"
    "44c50af32acd3f2cdd066568706f509bc1bdde58295dae3f891a9a0fca578378",
    "483366601360a8771c6863080cc4114d8db44530f8f1e1ee4f94ea37e78b5739"
    "d5a15bef186a5386c75744c0527e1faa9f8726e462a12a4feb06bd8801e751e4",
};
static const char *const s448_d[4] = {
    "8a24108b154ada21c9fd5574494479ba5c7e7ab76ef264ead0fcce33",
    "41c0dba2a9d6240849100376a8235e2c82e1b9998a999e21db32dd97496d3376",
    "991c665755eb3a4b6bbdfb75c78a492e8c56a22c5c4d7e429bfdbc32b9d4ad5a"
    "a04a1f076e62fea19eef51acd0657c22",
    "04a371e84ecfb5b8b77cb48610fca8182dd457ce6f326a0fd3d7ec2f1e91636d"
    "ee691fbe0c985302ba1b0d8dc78c086346b533b49c030d99a27daf1139d6e75e",
};
static const char *const s448_x[2] = {
    "1a96182b50fb8c7e74e0a707788f55e98209b8d91fade8f32f8dd5cff7bf21f5"
    "4ee5f19550825a6e070030519e944263ac1c6765287065621f9fcb3201723e32",
    "4d8c2dd2435a0128eefbb8c36f6f87133a7911e18d979ee1ae6be5d4fd2e3329"
    "40d8688a4e6a59aa8060f1f9bc996c05aca3c696a8b66279dc672c740bb224ec",
};
static const char *const s896_d[4] = {
    "543e6868e1666c1a643630df77367ae5a62a85070a51c14cbf665cbc",
    "916f6061fe879741ca6469b43971dfdb28b1a32dc36cb3254e812be27aad1d18",
    "79407d3b5916b59c3e30b09822974791c313fb9ecc849e406f23592d04f625dc"
    "8c709b98b43b3852b337216179aa7fc7",
    "afebb2ef542e6579c50cad06d2e578f9f8dd6881d7dc824d26360feebf18a4fa"
    "73e3261122948efcfd492e74e82e2189ed0fb440d187f382270cb455f21dd185",
};
static const char *const s896_x[2] = {
    "7b6df6ff181173b6d7898d7ff63fb07b7c237daf471a5ae5602adbccef9ccf4b"
    "37e06b4a3543164ffbe0d0557c02f9b25ad434005526d88ca04a6094b93ee57a",
    "98be04516c04cc73593fef3ed0352ea9f6443942d6950e29a372a681c3deaf45"
    "35423709b02843948684e029010badcc0acd8303fc85fdad3eabf4f78cae1656",
};
static const char *const m1000_d[4] = {
    "2459c65a000e217e65e9992435021787b4461e3bcd09b14348d2d9fc",
    "9392d9e39b54fd1ee9f4655170fe8452f0793f47fc2af813d9c75727390b07a3",
    "95a2b7f72e41a03e3ca1f0124d877927368a417aa593e0d0e9081809abea8c26"
    "9b54575746b3753d50e714060322f67d",
    "71a4118f314ec6f5bf8ba025d49b997515fd1eeeb58ce48ee94c5c7ef927e474"
    "bc903d5859632f548dd6500f1c5f2b05f01a10d858c5f45957c51d2747e48d01",
};
static const char *const m1000_x[2] = {
    "394d95d6ddda7470d2e0cbe62961cf146c335dad81685e6242a7de2e09644bbe"
    "cab6532ba00bf7212a6e686893af05add59f4a6a114e061a131ffb25e290611a",
    "9c5d86e3aaa8830ec440a447b8f69e171903f9c691e73ef8a82f617a9680f233"
    "4b50cc6c0e5a4622aa226212d9901b7cf6eefd5d38d2c8f30f509e10079f943f",
};

static const char *const abcabc_d[4] = {
    "58f426458091e16fbc61ddcb8f2d2a6f30f729cafa3c289a4eb2bcf8",
    "6c0872716337de1ee664c1e37f64ade109448f02681c63a912bc230fdefc0058",
    "34fa93e11e467d610524ec91cedc848ee1395bcf8f4f987455478e63db0bce47"
    "194d33d1251a3cc32bbb18d8726040d0",
    "bb582da40d15399acf62afcbbd6cfc9ee1dd5129b1ef9935dd3b21668f1a73d7"
    "841018be3b13f281c3a8e9da7edb60f57b9f9f1c04033df4ce3654b7b2adb310",
};
static const char *const abcabc_x[2] = {
    "b3e0f3d610f7bdbb3b7ad0bfeb76e1ef253ff4bcf11820831ec921900b47e17f"
    "1c7aa205158d2de5a7a2f7e84496acf1e7a772fae0ae0ed5387555bfeed763b8",
    "862c9aa2e847b85719054ac8b234ce0126f3e1e87b0062ca498aed13e56f55b5"
    "b5990cc0048b19103de0a1c6dd4c9d2053b42f93badc82aec3338c3a2dae0465",
};

/* --- lifecycle ----------------------------------------------------------- */

/* digest does not consume the state: calling it twice gives the same bytes,
 * and an update afterwards continues the same message. */
static void check_reuse(const alg *a, const char *expected_abc,
                        const char *expected_abcabc) {
  state st;
  uint8_t out1[64], out2[64], out3[64], ref[64];
  char got[129], want[129];

  memset(&st, 0, sizeof st);
  a->init(st.acc, st.buf, &st.tot);
  a->update(st.acc, st.buf, &st.tot, (uint8_t *)"abc", 3);
  squeeze(a, &st, out1, a->digest_len);
  squeeze(a, &st, out2, a->digest_len);
  if (memcmp(out1, out2, a->digest_len) != 0) {
    printf("  FAIL %s digest is not idempotent\n", a->name);
    failures++;
  }
  hex(got, out1, a->digest_len);
  if (strcmp(got, expected_abc) != 0) {
    printf("  FAIL %s reuse: digest of \"abc\"\n    got      %s\n"
           "    expected %s\n",
           a->name, got, expected_abc);
    failures++;
  }

  a->update(st.acc, st.buf, &st.tot, (uint8_t *)"abc", 3);
  squeeze(a, &st, out3, a->digest_len);
  hex(got, out3, a->digest_len);
  if (strcmp(got, expected_abcabc) != 0) {
    printf("  FAIL %s update after digest\n    got      %s\n"
           "    expected %s\n",
           a->name, got, expected_abcabc);
    failures++;
  }

  /* the same message hashed from scratch had better agree */
  memset(&st, 0, sizeof st);
  hash_in_chunks(a, &st, (const uint8_t *)"abcabc", 6, 1, ref, a->digest_len);
  hex(want, ref, a->digest_len);
  if (strcmp(got, want) != 0) {
    printf("  FAIL %s update after digest disagrees with one shot\n", a->name);
    failures++;
  }
  printf("  ok   %s reuse\n", a->name);
}

/* A SHAKE state squeezed at two lengths: the shorter output is a prefix of the
 * longer one, because both are the same output stream. */
static void check_xof_lengths(const alg *a) {
  state st;
  uint8_t shortout[16], longout[200];

  memset(&st, 0, sizeof st);
  a->init(st.acc, st.buf, &st.tot);
  a->update(st.acc, st.buf, &st.tot, (uint8_t *)"abc", 3);
  a->xdigest(st.acc, st.buf, &st.tot, shortout, sizeof shortout);
  a->xdigest(st.acc, st.buf, &st.tot, longout, sizeof longout);
  if (memcmp(shortout, longout, sizeof shortout) != 0) {
    printf("  FAIL %s short squeeze is not a prefix of the long one\n",
           a->name);
    failures++;
  } else {
    printf("  ok   %s squeezed at two lengths\n", a->name);
  }
}

int main(void) {
  uint8_t m1000[1000];
  memset(m1000, 'x', sizeof m1000);

  printf("streaming SHA-3\n");
  check_all_chunks("\"\"", (const uint8_t *)"", 0, empty_d, empty_x);
  check_all_chunks("\"abc\"", (const uint8_t *)"abc", 3, abc_d, abc_x);
  check_all_chunks("448-bit", (const uint8_t *)S448, strlen(S448), s448_d,
                   s448_x);
  check_all_chunks("896-bit", (const uint8_t *)S896, strlen(S896), s896_d,
                   s896_x);
  check_all_chunks("1000 x 'x'", m1000, sizeof m1000, m1000_d, m1000_x);

  for (int k = 0; k < 6; k++)
    check_reuse(&algs[k], k < 4 ? abc_d[k] : abc_x[k - 4],
                k < 4 ? abcabc_d[k] : abcabc_x[k - 4]);

  check_xof_lengths(&algs[4]);
  check_xof_lengths(&algs[5]);

  if (failures == 0) {
    printf("all streaming SHA-3 tests passed\n");
    return 0;
  }
  printf("%d streaming SHA-3 test(s) FAILED\n", failures);
  return 1;
}
