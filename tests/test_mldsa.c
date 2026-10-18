/* ML-DSA (FIPS 204) against the NIST ACVP vectors.
 *
 * The seed for each parameter set is that of the first ML-DSA-keyGen AFT
 * case of the published vectors, so the public and private keys are that
 * case's, byte for byte.  The signatures are over a fixed 33-byte message
 * with the context "context": deterministic, hedged with a fixed rnd, and
 * through the internal interface on the same message.  They were
 * computed with an independent Python model of FIPS 204 that reproduces
 * every published pure, internal and external-mu keyGen, sigGen and
 * sigVer case, and that the extracted C was also run against in full.
 *
 * Keys and signatures run to kilobytes, so what is stored is a SHA3-256
 * digest of each.
 *
 * Each parameter set is checked these ways: the two keys and the three
 * signatures against their digests; the external-mu signature, from
 * mu = H(H(pk) || M'), against the internal one, which must be the same
 * bytes; all four signatures verified through the matching interface;
 * rejection of a signature with one bit flipped, of the right signature
 * under another context, and of the right signature through the internal
 * interface, which does not format the message; and refusal, by both
 * sign and verify, of a 256-byte context.
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl.h"
#include "test_util.h"

static uint8_t pk[2592];
static uint8_t sk[4896];
static uint8_t sg[4627];
static uint8_t sg2[4627];
static uint8_t tr[64];
static uint8_t mu[64];
static uint8_t digest[32];
static uint8_t longctx[256];

static uint8_t msg[33];
static uint8_t ctx[7] = { 'c', 'o', 'n', 't', 'e', 'x', 't' };
static uint8_t rnd[32];

typedef void (*keypair_t)(uint8_t *, uint8_t *, uint8_t *);
typedef bool (*sign_t)(uint8_t *, uint8_t *, uint8_t *, size_t, uint8_t *, size_t, uint8_t *);
typedef bool (*sign_det_t)(uint8_t *, uint8_t *, uint8_t *, size_t, uint8_t *, size_t);
typedef bool (*verify_t)(uint8_t *, uint8_t *, size_t, uint8_t *, size_t, uint8_t *);
typedef bool (*sign_int_t)(uint8_t *, uint8_t *, uint8_t *, size_t, uint8_t *);
typedef bool (*verify_int_t)(uint8_t *, uint8_t *, size_t, uint8_t *);
typedef bool (*sign_mu_t)(uint8_t *, uint8_t *, uint8_t *, uint8_t *);
typedef bool (*verify_mu_t)(uint8_t *, uint8_t *, uint8_t *);

typedef struct {
  const char *name;
  keypair_t keypair;
  sign_t sign;
  sign_det_t sign_det;
  verify_t verify;
  sign_int_t sign_int;
  verify_int_t verify_int;
  sign_mu_t sign_mu;
  verify_mu_t verify_mu;
  size_t pkb, skb, sgb;
  const uint8_t *seed, *pkd, *skd, *sgd_det, *sgd_hedged, *sgd_internal;
} params_t;

static int check_digest(const char *name, const uint8_t *buf, size_t len,
                        const uint8_t *expected) {
  Hacl_Hash_SHA3_sha3_256(digest, (uint8_t *)buf, len);
  return check(name, digest, expected, 32);
}

static int expect(const char *name, bool got, bool want) {
  if (got == want) {
    printf("  ok   %s\n", name);
    return 0;
  }
  printf("  FAIL %s: got %d, expected %d\n", name, (int)got, (int)want);
  return 1;
}

static int one(const params_t *p) {
  int r = 0;
  char label[64];
#define L(s) (snprintf(label, sizeof label, "%s %s", p->name, s), label)

  p->keypair(pk, sk, (uint8_t *)p->seed);
  r |= check_digest(L("pk"), pk, p->pkb, p->pkd);
  r |= check_digest(L("sk"), sk, p->skb, p->skd);

  /* Deterministic, pure. */
  r |= expect(L("sign deterministic"),
              p->sign_det(sg, sk, msg, sizeof msg, ctx, sizeof ctx), true);
  r |= check_digest(L("sig deterministic"), sg, p->sgb, p->sgd_det);
  r |= expect(L("verify deterministic"),
              p->verify(pk, msg, sizeof msg, ctx, sizeof ctx, sg), true);
  /* The same signature under another context, and through the internal
     interface, which does not prepend the context. */
  r |= expect(L("verify other context"),
              p->verify(pk, msg, sizeof msg, ctx, sizeof ctx - 1, sg), false);
  r |= expect(L("verify internal of pure"),
              p->verify_int(pk, msg, sizeof msg, sg), false);
  sg[p->sgb / 2] ^= 1U;
  r |= expect(L("verify flipped bit"),
              p->verify(pk, msg, sizeof msg, ctx, sizeof ctx, sg), false);

  /* Hedged, pure. */
  r |= expect(L("sign hedged"),
              p->sign(sg, sk, msg, sizeof msg, ctx, sizeof ctx, rnd), true);
  r |= check_digest(L("sig hedged"), sg, p->sgb, p->sgd_hedged);
  r |= expect(L("verify hedged"),
              p->verify(pk, msg, sizeof msg, ctx, sizeof ctx, sg), true);

  /* Internal, and external mu with mu = H(H(pk) || M'). */
  r |= expect(L("sign internal"),
              p->sign_int(sg, sk, msg, sizeof msg, rnd), true);
  r |= check_digest(L("sig internal"), sg, p->sgb, p->sgd_internal);
  r |= expect(L("verify internal"),
              p->verify_int(pk, msg, sizeof msg, sg), true);
  Hacl_Hash_SHA3_shake256(tr, 64, pk, p->pkb);
  {
    static uint8_t buf[64 + sizeof msg];
    memcpy(buf, tr, 64);
    memcpy(buf + 64, msg, sizeof msg);
    Hacl_Hash_SHA3_shake256(mu, 64, buf, sizeof buf);
  }
  r |= expect(L("sign mu"), p->sign_mu(sg2, sk, mu, rnd), true);
  r |= expect(L("sig mu = sig internal"), memcmp(sg, sg2, p->sgb) == 0, true);
  r |= expect(L("verify mu"), p->verify_mu(pk, mu, sg2), true);
  mu[0] ^= 1U;
  r |= expect(L("verify mu other mu"), p->verify_mu(pk, mu, sg2), false);

  /* A context is at most 255 bytes. */
  r |= expect(L("sign 256-byte context"),
              p->sign(sg, sk, msg, sizeof msg, longctx, sizeof longctx, rnd), false);
  r |= expect(L("verify 256-byte context"),
              p->verify(pk, msg, sizeof msg, longctx, sizeof longctx, sg), false);

#undef L
  return r;
}

/* ML-DSA-44 */
static const uint8_t seed_44[32] = {
  0x71U, 0x94U, 0xb1U, 0x3cU, 0x95U, 0x23U, 0x10U, 0x10U, 0xafU, 0xd2U, 0xc9U, 0x09U,
  0x99U, 0x2bU, 0xd2U, 0x00U, 0x3bU, 0xa6U, 0xf4U, 0x37U, 0xc3U, 0x88U, 0x6bU, 0xdbU,
  0xe3U, 0xf6U, 0xb8U, 0x67U, 0xa1U, 0x4bU, 0xa1U, 0x61U,
};
static const uint8_t pkd_44[32] = {
  0xd8U, 0xd9U, 0xaaU, 0x04U, 0x03U, 0xddU, 0xc9U, 0x1aU, 0x7fU, 0x2aU, 0xb6U, 0x68U,
  0xfeU, 0xa9U, 0xe8U, 0x5fU, 0x59U, 0xa6U, 0xf5U, 0x19U, 0xbeU, 0xb9U, 0x49U, 0x9fU,
  0xfcU, 0x93U, 0x7dU, 0x6eU, 0xd7U, 0x64U, 0x42U, 0xe3U,
};
static const uint8_t skd_44[32] = {
  0x07U, 0x72U, 0xf7U, 0xccU, 0xc3U, 0x67U, 0x4bU, 0x85U, 0x9cU, 0x9eU, 0xd7U, 0x0dU,
  0xa4U, 0x4bU, 0x35U, 0x59U, 0xceU, 0xc4U, 0x4bU, 0xbdU, 0xf7U, 0x5bU, 0x8eU, 0xa3U,
  0x1eU, 0x04U, 0xa2U, 0x3fU, 0xa6U, 0x87U, 0x1bU, 0x24U,
};
static const uint8_t sgd_det_44[32] = {
  0x92U, 0x3eU, 0x3dU, 0x85U, 0xe7U, 0xedU, 0x36U, 0x60U, 0x69U, 0x77U, 0x8aU, 0xe0U,
  0x32U, 0xa5U, 0x59U, 0x22U, 0x64U, 0x39U, 0x93U, 0xebU, 0x83U, 0x68U, 0xf6U, 0x3fU,
  0x08U, 0x71U, 0xd6U, 0x2aU, 0xb3U, 0x51U, 0x82U, 0x65U,
};
static const uint8_t sgd_hedged_44[32] = {
  0xdcU, 0x7bU, 0xa3U, 0x7cU, 0x16U, 0x86U, 0xb1U, 0x46U, 0x88U, 0xf7U, 0x6fU, 0xccU,
  0xb6U, 0xdeU, 0xdaU, 0xa5U, 0xd1U, 0xd9U, 0x0dU, 0xfaU, 0xd7U, 0x77U, 0x61U, 0xbfU,
  0x99U, 0xe2U, 0xe4U, 0x27U, 0x34U, 0xfeU, 0xeeU, 0x91U,
};
static const uint8_t sgd_internal_44[32] = {
  0xfdU, 0x4aU, 0x03U, 0x32U, 0xc6U, 0x58U, 0x84U, 0x2fU, 0xe9U, 0x88U, 0x7cU, 0xbdU,
  0xa4U, 0x15U, 0x1cU, 0x12U, 0xedU, 0x5cU, 0x7dU, 0x2cU, 0xd6U, 0x96U, 0x45U, 0xf2U,
  0x49U, 0x7eU, 0x11U, 0xdaU, 0xf1U, 0x30U, 0x97U, 0x8cU,
};

/* ML-DSA-65 */
static const uint8_t seed_65[32] = {
  0xa9U, 0x91U, 0xfdU, 0x42U, 0xb0U, 0x71U, 0xd4U, 0x9cU, 0x48U, 0xaeU, 0x3eU, 0x75U,
  0xc6U, 0x47U, 0x45U, 0x9eU, 0x0dU, 0xaaU, 0xd1U, 0xe1U, 0xbaU, 0x35U, 0x6aU, 0x04U,
  0x80U, 0x19U, 0x12U, 0xd3U, 0x29U, 0x4bU, 0xcfU, 0xf8U,
};
static const uint8_t pkd_65[32] = {
  0x00U, 0x83U, 0xe4U, 0xd4U, 0xf5U, 0x62U, 0x78U, 0x0dU, 0xd5U, 0xefU, 0x68U, 0x5cU,
  0x88U, 0xdbU, 0x5aU, 0xfcU, 0xdaU, 0xc4U, 0x4dU, 0x1bU, 0x4bU, 0xe5U, 0xe4U, 0x25U,
  0x3dU, 0x0dU, 0xe7U, 0x71U, 0x10U, 0x03U, 0x16U, 0xf3U,
};
static const uint8_t skd_65[32] = {
  0x9aU, 0x6fU, 0xe5U, 0x79U, 0x6bU, 0xc8U, 0xb6U, 0x1cU, 0x6eU, 0xb2U, 0x74U, 0xccU,
  0x59U, 0x05U, 0xb3U, 0xd3U, 0xceU, 0x21U, 0x69U, 0x3cU, 0x9eU, 0x7fU, 0xd3U, 0x2dU,
  0xb7U, 0x9bU, 0x1cU, 0xffU, 0x49U, 0xe9U, 0x37U, 0x17U,
};
static const uint8_t sgd_det_65[32] = {
  0x98U, 0x49U, 0xc0U, 0x5aU, 0x57U, 0x0eU, 0x16U, 0x0fU, 0xc8U, 0xe6U, 0xd4U, 0x49U,
  0xf9U, 0x83U, 0x1bU, 0x12U, 0xc6U, 0x3dU, 0x12U, 0xdeU, 0x7fU, 0xc3U, 0x4aU, 0xdcU,
  0xb3U, 0xd8U, 0x69U, 0xdaU, 0x33U, 0xb3U, 0x16U, 0x97U,
};
static const uint8_t sgd_hedged_65[32] = {
  0xc6U, 0x5fU, 0xa6U, 0xc0U, 0x5eU, 0x98U, 0xaaU, 0xc0U, 0xb9U, 0x50U, 0xb8U, 0x41U,
  0x69U, 0x86U, 0x58U, 0xd6U, 0xdbU, 0x44U, 0x90U, 0x57U, 0x52U, 0xaeU, 0x45U, 0xb5U,
  0xb5U, 0x17U, 0x2aU, 0x31U, 0xa8U, 0x59U, 0x55U, 0xa9U,
};
static const uint8_t sgd_internal_65[32] = {
  0xf3U, 0x85U, 0x8dU, 0xb6U, 0x7aU, 0xf4U, 0x7eU, 0x09U, 0x8cU, 0x3eU, 0xffU, 0x80U,
  0x57U, 0x93U, 0x8dU, 0x8dU, 0xdeU, 0x77U, 0x92U, 0x26U, 0xb7U, 0xf7U, 0x1aU, 0x03U,
  0x7eU, 0x32U, 0x86U, 0xf1U, 0x11U, 0x69U, 0x27U, 0x63U,
};

/* ML-DSA-87 */
static const uint8_t seed_87[32] = {
  0xa1U, 0x6fU, 0x5bU, 0x07U, 0x96U, 0x70U, 0x3eU, 0x2dU, 0x1aU, 0x01U, 0x40U, 0xa3U,
  0x5cU, 0xbfU, 0x36U, 0xefU, 0xabU, 0xe7U, 0x0eU, 0x75U, 0x2bU, 0xa5U, 0x9bU, 0x6aU,
  0x9aU, 0x0eU, 0x9cU, 0x4bU, 0x05U, 0x30U, 0x2fU, 0x73U,
};
static const uint8_t pkd_87[32] = {
  0x9dU, 0xf3U, 0x92U, 0x32U, 0x07U, 0x7aU, 0x88U, 0xb3U, 0xb3U, 0x6cU, 0x0dU, 0x4bU,
  0x37U, 0xd2U, 0xd3U, 0x69U, 0xf9U, 0x42U, 0xbaU, 0xaaU, 0xa4U, 0x36U, 0xcfU, 0x54U,
  0x86U, 0xa1U, 0xf0U, 0x9dU, 0x45U, 0xd7U, 0xceU, 0x0bU,
};
static const uint8_t skd_87[32] = {
  0xc4U, 0x13U, 0x88U, 0xf2U, 0x2cU, 0xf3U, 0xbcU, 0x0cU, 0xe7U, 0x9eU, 0xb5U, 0xfcU,
  0xcfU, 0xafU, 0xeeU, 0xe5U, 0xecU, 0x31U, 0xe3U, 0xd4U, 0x32U, 0x1aU, 0x8bU, 0xefU,
  0xe7U, 0xf2U, 0x30U, 0xd6U, 0xc4U, 0x84U, 0x1cU, 0xf0U,
};
static const uint8_t sgd_det_87[32] = {
  0x5bU, 0x77U, 0xe6U, 0x8bU, 0x99U, 0xaeU, 0x5fU, 0x14U, 0x6eU, 0x98U, 0x81U, 0x7cU,
  0x97U, 0xd9U, 0xd4U, 0xeeU, 0xc3U, 0xdfU, 0x17U, 0x3cU, 0x8bU, 0xc1U, 0x4fU, 0xe6U,
  0xc6U, 0x0dU, 0x17U, 0x3eU, 0x4aU, 0xd3U, 0x6dU, 0x5bU,
};
static const uint8_t sgd_hedged_87[32] = {
  0x2fU, 0x52U, 0xb8U, 0xd9U, 0x3cU, 0x12U, 0x76U, 0x50U, 0x51U, 0xa0U, 0x49U, 0x02U,
  0xa2U, 0xe5U, 0xadU, 0x65U, 0x36U, 0xa5U, 0xdbU, 0x57U, 0xe8U, 0x37U, 0x2bU, 0x2aU,
  0x01U, 0x2eU, 0x44U, 0x37U, 0x39U, 0x1bU, 0x07U, 0x00U,
};
static const uint8_t sgd_internal_87[32] = {
  0x42U, 0x9aU, 0xfaU, 0x87U, 0xd2U, 0xbdU, 0xcbU, 0x62U, 0x1eU, 0x7aU, 0x20U, 0x96U,
  0xffU, 0x3fU, 0x6fU, 0xd6U, 0x49U, 0x87U, 0x3eU, 0x18U, 0x07U, 0x4eU, 0xa4U, 0x28U,
  0x8fU, 0xa1U, 0xd4U, 0x2cU, 0xb1U, 0xbcU, 0xdcU, 0x29U,
};

#define PARAMS(n, pkb, skb, sgb)                                              \
  { "ML-DSA-" #n, Hacl_MLDSA##n##_keypair, Hacl_MLDSA##n##_sign,              \
    Hacl_MLDSA##n##_sign_deterministic, Hacl_MLDSA##n##_verify,               \
    Hacl_MLDSA##n##_sign_internal, Hacl_MLDSA##n##_verify_internal,           \
    Hacl_MLDSA##n##_sign_mu, Hacl_MLDSA##n##_verify_mu, pkb, skb, sgb,        \
    seed_##n, pkd_##n, skd_##n, sgd_det_##n, sgd_hedged_##n,                  \
    sgd_internal_##n }

static const params_t all[3] = {
  PARAMS(44, 1312, 2560, 2420),
  PARAMS(65, 1952, 4032, 3309),
  PARAMS(87, 2592, 4896, 4627),
};

int main(void) {
  int r = 0;
  for (size_t i = 0; i < sizeof msg; i++)
    msg[i] = (uint8_t)i;
  for (size_t i = 0; i < sizeof rnd; i++)
    rnd[i] = (uint8_t)(64 + i);
  printf("ML-DSA\n");
  for (size_t i = 0; i < 3; i++)
    r |= one(&all[i]);
  return r;
}
