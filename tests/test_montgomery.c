/* Montgomery arithmetic, against Python.
 *
 * Every expected value below was computed with Python's arbitrary-precision
 * integers by files/gen_mont.py, which knows nothing about the
 * implementation: it inverts the radix with pow(R, -1, N) and multiplies
 * out.  The modulus is four limbs -- two hundred and fifty-six bits --
 * odd and with its top bit set, which is what every modulus Montgomery
 * arithmetic is applied to looks like.
 *
 * Limbs are little-endian and the arrays are compared as raw bytes, so the
 * host's own byte order never enters into it.
 */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl.h"
#include "test_util.h"

#define NN 4

static uint64_t mont_n[4] = { 0x0aff37b0a9993823ULL, 0x61ea5cd6aeb9ff44ULL, 0x28bf92e8f129e72dULL, 0xa4c4c25edec23e4aULL };
static uint64_t mont_a[4] = { 0x5e9974481bc955eaULL, 0x3dc165d08123c0d7ULL, 0xc30f3acfddc60450ULL, 0x701cb1ea97062032ULL };
static uint64_t mont_b[4] = { 0x92b3c87ba970c296ULL, 0x803ccbc49a645bd1ULL, 0x8fc54d6fbc318d2cULL, 0x88efc1ba9cd237f8ULL };
static uint64_t mont_c[8] = { 0x30a17d057aa91a25ULL, 0xdc1b048507cbd566ULL, 0xf2647d8a135a236eULL, 0x5d7c498a0c68b695ULL, 0xd91b05b30656a414ULL, 0xfd408d19530874abULL, 0x7a26446ff2a30623ULL, 0x68394383426f97bcULL };
static const uint64_t mont_mu_expected = 0x80324e2ea54ac875ULL;
static uint64_t mont_r2[4] = { 0x9891d7c2f5f331abULL, 0xa4b60055aea96d6cULL, 0x7128a33d9e032e0dULL, 0x999205a3a34c9329ULL };
static const uint64_t mont_mul_ab[4] = { 0x12dde768b9990a13ULL, 0x09aa8f21379f2658ULL, 0x659f129032aefdb1ULL, 0x8f14737f494c25e6ULL };
static const uint64_t mont_from_a[4] = { 0x53a587a5b8e3d3bdULL, 0xd489f6035daf99faULL, 0xc00d013f83eb5e81ULL, 0x681e0e21c16a0fe9ULL };
static const uint64_t mont_c_mod[4] = { 0xf04da55854a6119dULL, 0x18b3e5b1eeb674c6ULL, 0xa389b10018bd348fULL, 0x95e107e67a406916ULL };
static const uint64_t mont_to_a[4] = { 0x2f9dc5ac5b1c0cb5ULL, 0x252bb9cbf75b3a32ULL, 0xea504b09c8845b3bULL, 0x7252d79fa5293682ULL };
static const uint64_t exp_ab[4] = { 0xbe72a321bba4ef18ULL, 0xb20d0fe168f1d3cdULL, 0xb44d1ec93764ffbcULL, 0x15c3a03310cf0608ULL };
static const uint64_t exp_inv[4] = { 0x1afdb80365dd4f38ULL, 0x78f2508dcc60cff0ULL, 0xc41b20aa6bbe0069ULL, 0x678e9fbe2513441aULL };

static int check_limbs(const char *name, const uint64_t *got,
                       const uint64_t *want, size_t n) {
  return check(name, (const uint8_t *)got, (const uint8_t *)want, 8 * n);
}

int main(void) {
  int bad = 0;
  uint64_t res[NN], acc[NN], scratch[NN], tmp[2 * NN], wide[2 * NN];

  /* The one precomputed limb. */
  uint64_t mu = Hacl_Bignum_Montgomery_mont_mu(mont_n[0]);
  if (mu != mont_mu_expected) {
    printf("  FAIL mont_mu: got %016" PRIx64 " expected %016" PRIx64 "\n", mu,
           mont_mu_expected);
    bad = 1;
  } else {
    printf("  ok   mont_mu\n");
  }

  /* R^2 mod N. */
  Hacl_Bignum_Montgomery_precomp(res, acc, scratch, wide, mont_n, NN, mu);
  bad |= check_limbs("precomp", res, mont_r2, NN);

  /* a * b / R mod N, both operands already reduced. */
  Hacl_Bignum_Montgomery_mont_mul(res, mont_a, mont_b, tmp, mont_n, NN, mu);
  bad |= check_limbs("mont_mul", res, mont_mul_ab, NN);

  /* Entering Montgomery form is a multiplication by the constant. */
  Hacl_Bignum_Montgomery_mont_mul(res, mont_a, mont_r2, tmp, mont_n, NN, mu);
  bad |= check_limbs("to_mont", res, mont_to_a, NN);

  /* ... and leaving it again gets the original back. */
  memcpy(acc, res, sizeof res);
  Hacl_Bignum_Montgomery_from_mont(res, acc, tmp, mont_n, NN, mu);
  bad |= check_limbs("round trip", res, mont_a, NN);

  /* a / R mod N on its own. */
  Hacl_Bignum_Montgomery_from_mont(res, mont_a, tmp, mont_n, NN, mu);
  bad |= check_limbs("from_mont", res, mont_from_a, NN);

  /* The reduction on its own: c / R mod N. */
  memcpy(wide, mont_c, sizeof wide);
  Hacl_Bignum_Montgomery_reduction(res, wide, mont_n, NN, mu);
  {
    /* c / R mod N is from_mont of (c mod N), so compare against that route. */
    uint64_t want[NN];
    memcpy(wide, mont_c, sizeof wide);
    Hacl_Bignum_Montgomery_modulo(want, wide, acc, mont_r2, mont_n, NN, mu);
    Hacl_Bignum_Montgomery_from_mont(acc, want, tmp, mont_n, NN, mu);
    bad |= check_limbs("reduction", res, acc, NN);
  }

  /* A plain remainder. */
  memcpy(wide, mont_c, sizeof wide);
  Hacl_Bignum_Montgomery_modulo(res, wide, acc, mont_r2, mont_n, NN, mu);
  bad |= check_limbs("mod", res, mont_c_mod, NN);

  /* a^b mod n, by both ladders: they must agree with each other and with
     Python. */
  {
    uint64_t aM[NN], t[NN], e[NN];
    Hacl_Bignum_Exponentiation_mod_exp_consttime(res, mont_a, mont_b, 256,
                                                 mont_r2, mont_n, NN, mu,
                                                 aM, acc, t, wide);
    bad |= check_limbs("mod_exp_consttime", res, exp_ab, NN);

    Hacl_Bignum_Exponentiation_mod_exp_vartime(res, mont_a, mont_b, 256,
                                               mont_r2, mont_n, NN, mu,
                                               aM, acc, t, wide);
    bad |= check_limbs("mod_exp_vartime", res, exp_ab, NN);

    /* a^(n-2) mod n: an inverse when n is prime, a power in any case. */
    Hacl_Bignum_Exponentiation_mod_inv_prime_vartime(res, mont_a, mont_r2,
                                                     mont_n, NN, mu, e,
                                                     aM, acc, t, wide);
    bad |= check_limbs("mod_inv_prime_vartime", res, exp_inv, NN);
  }

  if (bad != 0) {
    printf("montgomery: failure(s)\n");
    return 1;
  }
  printf("all montgomery vectors pass\n");
  return 0;
}
