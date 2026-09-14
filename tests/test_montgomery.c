/* Montgomery arithmetic, against Python.
 *
 * Every expected value below was computed with Python's arbitrary-precision
 * integers by files/gen_mont.py, which knows nothing about the
 * implementation: it inverts the radix with pow(R, -1, N) and multiplies
 * out.  The modulus is four limbs -- a hundred and twenty-eight bits --
 * odd and with its top bit set, which is what every modulus Montgomery
 * arithmetic is applied to looks like.
 *
 * Limbs are little-endian and the arrays are compared as raw bytes, so the
 * host's own byte order never enters into it.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "Hacl.h"
#include "test_util.h"

#define NN 4

static uint32_t mont_n[4] = { 0x090b8461U, 0xd9d89c6dU, 0xdaca8cebU, 0xe6435113U };
static uint32_t mont_a[4] = { 0xb07280c0U, 0x7d858c44U, 0xccb7e564U, 0xa62ffd7dU };
static uint32_t mont_b[4] = { 0x3b659e8eU, 0x4f0d4e56U, 0xa7771d9eU, 0x14dbcb1dU };
static uint32_t mont_c[8] = { 0xe828155fU, 0x95bcc355U, 0xbcb88d29U, 0xd381108eU, 0x6bea4de7U, 0x7a63caceU, 0xe476bb20U, 0xab1835acU };
static const uint32_t mont_mu_expected = 0xdb05e05fU;
static uint32_t mont_r2[4] = { 0xe396a093U, 0x4370fe2bU, 0x5c7e2c95U, 0x7699f3dfU };
static const uint32_t mont_mul_ab[4] = { 0xc67cf3c0U, 0x39a0ece2U, 0x90c0b3eaU, 0x114010b6U };
static const uint32_t mont_from_a[4] = { 0x30bd1330U, 0x17eeed24U, 0x11450f48U, 0x76a4b302U };
static const uint32_t mont_c_mod[4] = { 0xbfb7e9a9U, 0x808c2de2U, 0x6fd659ccU, 0x14a1abfdU };
static const uint32_t mont_to_a[4] = { 0x8e598ba5U, 0x5c27ab9cU, 0x97ba74dbU, 0xadf82829U };
static const uint32_t exp_ab[4] = { 0xee9c8d88U, 0x6188a6e3U, 0x2c138fafU, 0x4927cc35U };
static const uint32_t exp_inv[4] = { 0x7da97972U, 0x1803aeb8U, 0xf00931faU, 0x7d07ed42U };

static int check_limbs(const char *name, const uint32_t *got,
                       const uint32_t *want, size_t n) {
  return check(name, (const uint8_t *)got, (const uint8_t *)want, 4 * n);
}

int main(void) {
  int bad = 0;
  uint32_t res[NN], acc[NN], tmp[2 * NN], wide[2 * NN];

  /* The one precomputed limb. */
  uint32_t mu = Hacl_Bignum_Montgomery_mont_mu(mont_n[0]);
  if (mu != mont_mu_expected) {
    printf("  FAIL mont_mu: got %08x expected %08x\n", mu, mont_mu_expected);
    bad = 1;
  } else {
    printf("  ok   mont_mu\n");
  }

  /* R^2 mod N. */
  Hacl_Bignum_Montgomery_precomp(res, mont_n, NN);
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
    uint32_t want[NN];
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
    uint32_t aM[NN], t[NN], e[NN];
    Hacl_Bignum_Exponentiation_mod_exp_consttime(res, mont_a, mont_b, 128,
                                                 mont_r2, mont_n, NN, mu,
                                                 aM, acc, t, wide);
    bad |= check_limbs("mod_exp_consttime", res, exp_ab, NN);

    Hacl_Bignum_Exponentiation_mod_exp_vartime(res, mont_a, mont_b, 128,
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
