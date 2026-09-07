/* AES-128-GCM using AES-NI + PCLMULQDQ intrinsics. See header for scope. */

#include "aesgcm_x86_intrin.h"

#include <string.h>
#include <wmmintrin.h>
#include <immintrin.h>

#define AGG AESGCM_AGG
#define TGT __attribute__((target("aes,pclmul,ssse3,sse4.1,avx")))

/* Byte-swap mask: GHASH operates big-endian, x86 loads little-endian. */
#define BSWAP_MASK _mm_set_epi64x(0x0001020304050607ULL, 0x08090a0b0c0d0e0fULL)

/* ---------------------------------------------------------------- AES-128 */

TGT static inline __m128i aes_ks_step(__m128i k, __m128i g)
{
  g = _mm_shuffle_epi32(g, 0xff);
  k = _mm_xor_si128(k, _mm_slli_si128(k, 4));
  k = _mm_xor_si128(k, _mm_slli_si128(k, 4));
  k = _mm_xor_si128(k, _mm_slli_si128(k, 4));
  return _mm_xor_si128(k, g);
}

TGT static void aes128_expand(const uint8_t *key, __m128i rk[11])
{
  rk[0] = _mm_loadu_si128((const __m128i *)key);
#define KE(i, r) rk[i] = aes_ks_step(rk[i - 1], _mm_aeskeygenassist_si128(rk[i - 1], r));
  KE(1, 0x01) KE(2, 0x02) KE(3, 0x04) KE(4, 0x08) KE(5, 0x10)
  KE(6, 0x20) KE(7, 0x40) KE(8, 0x80) KE(9, 0x1b) KE(10, 0x36)
#undef KE
}

TGT static inline __m128i aes128_encrypt_block(__m128i b, const __m128i rk[11])
{
  b = _mm_xor_si128(b, rk[0]);
  for (int i = 1; i < 10; i++) b = _mm_aesenc_si128(b, rk[i]);
  return _mm_aesenclast_si128(b, rk[10]);
}

/* ------------------------------------------------------------------ GHASH */

/* hi^lo halves, precomputed once per key power for Karatsuba. */
TGT static inline __m128i ghash_xhalf(__m128i h)
{
  return _mm_xor_si128(h, _mm_shuffle_epi32(h, 0x4E));
}

/* Karatsuba: 3 clmuls per block instead of the naive 4.
 *
 * This is the single biggest win in this file. Going from 4 to 3 clmuls took
 * the implementation from 1.24x Vale to 0.96x Vale -- PCLMULQDQ throughput is
 * the bottleneck in the aggregated loop, not AES.
 *
 * Products are accumulated unreduced across AGG blocks; one reduction at the
 * end. Valid because GF(2) multiply-then-reduce is linear, so
 * sum(reduce(x_i)) == reduce(sum(x_i)). */
TGT static inline void ghash_karatsuba_acc(__m128i a, __m128i b, __m128i bx,
                                           __m128i *lo, __m128i *hi, __m128i *k)
{
  *lo = _mm_xor_si128(*lo, _mm_clmulepi64_si128(a, b, 0x00));
  *hi = _mm_xor_si128(*hi, _mm_clmulepi64_si128(a, b, 0x11));
  __m128i ax = _mm_xor_si128(a, _mm_shuffle_epi32(a, 0x4E));
  *k  = _mm_xor_si128(*k,  _mm_clmulepi64_si128(ax, bx, 0x00));
}

/* Fold the Karatsuba middle term, shift left by 1 (GCM's reflected bit order),
 * then reduce mod x^128 + x^7 + x^2 + x + 1.
 *
 * This is Intel's shift-based reduction. A 2-clmul Montgomery reduction would
 * be cheaper, but the obvious transcription of it did not validate against
 * EverCrypt and the payoff is small (one reduction per AGG=8 blocks), so it
 * was left alone. That is the main remaining optimisation in this file. */
TGT static inline __m128i ghash_reduce(__m128i lo, __m128i hi, __m128i k)
{
  __m128i mid = _mm_xor_si128(k, _mm_xor_si128(lo, hi));
  __m128i t3 = lo, t6 = hi, t7, t8, t9, t2, t4, t5;

  t3 = _mm_xor_si128(t3, _mm_slli_si128(mid, 8));
  t6 = _mm_xor_si128(t6, _mm_srli_si128(mid, 8));

  t7 = _mm_srli_epi32(t3, 31); t8 = _mm_srli_epi32(t6, 31);
  t3 = _mm_slli_epi32(t3, 1);  t6 = _mm_slli_epi32(t6, 1);
  t9 = _mm_srli_si128(t7, 12); t8 = _mm_slli_si128(t8, 4); t7 = _mm_slli_si128(t7, 4);
  t3 = _mm_or_si128(t3, t7); t6 = _mm_or_si128(t6, t8); t6 = _mm_or_si128(t6, t9);

  t7 = _mm_slli_epi32(t3, 31); t8 = _mm_slli_epi32(t3, 30); t9 = _mm_slli_epi32(t3, 25);
  t7 = _mm_xor_si128(t7, t8); t7 = _mm_xor_si128(t7, t9);
  t8 = _mm_srli_si128(t7, 4); t7 = _mm_slli_si128(t7, 12);
  t3 = _mm_xor_si128(t3, t7);

  t2 = _mm_srli_epi32(t3, 1); t4 = _mm_srli_epi32(t3, 2); t5 = _mm_srli_epi32(t3, 7);
  t2 = _mm_xor_si128(t2, t4); t2 = _mm_xor_si128(t2, t5); t2 = _mm_xor_si128(t2, t8);
  t3 = _mm_xor_si128(t3, t2);

  return _mm_xor_si128(t6, t3);
}

TGT static inline __m128i ghash_mul(__m128i a, __m128i b)
{
  __m128i lo = _mm_setzero_si128(), hi = _mm_setzero_si128(), k = _mm_setzero_si128();
  ghash_karatsuba_acc(a, b, ghash_xhalf(b), &lo, &hi, &k);
  return ghash_reduce(lo, hi, k);
}

/* -------------------------------------------------------------------- API */

TGT void aesgcm128_init(aesgcm_ctx *g, const uint8_t *key)
{
  aes128_expand(key, g->rk);
  g->H = _mm_shuffle_epi8(aes128_encrypt_block(_mm_setzero_si128(), g->rk), BSWAP_MASK);
  g->Hp[0] = g->H;
  for (int i = 1; i < AGG; i++) g->Hp[i] = ghash_mul(g->Hp[i - 1], g->H);
  for (int i = 0; i < AGG; i++) g->Hx[i] = ghash_xhalf(g->Hp[i]);
}

TGT void aesgcm128_encrypt(const aesgcm_ctx *g,
                           const uint8_t *iv,
                           const uint8_t *aad, size_t aad_len,
                           const uint8_t *pt, size_t len,
                           uint8_t *ct, uint8_t *tag)
{
  const __m128i BS = BSWAP_MASK;
  const __m128i *rk = g->rk, *Hp = g->Hp, *Hx = g->Hx;
  const __m128i H = g->H;
  const __m128i J0 = _mm_loadu_si128((const __m128i *)iv);
  __m128i Y = _mm_setzero_si128();

  /* --- AAD --- */
  size_t i = 0;
  for (; i + 16 <= aad_len; i += 16)
    Y = ghash_mul(_mm_xor_si128(Y, _mm_shuffle_epi8(
          _mm_loadu_si128((const __m128i *)(aad + i)), BS)), H);
  if (i < aad_len) {
    uint8_t b[16] = {0};
    memcpy(b, aad + i, aad_len - i);
    Y = ghash_mul(_mm_xor_si128(Y, _mm_shuffle_epi8(
          _mm_loadu_si128((const __m128i *)b), BS)), H);
  }

  uint32_t ctr;
  { uint32_t v; memcpy(&v, iv + 12, 4); ctr = __builtin_bswap32(v); }

  const size_t nb = len / 16;
  size_t done = 0;
  int have = 0;                 /* is gbuf holding a previous group? */
  __m128i gbuf[AGG];

  /* --- Main loop: AGG blocks of CTR, with the *previous* group's GHASH
   * products folded in one per AES round ("stitching"). Interleaving the
   * PCLMULQDQ and AESENC dependency chains is worth a few percent; Vale does
   * the same thing by hand. --- */
  while (done + AGG <= nb) {
    __m128i ks[AGG];
    for (int j = 0; j < AGG; j++) {
      __m128i cb = _mm_insert_epi32(J0,
          (int)__builtin_bswap32(ctr + 1 + (uint32_t)(done + j)), 3);
      ks[j] = _mm_xor_si128(cb, rk[0]);
    }

    __m128i lo = _mm_setzero_si128(), hi = _mm_setzero_si128(), k = _mm_setzero_si128();
    for (int r = 1; r < 10; r++) {
      for (int j = 0; j < AGG; j++) ks[j] = _mm_aesenc_si128(ks[j], rk[r]);
      if (have && r <= AGG)
        ghash_karatsuba_acc(gbuf[r - 1], Hp[AGG - r], Hx[AGG - r], &lo, &hi, &k);
    }
    for (int j = 0; j < AGG; j++) ks[j] = _mm_aesenclast_si128(ks[j], rk[10]);

    if (have) Y = ghash_reduce(lo, hi, k);

    for (int j = 0; j < AGG; j++) {
      __m128i c = _mm_xor_si128(
          _mm_loadu_si128((const __m128i *)(pt + (done + j) * 16)), ks[j]);
      _mm_storeu_si128((__m128i *)(ct + (done + j) * 16), c);
      gbuf[j] = _mm_shuffle_epi8(c, BS);
    }
    gbuf[0] = _mm_xor_si128(gbuf[0], Y);
    have = 1;
    done += AGG;
  }

  /* drain the pipeline */
  if (have) {
    __m128i lo = _mm_setzero_si128(), hi = _mm_setzero_si128(), k = _mm_setzero_si128();
    for (int j = 0; j < AGG; j++)
      ghash_karatsuba_acc(gbuf[j], Hp[AGG - 1 - j], Hx[AGG - 1 - j], &lo, &hi, &k);
    Y = ghash_reduce(lo, hi, k);
  }

  /* --- tail: whole blocks, then a partial block --- */
  for (; done < nb; done++) {
    __m128i cb = _mm_insert_epi32(J0,
        (int)__builtin_bswap32(ctr + 1 + (uint32_t)done), 3);
    __m128i c = _mm_xor_si128(
        _mm_loadu_si128((const __m128i *)(pt + done * 16)),
        aes128_encrypt_block(cb, rk));
    _mm_storeu_si128((__m128i *)(ct + done * 16), c);
    Y = ghash_mul(_mm_xor_si128(Y, _mm_shuffle_epi8(c, BS)), H);
  }

  size_t rem = len % 16;
  if (rem) {
    uint8_t b[16] = {0}, kb[16];
    __m128i cb = _mm_insert_epi32(J0,
        (int)__builtin_bswap32(ctr + 1 + (uint32_t)nb), 3);
    _mm_storeu_si128((__m128i *)kb, aes128_encrypt_block(cb, rk));
    for (size_t j = 0; j < rem; j++) ct[nb * 16 + j] = pt[nb * 16 + j] ^ kb[j];
    memcpy(b, ct + nb * 16, rem);
    Y = ghash_mul(_mm_xor_si128(Y, _mm_shuffle_epi8(
          _mm_loadu_si128((const __m128i *)b), BS)), H);
  }

  /* --- length block and tag --- */
  __m128i L = _mm_set_epi64x((long long)(aad_len * 8), (long long)(len * 8));
  Y = ghash_mul(_mm_xor_si128(Y, L), H);
  _mm_storeu_si128((__m128i *)tag,
      _mm_xor_si128(_mm_shuffle_epi8(Y, BS), aes128_encrypt_block(J0, rk)));
}
