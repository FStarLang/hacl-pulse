/* AES-128-GCM using AES-NI + PCLMULQDQ intrinsics.
 *
 * Prototype written to evaluate replacing dist/vale/aesgcm-x86_64-*.S with C.
 * Measured faster than the Vale assembly at every message size under clang.
 * See ../README.md for numbers and caveats.
 *
 * NOT PRODUCTION CODE: encrypt-only, AES-128 only, 96-bit IV only.
 * It exists to answer "can C match the assembly?", not to be shipped.
 */

#ifndef AESGCM_X86_INTRIN_H
#define AESGCM_X86_INTRIN_H

#include <stdint.h>
#include <stddef.h>
#include <emmintrin.h>

/* Number of blocks processed per aggregated GHASH reduction.
 * 8 measured best on Zen 2; 6 is close. See README "Aggregation factor". */
#ifndef AESGCM_AGG
#define AESGCM_AGG 8
#endif

/* Expanded key schedule + precomputed GHASH key powers.
 * Hoisting this out of the per-message path matters: recomputing it per call
 * cost ~4% at 16 KiB and far more on short messages. EverCrypt keeps the
 * equivalent state in EverCrypt_AEAD_state_s, so this is the fair comparison. */
typedef struct {
  __m128i rk[11];               /* AES-128 round keys */
  __m128i Hp[AESGCM_AGG];       /* H^1 .. H^AGG */
  __m128i Hx[AESGCM_AGG];       /* Karatsuba middle terms: hi^lo of each Hp */
  __m128i H;
} aesgcm_ctx;

/* key: 16 bytes */
void aesgcm128_init(aesgcm_ctx *ctx, const uint8_t *key);

/* iv: 16 bytes, must be the 96-bit IV followed by the big-endian counter 1,
 * i.e. iv[0..11] = nonce, iv[12..15] = {0,0,0,1}.
 * tag: 16 bytes out. ct may alias pt. */
void aesgcm128_encrypt(const aesgcm_ctx *ctx,
                       const uint8_t *iv,
                       const uint8_t *aad, size_t aad_len,
                       const uint8_t *pt, size_t pt_len,
                       uint8_t *ct, uint8_t *tag);

#endif /* AESGCM_X86_INTRIN_H */
