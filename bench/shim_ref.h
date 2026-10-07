/* HACL* (reference C dist) side of the benchmark shim. */
#ifndef SHIM_H
#define SHIM_H

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "Hacl_Hash_MD5.h"
#include "Hacl_Hash_SHA1.h"
#include "Hacl_Hash_SHA2.h"
#include "Hacl_Hash_SHA3.h"
#include "Hacl_Hash_Blake2b.h"
#include "Hacl_Hash_Blake2s.h"
#include "Hacl_HMAC.h"
#include "Hacl_HKDF.h"
#include "Hacl_Chacha20.h"
#include "Hacl_Salsa20.h"
#include "Hacl_MAC_Poly1305.h"
#include "Hacl_AEAD_Chacha20Poly1305.h"
#include "Hacl_NaCl.h"
#include "Hacl_Curve25519_51.h"
#include "Hacl_Curve25519_64.h"
#include "Hacl_Ed25519.h"
#include "Hacl_P256.h"
#include "Hacl_K256_ECDSA.h"
#include "Hacl_RSAPSS.h"
#include "Hacl_FFDHE.h"
#include "Hacl_Bignum32.h"
#include "Hacl_Bignum64.h"
#include "Hacl_HMAC_DRBG.h"
#ifdef BS_REF_BEST
#include "Hacl_Hash_Blake2b_Simd256.h"
#include "Hacl_Hash_Blake2s_Simd128.h"
#include "Hacl_Chacha20_Vec256.h"
#include "Hacl_MAC_Poly1305_Simd256.h"
#include "Hacl_AEAD_Chacha20Poly1305_Simd256.h"
#include "EverCrypt_Hash.h"
#include "EverCrypt_HMAC.h"
#include "EverCrypt_HKDF.h"
#endif
#include "EverCrypt_AEAD.h"
#include "EverCrypt_AutoConfig2.h"
#include "Hacl_Spec.h"
#include "Hacl_Streaming_Types.h"

#ifdef BS_REF_BEST
#define IMPL_NAME "hacl-best"
#else
#define IMPL_NAME "hacl"
#endif
#define HAVE_REF_EXTRAS 1

/* ---- hashes ---- */
static inline void bs_md5(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_MD5_hash(o, m, (uint32_t)n); }
static inline void bs_sha1(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA1_hash(o, m, (uint32_t)n); }
#ifdef BS_REF_BEST
/* EverCrypt multiplexes SHA-2 onto Vale's SHA-EXT code on a CPU with sha_ni,
   which this one has; the scalar entry point never would. */
static inline void bs_sha256(uint8_t *o, uint8_t *m, size_t n) { EverCrypt_Hash_Incremental_hash(Spec_Hash_Definitions_SHA2_256, o, m, (uint32_t)n); }
#else
static inline void bs_sha256(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA2_hash_256(o, m, (uint32_t)n); }
#endif
#ifdef BS_REF_BEST
static inline void bs_sha512(uint8_t *o, uint8_t *m, size_t n) { EverCrypt_Hash_Incremental_hash(Spec_Hash_Definitions_SHA2_512, o, m, (uint32_t)n); }
#else
static inline void bs_sha512(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA2_hash_512(o, m, (uint32_t)n); }
#endif
static inline void bs_sha3_256(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA3_sha3_256(o, m, (uint32_t)n); }
static inline void bs_sha3_512(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA3_sha3_512(o, m, (uint32_t)n); }
static inline void bs_shake128(uint8_t *o, size_t ol, uint8_t *m, size_t n) { Hacl_Hash_SHA3_shake128(o, (uint32_t)ol, m, (uint32_t)n); }
#ifdef BS_REF_BEST
static inline void bs_blake2b(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_Blake2b_Simd256_hash_with_key(o, 64, m, (uint32_t)n, NULL, 0); }
#else
static inline void bs_blake2b(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_Blake2b_hash_with_key(o, 64, m, (uint32_t)n, NULL, 0); }
#endif
#ifdef BS_REF_BEST
static inline void bs_blake2s(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_Blake2s_Simd128_hash_with_key(o, 32, m, (uint32_t)n, NULL, 0); }
#else
static inline void bs_blake2s(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_Blake2s_hash_with_key(o, 32, m, (uint32_t)n, NULL, 0); }
#endif

/* ---- streaming SHA-256 ----
   HACL*'s streaming state is heap-allocated once and reset per message, which
   is the cheapest way to drive it; the malloc is therefore outside the loop. */
typedef struct { Hacl_Streaming_MD_state_32 *st; } bs_sha256_state;
static inline void bs_sha256_stream(bs_sha256_state *s, uint8_t *o, uint8_t *m, size_t n, size_t chunk) {
  if (s->st == NULL) s->st = Hacl_Hash_SHA2_malloc_256();
  Hacl_Hash_SHA2_reset_256(s->st);
  for (size_t i = 0; i < n; i += chunk) {
    size_t c = n - i < chunk ? n - i : chunk;
    Hacl_Hash_SHA2_update_256(s->st, m + i, (uint32_t)c);
  }
  Hacl_Hash_SHA2_digest_256(s->st, o);
}

/* ---- MACs / KDFs ---- */
#ifdef BS_REF_BEST
static inline void bs_hmac_sha256(uint8_t *o, uint8_t *k, size_t kl, uint8_t *m, size_t n) { EverCrypt_HMAC_compute(Spec_Hash_Definitions_SHA2_256, o, k, (uint32_t)kl, m, (uint32_t)n); }
#else
static inline void bs_hmac_sha256(uint8_t *o, uint8_t *k, size_t kl, uint8_t *m, size_t n) { Hacl_HMAC_compute_sha2_256(o, k, (uint32_t)kl, m, (uint32_t)n); }
#endif
#ifdef BS_REF_BEST
static inline void bs_hmac_sha512(uint8_t *o, uint8_t *k, size_t kl, uint8_t *m, size_t n) { EverCrypt_HMAC_compute(Spec_Hash_Definitions_SHA2_512, o, k, (uint32_t)kl, m, (uint32_t)n); }
#else
static inline void bs_hmac_sha512(uint8_t *o, uint8_t *k, size_t kl, uint8_t *m, size_t n) { Hacl_HMAC_compute_sha2_512(o, k, (uint32_t)kl, m, (uint32_t)n); }
#endif
#ifdef BS_REF_BEST
static inline void bs_hkdf_extract_sha256(uint8_t *o, uint8_t *s, size_t sl, uint8_t *i, size_t il) { EverCrypt_HKDF_extract(Spec_Hash_Definitions_SHA2_256, o, s, (uint32_t)sl, i, (uint32_t)il); }
#else
static inline void bs_hkdf_extract_sha256(uint8_t *o, uint8_t *s, size_t sl, uint8_t *i, size_t il) { Hacl_HKDF_extract_sha2_256(o, s, (uint32_t)sl, i, (uint32_t)il); }
#endif
#ifdef BS_REF_BEST
static inline void bs_hkdf_expand_sha256(uint8_t *o, size_t ol, uint8_t *prk, size_t pl, uint8_t *i, size_t il) { EverCrypt_HKDF_expand(Spec_Hash_Definitions_SHA2_256, o, prk, (uint32_t)pl, i, (uint32_t)il, (uint32_t)ol); }
#else
static inline void bs_hkdf_expand_sha256(uint8_t *o, size_t ol, uint8_t *prk, size_t pl, uint8_t *i, size_t il) { Hacl_HKDF_expand_sha2_256(o, prk, (uint32_t)pl, i, (uint32_t)il, (uint32_t)ol); }
#endif

/* ---- stream ciphers / AEAD ---- */
#ifdef BS_REF_BEST
static inline void bs_chacha20(uint8_t *o, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { Hacl_Chacha20_Vec256_chacha20_encrypt_256((uint32_t)n, o, m, k, v, 0); }
#else
static inline void bs_chacha20(uint8_t *o, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { Hacl_Chacha20_chacha20_encrypt((uint32_t)n, o, m, k, v, 0); }
#endif
static inline void bs_salsa20(uint8_t *o, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { Hacl_Salsa20_salsa20_encrypt((uint32_t)n, o, m, k, v, 0); }
#ifdef BS_REF_BEST
static inline void bs_poly1305(uint8_t *o, uint8_t *m, size_t n, uint8_t *k) { Hacl_MAC_Poly1305_Simd256_mac(o, m, (uint32_t)n, k); }
#else
static inline void bs_poly1305(uint8_t *o, uint8_t *m, size_t n, uint8_t *k) { Hacl_MAC_Poly1305_mac(o, m, (uint32_t)n, k); }
#endif
#ifdef BS_REF_BEST
static inline void bs_chachapoly_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) { Hacl_AEAD_Chacha20Poly1305_Simd256_encrypt(c, t, m, (uint32_t)n, a, (uint32_t)al, k, v); }
#else
static inline void bs_chachapoly_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) { Hacl_AEAD_Chacha20Poly1305_encrypt(c, t, m, (uint32_t)n, a, (uint32_t)al, k, v); }
#endif
#ifdef BS_REF_BEST
static inline int bs_chachapoly_dec(uint8_t *m, uint8_t *c, size_t n, uint8_t *t, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) { return Hacl_AEAD_Chacha20Poly1305_Simd256_decrypt(m, c, (uint32_t)n, a, (uint32_t)al, k, v, t) == 0; }
#else
static inline int bs_chachapoly_dec(uint8_t *m, uint8_t *c, size_t n, uint8_t *t, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) { return Hacl_AEAD_Chacha20Poly1305_decrypt(m, c, (uint32_t)n, a, (uint32_t)al, k, v, t) == 0; }
#endif
static inline void bs_secretbox_easy(uint8_t *c, uint8_t *m, size_t n, uint8_t *v, uint8_t *k) { Hacl_NaCl_crypto_secretbox_easy(c, m, (uint32_t)n, v, k); }

/* ---- AES-GCM: EverCrypt, which on this machine dispatches to the Vale
       AES-NI/PCLMULQDQ assembly.  The expanded-key state is built once. ---- */
static EverCrypt_AEAD_state_s *bs_gcm128 = NULL, *bs_gcm256 = NULL;
static inline void bs_aes128gcm_setup(uint8_t *k) { EverCrypt_AEAD_create_in(Spec_Agile_AEAD_AES128_GCM, &bs_gcm128, k); }
static inline void bs_aes256gcm_setup(uint8_t *k) { EverCrypt_AEAD_create_in(Spec_Agile_AEAD_AES256_GCM, &bs_gcm256, k); }
static inline void bs_aes128gcm_enc(uint8_t *ct, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *iv) {
  (void)k;
  EverCrypt_AEAD_encrypt(bs_gcm128, iv, 12, a, (uint32_t)al, m, (uint32_t)n, ct, t);
}
static inline void bs_aes256gcm_enc(uint8_t *ct, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *iv) {
  (void)k;
  EverCrypt_AEAD_encrypt(bs_gcm256, iv, 12, a, (uint32_t)al, m, (uint32_t)n, ct, t);
}
static inline int bs_aes128gcm_dec(uint8_t *m, uint8_t *ct, size_t n, uint8_t *t, uint8_t *a, size_t al, uint8_t *k, uint8_t *iv) {
  (void)k;
  return EverCrypt_AEAD_decrypt(bs_gcm128, iv, 12, a, (uint32_t)al, ct, (uint32_t)n, t, m) == 0;
}

/* ---- Curve25519 / Ed25519 ----
   _51 is the portable C field; _64 additionally uses the BMI2/ADX inline
   assembly, and is what HACL* would really ship on this machine. */
#ifdef BS_REF_BEST
/* Curve25519_64 is the BMI2/ADX inline-asm field; this CPU has both. */
static inline void bs_x25519(uint8_t *o, uint8_t *s, uint8_t *p) { Hacl_Curve25519_64_scalarmult(o, s, p); }
#else
static inline void bs_x25519(uint8_t *o, uint8_t *s, uint8_t *p) { Hacl_Curve25519_51_scalarmult(o, s, p); }
#endif
#ifdef BS_REF_BEST
static inline void bs_x25519_base(uint8_t *o, uint8_t *s) { Hacl_Curve25519_64_secret_to_public(o, s); }
#else
static inline void bs_x25519_base(uint8_t *o, uint8_t *s) { Hacl_Curve25519_51_secret_to_public(o, s); }
#endif
static inline void bs_x25519_64(uint8_t *o, uint8_t *s, uint8_t *p) { Hacl_Curve25519_64_scalarmult(o, s, p); }
static inline void bs_ed25519_keygen(uint8_t *o, uint8_t *s) { Hacl_Ed25519_secret_to_public(o, s); }
static inline void bs_ed25519_sign(uint8_t *sg, uint8_t *sk, uint8_t *m, size_t n) { Hacl_Ed25519_sign(sg, sk, (uint32_t)n, m); }
static inline int bs_ed25519_verify(uint8_t *pk, uint8_t *m, size_t n, uint8_t *sg) { return Hacl_Ed25519_verify(pk, (uint32_t)n, m, sg); }

/* ---- P-256 ---- */
static inline int bs_p256_sign(uint8_t *sg, uint8_t *m, size_t n, uint8_t *sk, uint8_t *nonce) { return Hacl_P256_ecdsa_sign_p256_sha2(sg, (uint32_t)n, m, sk, nonce); }
static inline int bs_p256_verify(uint8_t *m, size_t n, uint8_t *pk, uint8_t *r, uint8_t *s) { return Hacl_P256_ecdsa_verif_p256_sha2((uint32_t)n, m, pk, r, s); }
static inline int bs_p256_dh_i(uint8_t *pk, uint8_t *sk) { return Hacl_P256_dh_initiator(pk, sk); }
static inline int bs_p256_dh_r(uint8_t *ss, uint8_t *pk, uint8_t *sk) { return Hacl_P256_dh_responder(ss, pk, sk); }

/* ---- K-256 ---- */
static inline int bs_k256_sign(uint8_t *sg, uint8_t *h, uint8_t *sk, uint8_t *nonce) { return Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(sg, h, sk, nonce); }
static inline int bs_k256_verify(uint8_t *h, uint8_t *pk, uint8_t *sg) { return Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(h, pk, sg); }
static inline int bs_k256_dh_i(uint8_t *pk, uint8_t *sk) { return Hacl_K256_ECDSA_secret_to_public(pk, sk); }
static inline int bs_k256_dh_r(uint8_t *ss, uint8_t *pk, uint8_t *sk) { return Hacl_K256_ECDSA_ecdh(ss, pk, sk); }

/* ---- RSA-PSS: the byte-level key API, so key loading is inside the call,
       matching what hacl-pulse's entry point does. ---- */
static inline int bs_rsapss_sign(uint32_t modBits, uint8_t *nb, size_t eLen, uint8_t *eb, size_t dLen, uint8_t *db,
                                 size_t sLen, uint8_t *salt, size_t mLen, uint8_t *msg, uint8_t *sgnt) {
  return Hacl_RSAPSS_rsapss_skey_sign(Spec_Hash_Definitions_SHA2_256, modBits, (uint32_t)(8 * eLen), (uint32_t)(8 * dLen),
                                      nb, eb, db, (uint32_t)sLen, salt, (uint32_t)mLen, msg, sgnt);
}
static inline int bs_rsapss_verify(uint32_t modBits, uint8_t *nb, size_t eLen, uint8_t *eb, size_t sLen,
                                   uint8_t *sgnt, size_t mLen, uint8_t *msg) {
  return Hacl_RSAPSS_rsapss_pkey_verify(Spec_Hash_Definitions_SHA2_256, modBits, (uint32_t)(8 * eLen), nb, eb,
                                        (uint32_t)sLen, (uint32_t)(modBits / 8), sgnt, (uint32_t)mLen, msg);
}

/* ---- FFDHE ---- */
static inline void bs_ffdhe2048_pub(uint8_t *pk, uint8_t *sk) { Hacl_FFDHE_ffdhe_secret_to_public(Spec_FFDHE_FFDHE2048, sk, pk); }
static inline int bs_ffdhe2048_ss(uint8_t *ss, uint8_t *sk, uint8_t *pk) { return Hacl_FFDHE_ffdhe_shared_secret(Spec_FFDHE_FFDHE2048, sk, pk, ss) != 0; }

/* ---- HMAC-DRBG ---- */
typedef struct { Hacl_HMAC_DRBG_state st; int made; } bs_drbg;
static inline void bs_drbg_init(bs_drbg *s, uint8_t *e, size_t el, uint8_t *n, size_t nl) {
  if (!s->made) { s->st = Hacl_HMAC_DRBG_create_in(Spec_Hash_Definitions_SHA2_256); s->made = 1; }
  Hacl_HMAC_DRBG_instantiate(Spec_Hash_Definitions_SHA2_256, s->st, (uint32_t)el, e, (uint32_t)nl, n, 0, NULL);
}
static inline int bs_drbg_gen(bs_drbg *s, uint8_t *o, size_t ol) {
  return Hacl_HMAC_DRBG_generate(Spec_Hash_Definitions_SHA2_256, o, s->st, (uint32_t)ol, 0, NULL);
}

/* ---- bignum: 2048-bit constant-time modular exponentiation ----
   32-bit limbs, to match hacl-pulse's limb width, plus the 64-bit limb
   version that HACL* actually uses on a 64-bit target. */
#define BS_BN_LIMBS 64
typedef struct {
  uint32_t n[64], a[64], b[64], res[64];
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *ctx;
  uint64_t n64[32], a64[32], b64[32], res64[32];
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *ctx64;
} bs_bnctx;
static inline void bs_bn_load_be(uint32_t *out, const uint8_t *b, size_t limbs) {
  for (size_t i = 0; i < limbs; i++) {
    const uint8_t *p = b + 4 * (limbs - 1 - i);
    out[i] = ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | p[3];
  }
}
static inline void bs_bn_load_be64(uint64_t *out, const uint8_t *b, size_t limbs) {
  for (size_t i = 0; i < limbs; i++) {
    const uint8_t *p = b + 8 * (limbs - 1 - i);
    uint64_t v = 0;
    for (int j = 0; j < 8; j++) v = (v << 8) | p[j];
    out[i] = v;
  }
}
static inline void bs_bn2048_setup(bs_bnctx *c, uint8_t *nb, uint8_t *ab, uint8_t *bb) {
  bs_bn_load_be(c->n, nb, 64); bs_bn_load_be(c->a, ab, 64); bs_bn_load_be(c->b, bb, 64);
  bs_bn_load_be64(c->n64, nb, 32); bs_bn_load_be64(c->a64, ab, 32); bs_bn_load_be64(c->b64, bb, 32);
  c->ctx = Hacl_Bignum32_mont_ctx_init(64, c->n);
  c->ctx64 = Hacl_Bignum64_mont_ctx_init(32, c->n64);
}
/* The main row must be like-for-like: hacl-pulse's bignum has 64-bit limbs,
   so the reference is Hacl_Bignum64.  Comparing it against Hacl_Bignum32 --
   which is what this used to do -- makes a 1.98x loss look like a 1.43x win. */
#define BS_BN_RES(c) ((uint64_t)(c).res64[0])
static inline void bs_bn2048_modexp(bs_bnctx *c, size_t bBits) {
  Hacl_Bignum64_mod_exp_consttime_precomp(c->ctx64, c->a64, (uint32_t)bBits, c->b64, c->res64);
}
static inline void bs_bn2048_modexp32(bs_bnctx *c, size_t bBits) {
  Hacl_Bignum32_mod_exp_consttime_precomp(c->ctx, c->a, (uint32_t)bBits, c->b, c->res);
}

static inline void bs_global_init(void) { EverCrypt_AutoConfig2_init(); }

#endif
