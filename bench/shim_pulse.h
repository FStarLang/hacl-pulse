/* hacl-pulse side of the benchmark shim. */
#ifndef SHIM_H
#define SHIM_H

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "Hacl.h"

#define IMPL_NAME "pulse"

/* ---- hashes ---- */
static inline void bs_md5(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_MD5_md5(o, m, n); }
static inline void bs_sha1(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA1_sha1(o, m, n); }
static inline void bs_sha256(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA2_sha256(o, m, n); }
static inline void bs_sha512(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA2_sha512(o, m, n); }
static inline void bs_sha3_256(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA3_sha3_256(o, m, n); }
static inline void bs_sha3_512(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA3_sha3_512(o, m, n); }
static inline void bs_shake128(uint8_t *o, size_t ol, uint8_t *m, size_t n) { Hacl_Hash_SHA3_shake128(o, ol, m, n); }
static inline void bs_blake2b(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_Blake2_Named_blake2b_512(o, NULL, 0, m, n); }
static inline void bs_blake2s(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_Blake2_Named_blake2s_256(o, NULL, 0, m, n); }

/* ---- streaming SHA-256 ---- */
typedef struct { uint32_t acc[8]; uint8_t buf[64]; size_t tot; } bs_sha256_state;
static inline void bs_sha256_stream(bs_sha256_state *s, uint8_t *o, uint8_t *m, size_t n, size_t chunk) {
  Hacl_Streaming_SHA2_sha256_init(s->acc, s->buf, &s->tot);
  for (size_t i = 0; i < n; i += chunk) {
    size_t c = n - i < chunk ? n - i : chunk;
    Hacl_Streaming_SHA2_sha256_update(s->acc, s->buf, &s->tot, m + i, c);
  }
  Hacl_Streaming_SHA2_sha256_digest(s->acc, s->buf, &s->tot, o);
}

/* ---- MACs / KDFs ---- */
static inline void bs_hmac_sha256(uint8_t *o, uint8_t *k, size_t kl, uint8_t *m, size_t n) { Hacl_HMAC_hmac_sha256(o, k, kl, m, n); }
static inline void bs_hmac_sha512(uint8_t *o, uint8_t *k, size_t kl, uint8_t *m, size_t n) { Hacl_HMAC_hmac_sha512(o, k, kl, m, n); }
static inline void bs_hkdf_extract_sha256(uint8_t *o, uint8_t *s, size_t sl, uint8_t *i, size_t il) { Hacl_HKDF_extract_sha256(o, s, sl, i, il); }
static inline void bs_hkdf_expand_sha256(uint8_t *o, size_t ol, uint8_t *prk, size_t pl, uint8_t *i, size_t il) { Hacl_HKDF_expand_sha256(o, ol, prk, pl, i, il); }

/* ---- stream ciphers / AEAD ---- */
static inline void bs_chacha20(uint8_t *o, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { Hacl_Chacha20_encrypt(o, m, n, k, v, 0); }
static inline void bs_salsa20(uint8_t *o, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { Hacl_Salsa20_encrypt(o, m, n, k, v, 0); }
static inline void bs_poly1305(uint8_t *o, uint8_t *m, size_t n, uint8_t *k) { Hacl_Poly1305_mac(o, m, n, k); }
static inline void bs_chachapoly_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) { Hacl_Chacha20Poly1305_encrypt(c, t, m, n, a, al, k, v); }
static inline int bs_chachapoly_dec(uint8_t *m, uint8_t *c, size_t n, uint8_t *t, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) { return Hacl_Chacha20Poly1305_decrypt(m, c, n, t, a, al, k, v); }
static inline void bs_secretbox_easy(uint8_t *c, uint8_t *m, size_t n, uint8_t *v, uint8_t *k) { Hacl_NaCl_crypto_secretbox_easy(c, m, n, v, k); }

/* ---- AES-GCM ---- */
/* The reference side encrypts against an EverCrypt_AEAD handle built once by
   bs_aes128gcm_setup, so this side uses the expanded-key entry points, which
   are the same thing: the round keys and the GHASH subkey, built once. */
static uint8_t bs_gcm128_ek[176], bs_gcm128_hk[128];
static uint8_t bs_gcm256_ek[240], bs_gcm256_hk[128];
static inline void bs_aes128gcm_setup(uint8_t *k) { Hacl_AES_GCM_aes128_expand(bs_gcm128_ek, bs_gcm128_hk, k); }
static inline void bs_aes256gcm_setup(uint8_t *k) { Hacl_AES_GCM_aes256_expand(bs_gcm256_ek, bs_gcm256_hk, k); }
static inline void bs_aes128gcm_enc(uint8_t *ct, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *iv) {
  (void)k;
  Hacl_AES_GCM_aes128_encrypt_expanded(ct, t, m, n, bs_gcm128_ek, bs_gcm128_hk, iv, 12, a, al);
}
static inline void bs_aes256gcm_enc(uint8_t *ct, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *iv) {
  (void)k;
  Hacl_AES_GCM_aes256_encrypt_expanded(ct, t, m, n, bs_gcm256_ek, bs_gcm256_hk, iv, 12, a, al);
}
static inline int bs_aes128gcm_dec(uint8_t *m, uint8_t *ct, size_t n, uint8_t *t, uint8_t *a, size_t al, uint8_t *k, uint8_t *iv) {
  (void)k;
  return Hacl_AES_GCM_aes128_decrypt_expanded(m, ct, n, t, bs_gcm128_ek, bs_gcm128_hk, iv, 12, a, al);
}

/* ---- Curve25519 / Ed25519 ---- */
static inline void bs_x25519(uint8_t *o, uint8_t *s, uint8_t *p) { Hacl_Curve25519_scalarmult(o, s, p); }
static inline void bs_x25519_base(uint8_t *o, uint8_t *s) { Hacl_Curve25519_secret_to_public(o, s); }
static inline void bs_ed25519_keygen(uint8_t *o, uint8_t *s) { Hacl_Ed25519_secret_to_public(o, s); }
static inline void bs_ed25519_sign(uint8_t *sg, uint8_t *sk, uint8_t *m, size_t n) { Hacl_Ed25519_sign(sg, sk, m, n); }
static inline int bs_ed25519_verify(uint8_t *pk, uint8_t *m, size_t n, uint8_t *sg) { return Hacl_Ed25519_verify(pk, m, n, sg); }

/* ---- P-256 ---- */
static inline int bs_p256_sign(uint8_t *sg, uint8_t *m, size_t n, uint8_t *sk, uint8_t *nonce) { return Hacl_P256_ecdsa_sign_sha256(sg, m, n, sk, nonce); }
static inline int bs_p256_verify(uint8_t *m, size_t n, uint8_t *pk, uint8_t *r, uint8_t *s) { return Hacl_P256_ecdsa_verify_sha256(m, n, pk, r, s); }
static inline int bs_p256_dh_i(uint8_t *pk, uint8_t *sk) { return Hacl_P256_Ecdh_dh_initiator(pk, sk); }
#define BS_HAVE_P384
static inline int bs_p384_sign(uint8_t *sg, uint8_t *m, size_t n, uint8_t *sk, uint8_t *nonce) { return Hacl_P384_ecdsa_sign_sha384(sg, m, n, sk, nonce); }
static inline int bs_p384_verify(uint8_t *m, size_t n, uint8_t *pk, uint8_t *sg) { return Hacl_P384_ecdsa_verify_sha384(m, n, pk, sg); }
static inline int bs_p384_dh_i(uint8_t *pk, uint8_t *sk) { return Hacl_P384_Ecdh_dh_initiator(pk, sk); }
static inline int bs_p384_dh_r(uint8_t *ss, uint8_t *pk, uint8_t *sk) { return Hacl_P384_Ecdh_dh_responder(ss, pk, sk); }
static inline int bs_p256_dh_r(uint8_t *ss, uint8_t *pk, uint8_t *sk) { return Hacl_P256_Ecdh_dh_responder(ss, pk, sk); }

/* ---- K-256 ---- */
static inline int bs_k256_sign(uint8_t *sg, uint8_t *h, uint8_t *sk, uint8_t *nonce) { return Hacl_K256_ecdsa_sign_hashed_msg(sg, h, sk, nonce); }
static inline int bs_k256_verify(uint8_t *h, uint8_t *pk, uint8_t *sg) { return Hacl_K256_ecdsa_verify_hashed_msg(h, pk, sg, sg + 32); }
static inline int bs_k256_dh_i(uint8_t *pk, uint8_t *sk) { return Hacl_K256_Ecdh_dh_initiator(pk, sk); }
static inline int bs_k256_dh_r(uint8_t *ss, uint8_t *pk, uint8_t *sk) { return Hacl_K256_Ecdh_dh_responder(ss, pk, sk); }

/* ---- RSA-PSS (byte-level key API: key loading is inside the call) ---- */
static inline int bs_rsapss_sign(uint32_t modBits, uint8_t *nb, size_t eLen, uint8_t *eb, size_t dLen, uint8_t *db,
                                 size_t sLen, uint8_t *salt, size_t mLen, uint8_t *msg, uint8_t *sgnt) {
  (void)eLen; (void)eb;
  return Hacl_RSAPSS_sign_sha256(modBits, nb, dLen, db, sLen, salt, mLen, msg, sgnt);
}
static inline int bs_rsapss_verify(uint32_t modBits, uint8_t *nb, size_t eLen, uint8_t *eb, size_t sLen,
                                   uint8_t *sgnt, size_t mLen, uint8_t *msg) {
  return Hacl_RSAPSS_verify_sha256(modBits, nb, eLen, eb, sLen, sgnt, mLen, msg);
}

/* ---- FFDHE ---- */
static inline void bs_ffdhe2048_pub(uint8_t *pk, uint8_t *sk) { Hacl_FFDHE_ffdhe2048_secret_to_public(pk, sk); }
static inline int bs_ffdhe2048_ss(uint8_t *ss, uint8_t *sk, uint8_t *pk) { return Hacl_FFDHE_ffdhe2048_shared_secret(ss, sk, pk); }

/* ---- HMAC-DRBG ---- */
typedef struct { uint8_t k[32], v[32]; size_t ctr; } bs_drbg;
static inline void bs_drbg_init(bs_drbg *s, uint8_t *e, size_t el, uint8_t *n, size_t nl) {
  Hacl_HMAC_DRBG_instantiate_sha256(s->k, s->v, &s->ctr, e, el, n, nl, NULL, 0);
}
static inline int bs_drbg_gen(bs_drbg *s, uint8_t *o, size_t ol) {
  return Hacl_HMAC_DRBG_generate_sha256(o, ol, s->k, s->v, &s->ctr, NULL, 0);
}

/* ---- bignum: 2048-bit constant-time modular exponentiation, 64-bit limbs ---- */
#define BS_BN_LIMBS 32
typedef struct {
  uint64_t n[32], a[32], b[32], r2[32], res[32];
  uint64_t aM[32], acc[32], t[32], wide[64];
  uint64_t mu;
} bs_bnctx;
static inline void bs_bn2048_setup(bs_bnctx *c, uint8_t *nb, uint8_t *ab, uint8_t *bb) {
  Hacl_Bignum_Convert_from_bytes_be(c->n, 32, nb);
  Hacl_Bignum_Convert_from_bytes_be(c->a, 32, ab);
  Hacl_Bignum_Convert_from_bytes_be(c->b, 32, bb);
  c->mu = Hacl_Bignum_Montgomery_mont_mu(c->n[0]);
#ifdef BS_PRECOMP7
  Hacl_Bignum_Montgomery_precomp(c->r2, c->aM, c->t, c->wide, c->n, 32, c->mu);
#else
  Hacl_Bignum_Montgomery_precomp(c->r2, c->n, 32);
#endif
}
#define BS_BN_RES(c) ((uint64_t)(c).res[0])
static inline void bs_bn2048_modexp(bs_bnctx *c, size_t bBits) {
  Hacl_Bignum_Exponentiation_mod_exp_consttime(c->res, c->a, c->b, bBits, c->r2, c->n, 32, c->mu,
                                               c->aM, c->acc, c->t, c->wide);
}

/* ---- ML-KEM ----
   HACL* has no ML-KEM, so there is nothing to compare against and these rows
   exist only on this side of the shim; the README reports them as absolute
   times rather than as a ratio.  They are called directly rather than through
   a function-pointer table because what they are usually measuring is how well
   the parameter sets specialise, and an indirect call would hide exactly that. */
#define BS_HAVE_MLKEM 1
static inline void bs_mlkem512_keypair(uint8_t *ek, uint8_t *dk, uint8_t *d, uint8_t *z) { Hacl_MLKEM512_keypair(ek, dk, d, z); }
static inline void bs_mlkem512_enc(uint8_t *ct, uint8_t *ss, uint8_t *ek, uint8_t *m) { Hacl_MLKEM512_enc(ct, ss, ek, m); }
static inline void bs_mlkem512_dec(uint8_t *ss, uint8_t *ct, uint8_t *dk) { Hacl_MLKEM512_dec(ss, ct, dk); }
static inline void bs_mlkem768_keypair(uint8_t *ek, uint8_t *dk, uint8_t *d, uint8_t *z) { Hacl_MLKEM768_keypair(ek, dk, d, z); }
static inline void bs_mlkem768_enc(uint8_t *ct, uint8_t *ss, uint8_t *ek, uint8_t *m) { Hacl_MLKEM768_enc(ct, ss, ek, m); }
static inline void bs_mlkem768_dec(uint8_t *ss, uint8_t *ct, uint8_t *dk) { Hacl_MLKEM768_dec(ss, ct, dk); }
static inline void bs_mlkem1024_keypair(uint8_t *ek, uint8_t *dk, uint8_t *d, uint8_t *z) { Hacl_MLKEM1024_keypair(ek, dk, d, z); }
static inline void bs_mlkem1024_enc(uint8_t *ct, uint8_t *ss, uint8_t *ek, uint8_t *m) { Hacl_MLKEM1024_enc(ct, ss, ek, m); }
static inline void bs_mlkem1024_dec(uint8_t *ss, uint8_t *ct, uint8_t *dk) { Hacl_MLKEM1024_dec(ss, ct, dk); }

/* ---- ML-DSA ----
   Likewise absent from HACL*, and likewise called directly.  Signing is the
   hedged pure variant with an empty context; its cost depends on the message
   through the number of rejected attempts, so the benchmark fixes one. */
#define BS_HAVE_MLDSA 1
static inline void bs_mldsa44_keypair(uint8_t *pk, uint8_t *sk, uint8_t *xi) { Hacl_MLDSA44_keypair(pk, sk, xi); }
static inline bool bs_mldsa44_sign(uint8_t *sg, uint8_t *sk, uint8_t *m, size_t ml, uint8_t *rnd) { return Hacl_MLDSA44_sign(sg, sk, m, ml, NULL, 0, rnd); }
static inline bool bs_mldsa44_verify(uint8_t *pk, uint8_t *m, size_t ml, uint8_t *sg) { return Hacl_MLDSA44_verify(pk, m, ml, NULL, 0, sg); }
static inline void bs_mldsa65_keypair(uint8_t *pk, uint8_t *sk, uint8_t *xi) { Hacl_MLDSA65_keypair(pk, sk, xi); }
static inline bool bs_mldsa65_sign(uint8_t *sg, uint8_t *sk, uint8_t *m, size_t ml, uint8_t *rnd) { return Hacl_MLDSA65_sign(sg, sk, m, ml, NULL, 0, rnd); }
static inline bool bs_mldsa65_verify(uint8_t *pk, uint8_t *m, size_t ml, uint8_t *sg) { return Hacl_MLDSA65_verify(pk, m, ml, NULL, 0, sg); }
static inline void bs_mldsa87_keypair(uint8_t *pk, uint8_t *sk, uint8_t *xi) { Hacl_MLDSA87_keypair(pk, sk, xi); }
static inline bool bs_mldsa87_sign(uint8_t *sg, uint8_t *sk, uint8_t *m, size_t ml, uint8_t *rnd) { return Hacl_MLDSA87_sign(sg, sk, m, ml, NULL, 0, rnd); }
static inline bool bs_mldsa87_verify(uint8_t *pk, uint8_t *m, size_t ml, uint8_t *sg) { return Hacl_MLDSA87_verify(pk, m, ml, NULL, 0, sg); }

static inline void bs_global_init(void) {}

#endif
