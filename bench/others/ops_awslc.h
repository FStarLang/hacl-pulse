/* AWS-LC, through the direct BoringSSL-family APIs (one-shot digests,
 * CRYPTO_chacha_20, EVP_AEAD, X25519(), ED25519_sign, EC_KEY, RSA, DH),
 * which is how code written against AWS-LC calls it. */
#include <openssl/aead.h>
#include <openssl/blake2.h>
#include <openssl/bn.h>
#include <openssl/chacha.h>
#include <openssl/curve25519.h>
#include <openssl/dh.h>
#include <openssl/digest.h>
#include <openssl/ec.h>
#include <openssl/ec_key.h>
#include <openssl/ecdh.h>
#include <openssl/ecdsa.h>
#include <openssl/evp.h>
#include <openssl/hmac.h>
#include <openssl/md5.h>
#include <openssl/nid.h>
#include <openssl/poly1305.h>
#include <openssl/rsa.h>
#include <openssl/sha.h>

#define IMPL_NAME "awslc"

static void al_die(const char *w) { fprintf(stderr, "aws-lc: %s failed\n", w); exit(1); }

static EVP_MD_CTX *al_mdctx;
static EVP_AEAD_CTX al_cp;
static void bo_init(void) { al_mdctx = EVP_MD_CTX_new(); }

#define BO_MD5
static inline void bo_md5(uint8_t *o, uint8_t *m, size_t n) { MD5(m, n, o); }
#define BO_SHA1
static inline void bo_sha1(uint8_t *o, uint8_t *m, size_t n) { SHA1(m, n, o); }
#define BO_SHA256
static inline void bo_sha256(uint8_t *o, uint8_t *m, size_t n) { SHA256(m, n, o); }
#define BO_SHA512
static inline void bo_sha512(uint8_t *o, uint8_t *m, size_t n) { SHA512(m, n, o); }
#define BO_SHA3_256
static inline void bo_sha3_256(uint8_t *o, uint8_t *m, size_t n) {
  EVP_DigestInit_ex(al_mdctx, EVP_sha3_256(), NULL);
  EVP_DigestUpdate(al_mdctx, m, n);
  EVP_DigestFinal_ex(al_mdctx, o, NULL);
}
#define BO_SHAKE128
static inline void bo_shake128(uint8_t *o, size_t ol, uint8_t *m, size_t n) {
  EVP_DigestInit_ex(al_mdctx, EVP_shake128(), NULL);
  EVP_DigestUpdate(al_mdctx, m, n);
  EVP_DigestFinalXOF(al_mdctx, o, ol);
}
/* AWS-LC has BLAKE2b only with a 256-bit output, and no BLAKE2s, so it has
   no BLAKE2 rows here. */

#define BO_HMAC256
static inline void bo_hmac256(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) { unsigned l; HMAC(EVP_sha256(), k, 32, m, n, o, &l); }
#define BO_HMAC512
static inline void bo_hmac512(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) { unsigned l; HMAC(EVP_sha512(), k, 32, m, n, o, &l); }
#define BO_POLY1305
static inline void bo_poly1305(uint8_t *o, uint8_t *m, size_t n, uint8_t *k) {
  poly1305_state st;
  CRYPTO_poly1305_init(&st, k);
  CRYPTO_poly1305_update(&st, m, n);
  CRYPTO_poly1305_finish(&st, o);
}

#define BO_CHACHA20
static inline void bo_chacha20(uint8_t *c, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { CRYPTO_chacha_20(c, m, n, k, v, 0); }
/* EVP_AEAD contexts hold the key, so the ChaCha20-Poly1305 one is rebuilt
   only when the key changes (never, in this driver). */
static uint8_t al_cp_key[32];
static int al_cp_init;
#define BO_CHACHAPOLY
static inline void bo_chachapoly(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) {
  if (!al_cp_init || memcmp(k, al_cp_key, 32)) {
    if (al_cp_init) EVP_AEAD_CTX_cleanup(&al_cp);
    if (!EVP_AEAD_CTX_init(&al_cp, EVP_aead_chacha20_poly1305(), k, 32, 16, NULL)) al_die("chachapoly init");
    memcpy(al_cp_key, k, 32);
    al_cp_init = 1;
  }
  size_t tl;
  EVP_AEAD_CTX_seal_scatter(&al_cp, c, t, &tl, 16, v, 12, m, n, NULL, 0, a, al);
}

static EVP_AEAD_CTX al_gcm128, al_gcm256;
#define BO_AES128GCM
static inline void bo_aes128gcm_setup(uint8_t *k) {
  if (!EVP_AEAD_CTX_init(&al_gcm128, EVP_aead_aes_128_gcm(), k, 16, 16, NULL)) al_die("gcm128 init");
}
static inline void bo_aes128gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) {
  size_t tl;
  EVP_AEAD_CTX_seal_scatter(&al_gcm128, c, t, &tl, 16, iv, 12, m, n, NULL, 0, a, al);
}
#define BO_AES256GCM
static inline void bo_aes256gcm_setup(uint8_t *k) {
  if (!EVP_AEAD_CTX_init(&al_gcm256, EVP_aead_aes_256_gcm(), k, 32, 16, NULL)) al_die("gcm256 init");
}
static inline void bo_aes256gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) {
  size_t tl;
  EVP_AEAD_CTX_seal_scatter(&al_gcm256, c, t, &tl, 16, iv, 12, m, n, NULL, 0, a, al);
}

#define BO_X25519
static inline void bo_x25519(uint8_t *o, uint8_t *s, uint8_t *p) { X25519(o, s, p); }

static uint8_t al_ed_sk[64];
#define BO_ED25519_SIGN
static inline void bo_ed25519_setup(uint8_t *seed) {
  uint8_t pk[32];
  ED25519_keypair_from_seed(pk, al_ed_sk, seed);
}
static inline void bo_ed25519_sign(uint8_t *sg, uint8_t *m, size_t n) { ED25519_sign(sg, m, n, al_ed_sk); }
#define BO_ED25519_VERIFY
static inline int bo_ed25519_verify(uint8_t *pk, uint8_t *m, size_t n, uint8_t *sg) { return ED25519_verify(m, n, sg, pk); }

static EC_POINT *al_point(const EC_GROUP *g, uint8_t *raw) {
  uint8_t pt[65];
  pt[0] = 4;
  memcpy(pt + 1, raw, 64);
  EC_POINT *p = EC_POINT_new(g);
  if (!EC_POINT_oct2point(g, p, pt, 65, NULL)) al_die("ec point");
  return p;
}
static EC_KEY *al_ec_key(int nid, uint8_t *sk) {
  EC_KEY *k = EC_KEY_new_by_curve_name(nid);
  BIGNUM *d = BN_bin2bn(sk, 32, NULL);
  EC_POINT *q = EC_POINT_new(EC_KEY_get0_group(k));
  EC_POINT_mul(EC_KEY_get0_group(k), q, d, NULL, NULL, NULL);
  if (!EC_KEY_set_private_key(k, d) || !EC_KEY_set_public_key(k, q)) al_die("ec key");
  return k;
}
static int al_sig_raw(uint8_t *sg, ECDSA_SIG *s) {
  if (!s) return 0;
  const BIGNUM *r, *ss;
  ECDSA_SIG_get0(s, &r, &ss);
  BN_bn2bin_padded(sg, 32, r);
  BN_bn2bin_padded(sg + 32, 32, ss);
  ECDSA_SIG_free(s);
  return 1;
}

static EC_KEY *al_p256;
static EC_POINT *al_p256_peer;
#define BO_P256_ECDH
#define BO_P256_SIGN
#define BO_P256_VERIFY
static inline void bo_p256_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) {
  (void)pk;
  al_p256 = al_ec_key(NID_X9_62_prime256v1, sk);
  al_p256_peer = al_point(EC_KEY_get0_group(al_p256), peer);
}
static inline int bo_p256_ecdh(uint8_t *ss) { return ECDH_compute_key(ss, 32, al_p256_peer, al_p256, NULL) == 32; }
static inline int bo_p256_sign(uint8_t *sg, uint8_t *m, size_t n) {
  uint8_t h[32];
  SHA256(m, n, h);
  return al_sig_raw(sg, ECDSA_do_sign(h, 32, al_p256));
}
static inline int bo_p256_verify(uint8_t *m, size_t n, uint8_t *sg) {
  uint8_t h[32];
  SHA256(m, n, h);
  ECDSA_SIG *s = ECDSA_SIG_new();
  ECDSA_SIG_set0(s, BN_bin2bn(sg, 32, NULL), BN_bin2bn(sg + 32, 32, NULL));
  int r = ECDSA_do_verify(h, 32, s, al_p256);
  ECDSA_SIG_free(s);
  return r == 1;
}

static EC_KEY *al_p384;
static EC_POINT *al_p384_peer;
#define BO_P384_ECDH
#define BO_P384_SIGN
#define BO_P384_VERIFY
static inline void bo_p384_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) {
  (void)pk;
  al_p384 = EC_KEY_new_by_curve_name(NID_secp384r1);
  const EC_GROUP *g = EC_KEY_get0_group(al_p384);
  BIGNUM *d = BN_bin2bn(sk, 48, NULL);
  EC_POINT *q = EC_POINT_new(g);
  EC_POINT_mul(g, q, d, NULL, NULL, NULL);
  if (!EC_KEY_set_private_key(al_p384, d) || !EC_KEY_set_public_key(al_p384, q)) al_die("p384 key");
  uint8_t pt[97];
  pt[0] = 4;
  memcpy(pt + 1, peer, 96);
  al_p384_peer = EC_POINT_new(g);
  if (!EC_POINT_oct2point(g, al_p384_peer, pt, 97, NULL)) al_die("p384 point");
}
static inline int bo_p384_ecdh(uint8_t *ss) { return ECDH_compute_key(ss, 48, al_p384_peer, al_p384, NULL) == 48; }
static inline int bo_p384_sign(uint8_t *sg, uint8_t *m, size_t n) {
  uint8_t h[48];
  SHA384(m, n, h);
  ECDSA_SIG *s = ECDSA_do_sign(h, 48, al_p384);
  if (!s) return 0;
  const BIGNUM *r, *ss;
  ECDSA_SIG_get0(s, &r, &ss);
  BN_bn2bin_padded(sg, 48, r);
  BN_bn2bin_padded(sg + 48, 48, ss);
  ECDSA_SIG_free(s);
  return 1;
}
static inline int bo_p384_verify(uint8_t *m, size_t n, uint8_t *sg) {
  uint8_t h[48];
  SHA384(m, n, h);
  ECDSA_SIG *s = ECDSA_SIG_new();
  ECDSA_SIG_set0(s, BN_bin2bn(sg, 48, NULL), BN_bin2bn(sg + 48, 48, NULL));
  int r = ECDSA_do_verify(h, 48, s, al_p384);
  ECDSA_SIG_free(s);
  return r == 1;
}

static EC_KEY *al_k256;
#define BO_K256_SIGN
static inline void bo_k256_setup(uint8_t *sk) { al_k256 = al_ec_key(NID_secp256k1, sk); }
static inline int bo_k256_sign(uint8_t *sg, uint8_t *h) { return al_sig_raw(sg, ECDSA_do_sign(h, 32, al_k256)); }

/* n, e, d only: one full-size exponentiation, as in hacl-pulse. */
static RSA *al_rsa;
#define BO_RSA
static inline void bo_rsa_setup(uint8_t *n, uint8_t *e, size_t el, uint8_t *d) {
  al_rsa = RSA_new_private_key_no_crt(BN_bin2bn(n, 256, NULL), BN_bin2bn(e, el, NULL), BN_bin2bn(d, 256, NULL));
  if (!al_rsa) al_die("rsa key");
}
static inline int bo_rsa_sign(uint8_t *sg, uint8_t *m, size_t ml) {
  uint8_t h[32];
  size_t l;
  SHA256(m, ml, h);
  return RSA_sign_pss_mgf1(al_rsa, &l, sg, 256, h, 32, EVP_sha256(), NULL, 0);
}
static inline int bo_rsa_verify(uint8_t *sg, uint8_t *m, size_t ml) {
  uint8_t h[32];
  SHA256(m, ml, h);
  return RSA_verify_pss_mgf1(al_rsa, h, 32, EVP_sha256(), NULL, 0, sg, 256);
}

static DH *al_dh;
static BIGNUM *al_dh_peer;
#define BO_FFDHE
static inline void bo_ffdhe_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) {
  al_dh = DH_get_rfc7919_2048();
  if (!DH_set0_key(al_dh, BN_bin2bn(pk, 256, NULL), BN_bin2bn(sk, 256, NULL))) al_die("dh key");
  al_dh_peer = BN_bin2bn(peer, 256, NULL);
}
static inline int bo_ffdhe_ss(uint8_t *ss) { return DH_compute_key_padded(ss, al_dh_peer, al_dh) == 256; }

static EVP_PKEY_CTX *al_kem_gen, *al_kem_enc, *al_kem_dec;
#define BO_MLKEM768
static inline void bo_mlkem768_setup(uint8_t *ek, uint8_t *dk) {
  EVP_PKEY *pub = EVP_PKEY_kem_new_raw_public_key(NID_MLKEM768, ek, 1184);
  EVP_PKEY *prv = EVP_PKEY_kem_new_raw_secret_key(NID_MLKEM768, dk, 2400);
  if (!pub || !prv) al_die("ml-kem import");
  al_kem_enc = EVP_PKEY_CTX_new(pub, NULL);
  al_kem_dec = EVP_PKEY_CTX_new(prv, NULL);
  al_kem_gen = EVP_PKEY_CTX_new_id(EVP_PKEY_KEM, NULL);
  if (!EVP_PKEY_CTX_kem_set_params(al_kem_gen, NID_MLKEM768) || !EVP_PKEY_keygen_init(al_kem_gen)) al_die("ml-kem init");
}
static inline void bo_mlkem768_keygen(void) {
  EVP_PKEY *k = NULL;
  EVP_PKEY_keygen(al_kem_gen, &k);
  EVP_PKEY_free(k);
}
static inline void bo_mlkem768_enc(uint8_t *ct, uint8_t *ss) {
  size_t cl = 1088, sl = 32;
  EVP_PKEY_encapsulate(al_kem_enc, ct, &cl, ss, &sl);
}
static inline void bo_mlkem768_dec(uint8_t *ss, uint8_t *ct) {
  size_t sl = 32;
  EVP_PKEY_decapsulate(al_kem_dec, ss, &sl, ct, 1088);
}

/* ML-DSA: key generation from a seed (EVP_PKEY_pqdsa_new_raw_private_key
   expands a 32-byte seed into a key pair), the public key read back out.
   AWS-LC's EVP signs hedged, with fresh randomness and an empty context, so
   its signatures are checked by hacl-pulse rather than byte for byte (the
   per-signature RAND_bytes is part of what is timed). */
#define BO_MLDSA_HEDGED
#define AL_MLDSA(P_, PK_, SK_, SG_)                                              \
  static EVP_PKEY *al_dsa##P_##_prv, *al_dsa##P_##_pub;                          \
  static EVP_MD_CTX *al_dsa##P_##_md;                                            \
  static inline void bo_mldsa##P_##_keygen(uint8_t *pk, uint8_t *xi) {          \
    EVP_PKEY *k = EVP_PKEY_pqdsa_new_raw_private_key(NID_MLDSA##P_, xi, 32);     \
    size_t l = PK_;                                                              \
    if (!k || !EVP_PKEY_get_raw_public_key(k, pk, &l)) al_die("ml-dsa keygen");  \
    EVP_PKEY_free(k);                                                            \
  }                                                                              \
  static inline void bo_mldsa##P_##_setup(uint8_t *pk, uint8_t *sk) {           \
    al_dsa##P_##_pub = EVP_PKEY_pqdsa_new_raw_public_key(NID_MLDSA##P_, pk, PK_); \
    al_dsa##P_##_prv = EVP_PKEY_pqdsa_new_raw_private_key(NID_MLDSA##P_, sk, SK_); \
    al_dsa##P_##_md = EVP_MD_CTX_new();                                          \
    if (!al_dsa##P_##_pub || !al_dsa##P_##_prv) al_die("ml-dsa import");         \
  }                                                                              \
  static inline int bo_mldsa##P_##_sign(uint8_t *sg, uint8_t *m, size_t n) {     \
    size_t l = SG_;                                                              \
    return EVP_DigestSignInit(al_dsa##P_##_md, NULL, NULL, NULL, al_dsa##P_##_prv) == 1 && \
           EVP_DigestSign(al_dsa##P_##_md, sg, &l, m, n) == 1;                   \
  }                                                                              \
  static inline int bo_mldsa##P_##_verify(uint8_t *m, size_t n, uint8_t *sg) {   \
    return EVP_DigestVerifyInit(al_dsa##P_##_md, NULL, NULL, NULL, al_dsa##P_##_pub) == 1 && \
           EVP_DigestVerify(al_dsa##P_##_md, sg, SG_, m, n) == 1;                \
  }
#define BO_MLDSA44
#define BO_MLDSA65
#define BO_MLDSA87
AL_MLDSA(44, 1312, 2560, 2420)
AL_MLDSA(65, 1952, 4032, 3309)
AL_MLDSA(87, 2592, 4896, 4627)
