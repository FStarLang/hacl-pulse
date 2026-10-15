/* OpenSSL 3.x, through EVP, with every algorithm fetched and every key
 * loaded once outside the timed region.  (AWS-LC has its own header,
 * ops_awslc.h, using the direct APIs BoringSSL-family code calls.) */
#include <openssl/core_names.h>
#include <openssl/evp.h>
#include <openssl/kdf.h>
#include <openssl/params.h>
#include <openssl/param_build.h>
#include <openssl/bn.h>
#include <openssl/ec.h>
#include <openssl/rsa.h>
#include <openssl/dh.h>

#ifndef IMPL_NAME
#define IMPL_NAME "openssl"
#endif

static EVP_MD *os_md5, *os_sha1, *os_sha256, *os_sha512, *os_sha3, *os_shake, *os_b2b, *os_b2s;
static EVP_MD_CTX *os_mdctx;
static EVP_MAC_CTX *os_hmac256, *os_hmac512, *os_poly;
static EVP_CIPHER_CTX *os_chacha, *os_cp, *os_gcm128, *os_gcm256;

static void os_die(const char *w) { fprintf(stderr, "openssl: %s failed\n", w); exit(1); }

static void bo_init(void) {
  os_md5 = EVP_MD_fetch(NULL, "MD5", NULL);
  os_sha1 = EVP_MD_fetch(NULL, "SHA1", NULL);
  os_sha256 = EVP_MD_fetch(NULL, "SHA256", NULL);
  os_sha512 = EVP_MD_fetch(NULL, "SHA512", NULL);
  os_sha3 = EVP_MD_fetch(NULL, "SHA3-256", NULL);
  os_shake = EVP_MD_fetch(NULL, "SHAKE128", NULL);
  os_b2b = EVP_MD_fetch(NULL, "BLAKE2B-512", NULL);
  os_b2s = EVP_MD_fetch(NULL, "BLAKE2S-256", NULL);
  os_mdctx = EVP_MD_CTX_new();
  EVP_MAC *hmac = EVP_MAC_fetch(NULL, "HMAC", NULL), *poly = EVP_MAC_fetch(NULL, "POLY1305", NULL);
  os_hmac256 = EVP_MAC_CTX_new(hmac);
  os_hmac512 = EVP_MAC_CTX_new(hmac);
  OSSL_PARAM p256[] = {OSSL_PARAM_construct_utf8_string("digest", "SHA256", 0), OSSL_PARAM_construct_end()};
  OSSL_PARAM p512[] = {OSSL_PARAM_construct_utf8_string("digest", "SHA512", 0), OSSL_PARAM_construct_end()};
  EVP_MAC_CTX_set_params(os_hmac256, p256);
  EVP_MAC_CTX_set_params(os_hmac512, p512);
  os_poly = EVP_MAC_CTX_new(poly);
  os_chacha = EVP_CIPHER_CTX_new();
  EVP_EncryptInit_ex2(os_chacha, EVP_CIPHER_fetch(NULL, "ChaCha20", NULL), NULL, NULL, NULL);
  os_cp = EVP_CIPHER_CTX_new();
  EVP_EncryptInit_ex2(os_cp, EVP_CIPHER_fetch(NULL, "ChaCha20-Poly1305", NULL), NULL, NULL, NULL);
  if (!os_md5 || !os_sha3 || !os_shake || !os_b2b || !os_b2s || !os_poly) os_die("fetch");
}

static inline void os_digest(EVP_MD *md, uint8_t *o, uint8_t *m, size_t n) {
  EVP_DigestInit_ex2(os_mdctx, md, NULL);
  EVP_DigestUpdate(os_mdctx, m, n);
  EVP_DigestFinal_ex(os_mdctx, o, NULL);
}
#define BO_MD5
static inline void bo_md5(uint8_t *o, uint8_t *m, size_t n) { os_digest(os_md5, o, m, n); }
#define BO_SHA1
static inline void bo_sha1(uint8_t *o, uint8_t *m, size_t n) { os_digest(os_sha1, o, m, n); }
#define BO_SHA256
static inline void bo_sha256(uint8_t *o, uint8_t *m, size_t n) { os_digest(os_sha256, o, m, n); }
#define BO_SHA512
static inline void bo_sha512(uint8_t *o, uint8_t *m, size_t n) { os_digest(os_sha512, o, m, n); }
#define BO_SHA3_256
static inline void bo_sha3_256(uint8_t *o, uint8_t *m, size_t n) { os_digest(os_sha3, o, m, n); }
#define BO_SHAKE128
static inline void bo_shake128(uint8_t *o, size_t ol, uint8_t *m, size_t n) {
  EVP_DigestInit_ex2(os_mdctx, os_shake, NULL);
  EVP_DigestUpdate(os_mdctx, m, n);
  EVP_DigestFinalXOF(os_mdctx, o, ol);
}
#define BO_BLAKE2B
static inline void bo_blake2b(uint8_t *o, uint8_t *m, size_t n) { os_digest(os_b2b, o, m, n); }
#define BO_BLAKE2S
static inline void bo_blake2s(uint8_t *o, uint8_t *m, size_t n) { os_digest(os_b2s, o, m, n); }

static inline void os_mac(EVP_MAC_CTX *c, uint8_t *o, size_t ol, uint8_t *k, uint8_t *m, size_t n) {
  size_t l;
  EVP_MAC_init(c, k, 32, NULL);
  EVP_MAC_update(c, m, n);
  EVP_MAC_final(c, o, &l, ol);
}
#define BO_HMAC256
static inline void bo_hmac256(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) { os_mac(os_hmac256, o, 32, k, m, n); }
#define BO_HMAC512
static inline void bo_hmac512(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) { os_mac(os_hmac512, o, 64, k, m, n); }
#define BO_POLY1305
static inline void bo_poly1305(uint8_t *o, uint8_t *m, size_t n, uint8_t *k) { os_mac(os_poly, o, 16, k, m, n); }

#define BO_CHACHA20
static inline void bo_chacha20(uint8_t *c, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) {
  uint8_t iv[16] = {0};               /* 32-bit little-endian counter, then the nonce */
  memcpy(iv + 4, v, 12);
  int l;
  EVP_EncryptInit_ex2(os_chacha, NULL, k, iv, NULL);
  EVP_EncryptUpdate(os_chacha, c, &l, m, (int)n);
}
#define BO_CHACHAPOLY
static inline void bo_chachapoly(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) {
  int l;
  EVP_EncryptInit_ex2(os_cp, NULL, k, v, NULL);
  EVP_EncryptUpdate(os_cp, NULL, &l, a, (int)al);
  EVP_EncryptUpdate(os_cp, c, &l, m, (int)n);
  EVP_EncryptFinal_ex(os_cp, c + l, &l);
  EVP_CIPHER_CTX_ctrl(os_cp, EVP_CTRL_AEAD_GET_TAG, 16, t);
}

static inline void os_gcm_enc(EVP_CIPHER_CTX *x, uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) {
  int l;
  EVP_EncryptInit_ex2(x, NULL, NULL, iv, NULL);
  EVP_EncryptUpdate(x, NULL, &l, a, (int)al);
  EVP_EncryptUpdate(x, c, &l, m, (int)n);
  EVP_EncryptFinal_ex(x, c + l, &l);
  EVP_CIPHER_CTX_ctrl(x, EVP_CTRL_AEAD_GET_TAG, 16, t);
}
#define BO_AES128GCM
static inline void bo_aes128gcm_setup(uint8_t *k) {
  os_gcm128 = EVP_CIPHER_CTX_new();
  EVP_EncryptInit_ex2(os_gcm128, EVP_CIPHER_fetch(NULL, "AES-128-GCM", NULL), k, NULL, NULL);
}
static inline void bo_aes128gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) { os_gcm_enc(os_gcm128, c, t, m, n, a, al, iv); }
#define BO_AES256GCM
static inline void bo_aes256gcm_setup(uint8_t *k) {
  os_gcm256 = EVP_CIPHER_CTX_new();
  EVP_EncryptInit_ex2(os_gcm256, EVP_CIPHER_fetch(NULL, "AES-256-GCM", NULL), k, NULL, NULL);
}
static inline void bo_aes256gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) { os_gcm_enc(os_gcm256, c, t, m, n, a, al, iv); }

/* X25519: the derive context is set up once per (key, peer) pair, which is
   the cheapest way EVP offers to repeat a scalar multiplication. */
static EVP_PKEY_CTX *os_x_ctx;
static uint8_t os_x_sk[32], os_x_pk[32];
#define BO_X25519
static inline void bo_x25519(uint8_t *o, uint8_t *s, uint8_t *p) {
  if (!os_x_ctx || memcmp(s, os_x_sk, 32) || memcmp(p, os_x_pk, 32)) {
    EVP_PKEY *k = EVP_PKEY_new_raw_private_key(EVP_PKEY_X25519, NULL, s, 32);
    EVP_PKEY *q = EVP_PKEY_new_raw_public_key(EVP_PKEY_X25519, NULL, p, 32);
    os_x_ctx = EVP_PKEY_CTX_new(k, NULL);
    if (EVP_PKEY_derive_init(os_x_ctx) <= 0 || EVP_PKEY_derive_set_peer(os_x_ctx, q) <= 0) os_die("x25519 setup");
    memcpy(os_x_sk, s, 32); memcpy(os_x_pk, p, 32);
  }
  size_t l = 32;
  EVP_PKEY_derive(os_x_ctx, o, &l);
}

static EVP_PKEY *os_ed;
static EVP_MD_CTX *os_edctx;
#define BO_ED25519_SIGN
static inline void bo_ed25519_setup(uint8_t *seed) {
  os_ed = EVP_PKEY_new_raw_private_key(EVP_PKEY_ED25519, NULL, seed, 32);
  os_edctx = EVP_MD_CTX_new();
}
static inline void bo_ed25519_sign(uint8_t *sg, uint8_t *m, size_t n) {
  size_t l = 64;
  EVP_DigestSignInit_ex(os_edctx, NULL, NULL, NULL, NULL, os_ed, NULL);
  EVP_DigestSign(os_edctx, sg, &l, m, n);
}
static EVP_PKEY *os_edpub;
static uint8_t os_edpub_b[32];
#define BO_ED25519_VERIFY
static inline int bo_ed25519_verify(uint8_t *pk, uint8_t *m, size_t n, uint8_t *sg) {
  if (!os_edpub || memcmp(pk, os_edpub_b, 32)) {
    os_edpub = EVP_PKEY_new_raw_public_key(EVP_PKEY_ED25519, NULL, pk, 32);
    memcpy(os_edpub_b, pk, 32);
    if (!os_edctx) os_edctx = EVP_MD_CTX_new();
  }
  EVP_DigestVerifyInit_ex(os_edctx, NULL, NULL, NULL, NULL, os_edpub, NULL);
  return EVP_DigestVerify(os_edctx, sg, 64, m, n) == 1;
}

/* An EC key from a raw scalar and a raw (x || y) public point. */
static EVP_PKEY *os_ec_key(const char *group, uint8_t *sk, uint8_t *pk) {
  uint8_t pt[65];
  pt[0] = 4;
  memcpy(pt + 1, pk, 64);
  OSSL_PARAM_BLD *b = OSSL_PARAM_BLD_new();
  OSSL_PARAM_BLD_push_utf8_string(b, OSSL_PKEY_PARAM_GROUP_NAME, group, 0);
  OSSL_PARAM_BLD_push_octet_string(b, OSSL_PKEY_PARAM_PUB_KEY, pt, 65);
  BIGNUM *d = NULL;
  if (sk) {
    d = BN_bin2bn(sk, 32, NULL);
    OSSL_PARAM_BLD_push_BN(b, OSSL_PKEY_PARAM_PRIV_KEY, d);
  }
  OSSL_PARAM *ps = OSSL_PARAM_BLD_to_param(b);
  EVP_PKEY_CTX *c = EVP_PKEY_CTX_new_from_name(NULL, "EC", NULL);
  EVP_PKEY *k = NULL;
  if (EVP_PKEY_fromdata_init(c) <= 0 ||
      EVP_PKEY_fromdata(c, &k, sk ? EVP_PKEY_KEYPAIR : EVP_PKEY_PUBLIC_KEY, ps) <= 0) os_die("ec key");
  return k;
}

/* DER ECDSA-Sig-Value <-> raw r || s */
static int os_der_to_raw(uint8_t *raw, const uint8_t *der, size_t dl) {
  ECDSA_SIG *s = d2i_ECDSA_SIG(NULL, &der, (long)dl);
  if (!s) return 0;
  BN_bn2binpad(ECDSA_SIG_get0_r(s), raw, 32);
  BN_bn2binpad(ECDSA_SIG_get0_s(s), raw + 32, 32);
  ECDSA_SIG_free(s);
  return 1;
}
static size_t os_raw_to_der(uint8_t *der, const uint8_t *raw) {
  ECDSA_SIG *s = ECDSA_SIG_new();
  ECDSA_SIG_set0(s, BN_bin2bn(raw, 32, NULL), BN_bin2bn(raw + 32, 32, NULL));
  uint8_t *p = der;
  size_t l = (size_t)i2d_ECDSA_SIG(s, &p);
  ECDSA_SIG_free(s);
  return l;
}

static EVP_PKEY *os_p256, *os_p256_pub;
static EVP_PKEY_CTX *os_p256_dh;
static EVP_MD_CTX *os_p256_md;
#define BO_P256_ECDH
#define BO_P256_SIGN
#define BO_P256_VERIFY
static inline void bo_p256_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) {
  os_p256 = os_ec_key("P-256", sk, pk);
  os_p256_pub = os_ec_key("P-256", NULL, pk);
  EVP_PKEY *q = os_ec_key("P-256", NULL, peer);
  os_p256_dh = EVP_PKEY_CTX_new(os_p256, NULL);
  if (EVP_PKEY_derive_init(os_p256_dh) <= 0 || EVP_PKEY_derive_set_peer(os_p256_dh, q) <= 0) os_die("p256 derive");
  os_p256_md = EVP_MD_CTX_new();
}
static inline int bo_p256_ecdh(uint8_t *ss) { size_t l = 32; return EVP_PKEY_derive(os_p256_dh, ss, &l) == 1; }
static inline int bo_p256_sign(uint8_t *sg, uint8_t *m, size_t n) {
  uint8_t der[80];
  size_t l = sizeof der;
  EVP_DigestSignInit_ex(os_p256_md, NULL, "SHA256", NULL, NULL, os_p256, NULL);
  if (EVP_DigestSign(os_p256_md, der, &l, m, n) != 1) return 0;
  return os_der_to_raw(sg, der, l);
}
static inline int bo_p256_verify(uint8_t *m, size_t n, uint8_t *sg) {
  uint8_t der[80];
  size_t l = os_raw_to_der(der, sg);
  EVP_DigestVerifyInit_ex(os_p256_md, NULL, "SHA256", NULL, NULL, os_p256_pub, NULL);
  return EVP_DigestVerify(os_p256_md, der, l, m, n) == 1;
}

static EVP_PKEY_CTX *os_k256;
#define BO_K256_SIGN
static inline void bo_k256_setup(uint8_t *sk) {
  /* the public point is required by fromdata; derive it with hacl-pulse */
  uint8_t pk[64];
  Hacl_K256_Ecdh_dh_initiator(pk, sk);
  os_k256 = EVP_PKEY_CTX_new(os_ec_key("secp256k1", sk, pk), NULL);
  if (EVP_PKEY_sign_init(os_k256) <= 0) os_die("k256 sign init");
}
static inline int bo_k256_sign(uint8_t *sg, uint8_t *h) {
  uint8_t der[80];
  size_t l = sizeof der;
  if (EVP_PKEY_sign(os_k256, der, &l, h, 32) != 1) return 0;
  return os_der_to_raw(sg, der, l);
}

/* RSA from n, e, d only, so that OpenSSL, like hacl-pulse, signs with one
   full-size exponentiation rather than with CRT.  OpenSSL still blinds. */
static EVP_PKEY *os_rsa;
static EVP_MD_CTX *os_rsa_md;
#define BO_RSA
static inline void bo_rsa_setup(uint8_t *n, uint8_t *e, size_t el, uint8_t *d) {
  OSSL_PARAM_BLD *b = OSSL_PARAM_BLD_new();
  OSSL_PARAM_BLD_push_BN(b, OSSL_PKEY_PARAM_RSA_N, BN_bin2bn(n, 256, NULL));
  OSSL_PARAM_BLD_push_BN(b, OSSL_PKEY_PARAM_RSA_E, BN_bin2bn(e, (int)el, NULL));
  OSSL_PARAM_BLD_push_BN(b, OSSL_PKEY_PARAM_RSA_D, BN_bin2bn(d, 256, NULL));
  OSSL_PARAM *ps = OSSL_PARAM_BLD_to_param(b);
  EVP_PKEY_CTX *c = EVP_PKEY_CTX_new_from_name(NULL, "RSA", NULL);
  if (EVP_PKEY_fromdata_init(c) <= 0 || EVP_PKEY_fromdata(c, &os_rsa, EVP_PKEY_KEYPAIR, ps) <= 0) os_die("rsa key");
  os_rsa_md = EVP_MD_CTX_new();
}
static inline int bo_rsa_sign(uint8_t *sg, uint8_t *m, size_t ml) {
  EVP_PKEY_CTX *pc;
  size_t l = 256;
  EVP_DigestSignInit_ex(os_rsa_md, &pc, "SHA256", NULL, NULL, os_rsa, NULL);
  EVP_PKEY_CTX_set_rsa_padding(pc, RSA_PKCS1_PSS_PADDING);
  EVP_PKEY_CTX_set_rsa_pss_saltlen(pc, 0);
  return EVP_DigestSign(os_rsa_md, sg, &l, m, ml) == 1;
}
static inline int bo_rsa_verify(uint8_t *sg, uint8_t *m, size_t ml) {
  EVP_PKEY_CTX *pc;
  EVP_DigestVerifyInit_ex(os_rsa_md, &pc, "SHA256", NULL, NULL, os_rsa, NULL);
  EVP_PKEY_CTX_set_rsa_padding(pc, RSA_PKCS1_PSS_PADDING);
  EVP_PKEY_CTX_set_rsa_pss_saltlen(pc, 0);
  return EVP_DigestVerify(os_rsa_md, sg, 256, m, ml) == 1;
}

static EVP_PKEY *os_dh_key(uint8_t *sk, uint8_t *pk) {
  OSSL_PARAM_BLD *b = OSSL_PARAM_BLD_new();
  OSSL_PARAM_BLD_push_utf8_string(b, OSSL_PKEY_PARAM_GROUP_NAME, "ffdhe2048", 0);
  OSSL_PARAM_BLD_push_BN(b, OSSL_PKEY_PARAM_PUB_KEY, BN_bin2bn(pk, 256, NULL));
  if (sk) OSSL_PARAM_BLD_push_BN(b, OSSL_PKEY_PARAM_PRIV_KEY, BN_bin2bn(sk, 256, NULL));
  OSSL_PARAM *ps = OSSL_PARAM_BLD_to_param(b);
  EVP_PKEY_CTX *c = EVP_PKEY_CTX_new_from_name(NULL, "DH", NULL);
  EVP_PKEY *k = NULL;
  if (EVP_PKEY_fromdata_init(c) <= 0 ||
      EVP_PKEY_fromdata(c, &k, sk ? EVP_PKEY_KEYPAIR : EVP_PKEY_PUBLIC_KEY, ps) <= 0) os_die("dh key");
  return k;
}
static EVP_PKEY_CTX *os_dh;
#define BO_FFDHE
static inline void bo_ffdhe_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) {
  os_dh = EVP_PKEY_CTX_new(os_dh_key(sk, pk), NULL);
  if (EVP_PKEY_derive_init(os_dh) <= 0 || EVP_PKEY_derive_set_peer(os_dh, os_dh_key(NULL, peer)) <= 0) os_die("dh derive");
  EVP_PKEY_CTX_set_dh_pad(os_dh, 1);
}
static inline int bo_ffdhe_ss(uint8_t *ss) { size_t l = 256; return EVP_PKEY_derive(os_dh, ss, &l) == 1; }

/* ML-KEM-768: keys imported from hacl-pulse's raw encodings; key generation
   and encapsulation draw from OpenSSL's DRBG, hacl-pulse's take explicit
   randomness. */
static EVP_PKEY_CTX *os_kem_gen, *os_kem_enc, *os_kem_dec;
#define BO_MLKEM768
static inline void bo_mlkem768_setup(uint8_t *ek, uint8_t *dk) {
  EVP_PKEY *pub = EVP_PKEY_new_raw_public_key_ex(NULL, "ML-KEM-768", NULL, ek, 1184);
  EVP_PKEY *prv = EVP_PKEY_new_raw_private_key_ex(NULL, "ML-KEM-768", NULL, dk, 2400);
  if (!pub || !prv) os_die("ml-kem import");
  os_kem_enc = EVP_PKEY_CTX_new(pub, NULL);
  os_kem_dec = EVP_PKEY_CTX_new(prv, NULL);
  os_kem_gen = EVP_PKEY_CTX_new_from_name(NULL, "ML-KEM-768", NULL);
  if (EVP_PKEY_encapsulate_init(os_kem_enc, NULL) <= 0 || EVP_PKEY_decapsulate_init(os_kem_dec, NULL) <= 0 ||
      EVP_PKEY_keygen_init(os_kem_gen) <= 0) os_die("ml-kem init");
}
static inline void bo_mlkem768_keygen(void) {
  EVP_PKEY *k = NULL;
  EVP_PKEY_generate(os_kem_gen, &k);
  EVP_PKEY_free(k);
}
static inline void bo_mlkem768_enc(uint8_t *ct, uint8_t *ss) {
  size_t cl = 1088, sl = 32;
  EVP_PKEY_encapsulate(os_kem_enc, ct, &cl, ss, &sl);
}
static inline void bo_mlkem768_dec(uint8_t *ss, uint8_t *ct) {
  size_t sl = 32;
  EVP_PKEY_decapsulate(os_kem_dec, ss, &sl, ct, 1088);
}
