/* hacl-pulse, through the same bo_* interface as the other libraries. */
#define IMPL_NAME "pulse"

static void bo_init(void) {}

#define BO_MD5
static inline void bo_md5(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_MD5_md5(o, m, n); }
#define BO_SHA1
static inline void bo_sha1(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA1_sha1(o, m, n); }
#define BO_SHA256
static inline void bo_sha256(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA2_sha256(o, m, n); }
#define BO_SHA512
static inline void bo_sha512(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA2_sha512(o, m, n); }
#define BO_SHA3_256
static inline void bo_sha3_256(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_SHA3_sha3_256(o, m, n); }
#define BO_SHAKE128
static inline void bo_shake128(uint8_t *o, size_t ol, uint8_t *m, size_t n) { Hacl_Hash_SHA3_shake128(o, ol, m, n); }
#define BO_BLAKE2B
static inline void bo_blake2b(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_Blake2_Named_blake2b_512(o, NULL, 0, m, n); }
#define BO_BLAKE2S
static inline void bo_blake2s(uint8_t *o, uint8_t *m, size_t n) { Hacl_Hash_Blake2_Named_blake2s_256(o, NULL, 0, m, n); }

#define BO_HMAC256
static inline void bo_hmac256(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) { Hacl_HMAC_hmac_sha256(o, k, 32, m, n); }
#define BO_HMAC512
static inline void bo_hmac512(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) { Hacl_HMAC_hmac_sha512(o, k, 32, m, n); }
#define BO_POLY1305
static inline void bo_poly1305(uint8_t *o, uint8_t *m, size_t n, uint8_t *k) { Hacl_Poly1305_mac(o, m, n, k); }

#define BO_CHACHA20
static inline void bo_chacha20(uint8_t *c, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { Hacl_Chacha20_encrypt(c, m, n, k, v, 0); }
#define BO_SALSA20
static inline void bo_salsa20(uint8_t *c, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { Hacl_Salsa20_encrypt(c, m, n, k, v, 0); }
#define BO_CHACHAPOLY
static inline void bo_chachapoly(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) {
  Hacl_Chacha20Poly1305_encrypt(c, t, m, n, a, al, k, v);
}
#define BO_SECRETBOX
static inline void bo_secretbox(uint8_t *c, uint8_t *m, size_t n, uint8_t *v, uint8_t *k) { Hacl_NaCl_crypto_secretbox_easy(c, m, n, v, k); }

static uint8_t pl_gcm128_ek[176], pl_gcm128_hk[128], pl_gcm256_ek[240], pl_gcm256_hk[128];
#define BO_AES128GCM
static inline void bo_aes128gcm_setup(uint8_t *k) { Hacl_AES_GCM_aes128_expand(pl_gcm128_ek, pl_gcm128_hk, k); }
static inline void bo_aes128gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) {
  Hacl_AES_GCM_aes128_encrypt_expanded(c, t, m, n, pl_gcm128_ek, pl_gcm128_hk, iv, 12, a, al);
}
#define BO_AES256GCM
static inline void bo_aes256gcm_setup(uint8_t *k) { Hacl_AES_GCM_aes256_expand(pl_gcm256_ek, pl_gcm256_hk, k); }
static inline void bo_aes256gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) {
  Hacl_AES_GCM_aes256_encrypt_expanded(c, t, m, n, pl_gcm256_ek, pl_gcm256_hk, iv, 12, a, al);
}

#define BO_X25519
static inline void bo_x25519(uint8_t *o, uint8_t *s, uint8_t *p) { Hacl_Curve25519_scalarmult(o, s, p); }

/* expand_keys: public key (32) || secret scalar (32) || prefix (32). */
static uint8_t pl_ed_ks[96];
#define BO_ED25519_SIGN
static inline void bo_ed25519_setup(uint8_t *seed) { Hacl_Ed25519_expand_keys(pl_ed_ks, seed); }
static inline void bo_ed25519_sign(uint8_t *sg, uint8_t *m, size_t n) {
  Hacl_Ed25519_sign_expanded(sg, pl_ed_ks, pl_ed_ks + 32, pl_ed_ks + 64, m, n);
}
#define BO_ED25519_VERIFY
static inline int bo_ed25519_verify(uint8_t *pk, uint8_t *m, size_t n, uint8_t *sg) { return Hacl_Ed25519_verify(pk, m, n, sg); }

static uint8_t pl_p256_sk[32], pl_p256_pk[64], pl_p256_peer[64], pl_p256_nonce[32];
#define BO_P256_ECDH
#define BO_P256_SIGN
#define BO_P256_VERIFY
static inline void bo_p256_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) {
  memcpy(pl_p256_sk, sk, 32); memcpy(pl_p256_pk, pk, 64); memcpy(pl_p256_peer, peer, 64);
  memset(pl_p256_nonce, 0x5a, 32);
}
static inline int bo_p256_ecdh(uint8_t *ss) {
  uint8_t pt[64];
  int r = Hacl_P256_Ecdh_dh_responder(pt, pl_p256_peer, pl_p256_sk);
  memcpy(ss, pt, 32);
  return r;
}
static inline int bo_p256_sign(uint8_t *sg, uint8_t *m, size_t n) {
  return Hacl_P256_ecdsa_sign_sha256(sg, m, n, pl_p256_sk, pl_p256_nonce);
}
static inline int bo_p256_verify(uint8_t *m, size_t n, uint8_t *sg) {
  return Hacl_P256_ecdsa_verify_sha256(m, n, pl_p256_pk, sg, sg + 32);
}

static uint8_t pl_p384_sk[48], pl_p384_pk[96], pl_p384_peer[96], pl_p384_nonce[48];
#define BO_P384_ECDH
#define BO_P384_SIGN
#define BO_P384_VERIFY
static inline void bo_p384_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) {
  memcpy(pl_p384_sk, sk, 48); memcpy(pl_p384_pk, pk, 96); memcpy(pl_p384_peer, peer, 96);
  memset(pl_p384_nonce, 0x5a, 48);
}
static inline int bo_p384_ecdh(uint8_t *ss) {
  uint8_t pt[96];
  int r = Hacl_P384_Ecdh_dh_responder(pt, pl_p384_peer, pl_p384_sk);
  memcpy(ss, pt, 48);
  return r;
}
static inline int bo_p384_sign(uint8_t *sg, uint8_t *m, size_t n) {
  return Hacl_P384_ecdsa_sign_sha384(sg, m, n, pl_p384_sk, pl_p384_nonce);
}
static inline int bo_p384_verify(uint8_t *m, size_t n, uint8_t *sg) {
  return Hacl_P384_ecdsa_verify_sha384(m, n, pl_p384_pk, sg);
}

static uint8_t pl_k256_sk[32], pl_k256_nonce[32];
#define BO_K256_SIGN
static inline void bo_k256_setup(uint8_t *sk) { memcpy(pl_k256_sk, sk, 32); memset(pl_k256_nonce, 0x5a, 32); }
static inline int bo_k256_sign(uint8_t *sg, uint8_t *h) { return Hacl_K256_ecdsa_sign_hashed_msg(sg, h, pl_k256_sk, pl_k256_nonce); }

/* hacl-pulse's RSA-PSS takes the key as bytes, so loading it is inside
   every call; the other libraries load it once. */
static uint8_t *pl_rsa_n, *pl_rsa_e, *pl_rsa_d;
static size_t pl_rsa_el;
#define BO_RSA
static inline void bo_rsa_setup(uint8_t *n, uint8_t *e, size_t el, uint8_t *d) { pl_rsa_n = n; pl_rsa_e = e; pl_rsa_el = el; pl_rsa_d = d; }
static inline int bo_rsa_sign(uint8_t *sg, uint8_t *m, size_t ml) {
  return Hacl_RSAPSS_sign_sha256(2048, pl_rsa_n, 256, pl_rsa_d, 0, NULL, ml, m, sg);
}
static inline int bo_rsa_verify(uint8_t *sg, uint8_t *m, size_t ml) {
  return Hacl_RSAPSS_verify_sha256(2048, pl_rsa_n, pl_rsa_el, pl_rsa_e, 0, sg, ml, m);
}

static uint8_t *pl_dh_sk, *pl_dh_peer;
#define BO_FFDHE
static inline void bo_ffdhe_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) { (void)pk; pl_dh_sk = sk; pl_dh_peer = peer; }
static inline int bo_ffdhe_ss(uint8_t *ss) { return Hacl_FFDHE_ffdhe2048_shared_secret(ss, pl_dh_sk, pl_dh_peer); }

static uint8_t pl_kem_ek[1184], pl_kem_dk[2400], pl_kem_ek2[1184], pl_kem_dk2[2400];
#define BO_MLKEM768
static inline void bo_mlkem768_setup(uint8_t *ek, uint8_t *dk) { memcpy(pl_kem_ek, ek, 1184); memcpy(pl_kem_dk, dk, 2400); }
/* OpenSSL and AWS-LC draw fresh randomness for every key pair and every
   encapsulation, so these take a fresh seed each call too: a fixed one lets
   the branch predictor learn the rejection sampling (REPORT.md Part 85). */
static uint64_t pl_kem_ctr;
static inline void pl_kem_seed(uint8_t *x, uint8_t b) {
  uint64_t c = ++pl_kem_ctr * 0x9e3779b97f4a7c15ULL;
  memset(x, b, 32);
  memcpy(x, &c, 8);
}
static inline void bo_mlkem768_keygen(void) {
  uint8_t d[32], z[32];
  pl_kem_seed(d, 1); pl_kem_seed(z, 2);
  Hacl_MLKEM768_keypair(pl_kem_ek2, pl_kem_dk2, d, z);
}
static inline void bo_mlkem768_enc(uint8_t *ct, uint8_t *ss) {
  uint8_t m[32];
  pl_kem_seed(m, 3);
  Hacl_MLKEM768_enc(ct, ss, pl_kem_ek, m);
}
static inline void bo_mlkem768_dec(uint8_t *ss, uint8_t *ct) { Hacl_MLKEM768_dec(ss, ct, pl_kem_dk); }

/* ML-DSA: deterministic signing (rnd = 0), empty context. */
#define PL_MLDSA(P_, PK_, SK_)                                                   \
  static uint8_t pl_dsa##P_##_pk[PK_], pl_dsa##P_##_sk[SK_], pl_dsa##P_##_sk2[SK_]; \
  static inline void bo_mldsa##P_##_keygen(uint8_t *pk, uint8_t *xi) {          \
    Hacl_MLDSA##P_##_keypair(pk, pl_dsa##P_##_sk2, xi);                          \
  }                                                                              \
  static inline void bo_mldsa##P_##_setup(uint8_t *pk, uint8_t *sk) {           \
    memcpy(pl_dsa##P_##_pk, pk, PK_); memcpy(pl_dsa##P_##_sk, sk, SK_);          \
  }                                                                              \
  static inline int bo_mldsa##P_##_sign(uint8_t *sg, uint8_t *m, size_t n) {     \
    return Hacl_MLDSA##P_##_sign_deterministic(sg, pl_dsa##P_##_sk, m, n, NULL, 0); \
  }                                                                              \
  static inline int bo_mldsa##P_##_verify(uint8_t *m, size_t n, uint8_t *sg) {   \
    return Hacl_MLDSA##P_##_verify(pl_dsa##P_##_pk, m, n, NULL, 0, sg);          \
  }
#define BO_MLDSA44
#define BO_MLDSA65
#define BO_MLDSA87
PL_MLDSA(44, 1312, 2560)
PL_MLDSA(65, 1952, 4032)
PL_MLDSA(87, 2592, 4896)
