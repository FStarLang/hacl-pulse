/* libsodium, through its public crypto_* API.  It is built from source
 * at -O3 so its runtime-dispatched AVX2 paths (ChaCha20, Salsa20,
 * Poly1305, BLAKE2b) are all available. */
#include <sodium.h>

#define IMPL_NAME "libsodium"

static void bo_init(void) {
  if (sodium_init() < 0) { fprintf(stderr, "sodium_init failed\n"); exit(1); }
}

#define BO_SHA256
static inline void bo_sha256(uint8_t *o, uint8_t *m, size_t n) { crypto_hash_sha256(o, m, n); }
#define BO_SHA512
static inline void bo_sha512(uint8_t *o, uint8_t *m, size_t n) { crypto_hash_sha512(o, m, n); }
#define BO_BLAKE2B
static inline void bo_blake2b(uint8_t *o, uint8_t *m, size_t n) { crypto_generichash(o, 64, m, n, NULL, 0); }

#define BO_HMAC256
static inline void bo_hmac256(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) {
  crypto_auth_hmacsha256_state st;
  crypto_auth_hmacsha256_init(&st, k, 32);
  crypto_auth_hmacsha256_update(&st, m, n);
  crypto_auth_hmacsha256_final(&st, o);
}
#define BO_HMAC512
static inline void bo_hmac512(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) {
  crypto_auth_hmacsha512_state st;
  crypto_auth_hmacsha512_init(&st, k, 32);
  crypto_auth_hmacsha512_update(&st, m, n);
  crypto_auth_hmacsha512_final(&st, o);
}
#define BO_POLY1305
static inline void bo_poly1305(uint8_t *o, uint8_t *m, size_t n, uint8_t *k) { crypto_onetimeauth_poly1305(o, m, n, k); }

#define BO_CHACHA20
static inline void bo_chacha20(uint8_t *c, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { crypto_stream_chacha20_ietf_xor(c, m, n, v, k); }
#define BO_SALSA20
static inline void bo_salsa20(uint8_t *c, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { crypto_stream_salsa20_xor(c, m, n, v, k); }
#define BO_CHACHAPOLY
static inline void bo_chachapoly(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *k, uint8_t *v) {
  crypto_aead_chacha20poly1305_ietf_encrypt_detached(c, t, NULL, m, n, a, al, NULL, v, k);
}
#define BO_SECRETBOX
static inline void bo_secretbox(uint8_t *c, uint8_t *m, size_t n, uint8_t *v, uint8_t *k) { crypto_secretbox_easy(c, m, n, v, k); }

/* libsodium has AES-256-GCM only (and only with AES-NI + PCLMUL). */
static crypto_aead_aes256gcm_state so_gcm;
#define BO_AES256GCM
static inline void bo_aes256gcm_setup(uint8_t *k) {
  if (!crypto_aead_aes256gcm_is_available()) { fprintf(stderr, "libsodium: no AES-GCM on this CPU\n"); exit(1); }
  crypto_aead_aes256gcm_beforenm(&so_gcm, k);
}
static inline void bo_aes256gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) {
  crypto_aead_aes256gcm_encrypt_detached_afternm(c, t, NULL, m, n, a, al, NULL, iv, &so_gcm);
}

#define BO_X25519
static inline void bo_x25519(uint8_t *o, uint8_t *s, uint8_t *p) {
  if (crypto_scalarmult(o, s, p) != 0) memset(o, 0, 32);
}
static uint8_t so_ed_sk[64];
#define BO_ED25519_SIGN
static inline void bo_ed25519_setup(uint8_t *seed) {
  uint8_t pk[32];
  crypto_sign_seed_keypair(pk, so_ed_sk, seed);
}
static inline void bo_ed25519_sign(uint8_t *sg, uint8_t *m, size_t n) { crypto_sign_detached(sg, NULL, m, n, so_ed_sk); }
#define BO_ED25519_VERIFY
static inline int bo_ed25519_verify(uint8_t *pk, uint8_t *m, size_t n, uint8_t *sg) { return crypto_sign_verify_detached(sg, m, n, pk) == 0; }
