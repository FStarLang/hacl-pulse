/* Firedancer's ballet library (the Solana validator's crypto), built
 * with clang at -march=native as its makefile requires.  ballet has no
 * MD5/SHA-3/BLAKE2s/Poly1305/AEAD-ChaCha rows; its P-256 is verify-only
 * and takes a compressed public key; its X25519 is s2n-bignum's verified
 * assembly.  fd_ed25519_sign takes the 32-byte seed, so (unlike the other
 * contenders, which sign with a pre-expanded key) it rehashes the seed on
 * every signature, as hacl-pulse's main-table Ed25519 does. */
#include "ballet/sha1/fd_sha1.h"
#include "ballet/sha256/fd_sha256.h"
#include "ballet/sha512/fd_sha512.h"
#include "ballet/hmac/fd_hmac.h"
#include "ballet/aes/fd_aes_gcm.h"
#include "ballet/ed25519/fd_x25519.h"
#include "ballet/ed25519/fd_ed25519.h"
#include "ballet/secp256r1/fd_secp256r1.h"

#define IMPL_NAME "firedancer"

static uchar fdx_sha512_mem[FD_SHA512_FOOTPRINT] __attribute__((aligned(FD_SHA512_ALIGN)));
static uchar fdx_sha256_mem[FD_SHA256_FOOTPRINT] __attribute__((aligned(FD_SHA256_ALIGN)));
static fd_sha512_t *fdx_sha512;
static fd_sha256_t *fdx_sha256;
static void bo_init(void) {
  fdx_sha512 = fd_sha512_join(fd_sha512_new(fdx_sha512_mem));
  fdx_sha256 = fd_sha256_join(fd_sha256_new(fdx_sha256_mem));
}

#define BO_SHA1
static inline void bo_sha1(uint8_t *o, uint8_t *m, size_t n) { fd_sha1_hash(m, n, o); }
#define BO_SHA256
static inline void bo_sha256(uint8_t *o, uint8_t *m, size_t n) { fd_sha256_hash(m, n, o); }
#define BO_SHA512
static inline void bo_sha512(uint8_t *o, uint8_t *m, size_t n) { fd_sha512_hash(m, n, o); }
#define BO_HMAC256
static inline void bo_hmac256(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) { fd_hmac_sha256(m, n, k, 32, o); }
#define BO_HMAC512
static inline void bo_hmac512(uint8_t *o, uint8_t *k, uint8_t *m, size_t n) { fd_hmac_sha512(m, n, k, 32, o); }

/* The GCM object holds the key schedule and GHASH table; each message
   sets its IV, as a QUIC packet protector does. */
static fd_aes_gcm_t fdx_gcm128, fdx_gcm256;
#define BO_AES128GCM
static inline void bo_aes128gcm_setup(uint8_t *k) { uint8_t iv[12] = {0}; fd_aes_gcm_init(&fdx_gcm128, k, 16, iv); }
static inline void bo_aes128gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) {
  fd_aes_gcm_set_iv(&fdx_gcm128, iv);
  fd_aes_gcm_encrypt(&fdx_gcm128, c, m, n, a, al, t);
}
#define BO_AES256GCM
static inline void bo_aes256gcm_setup(uint8_t *k) { uint8_t iv[12] = {0}; fd_aes_gcm_init(&fdx_gcm256, k, 32, iv); }
static inline void bo_aes256gcm_enc(uint8_t *c, uint8_t *t, uint8_t *m, size_t n, uint8_t *a, size_t al, uint8_t *iv) {
  fd_aes_gcm_set_iv(&fdx_gcm256, iv);
  fd_aes_gcm_encrypt(&fdx_gcm256, c, m, n, a, al, t);
}

#define BO_X25519
static inline void bo_x25519(uint8_t *o, uint8_t *s, uint8_t *p) {
  if (!fd_x25519_exchange(o, s, p)) memset(o, 0, 32);
}

static uint8_t fdx_seed[32], fdx_pk[32];
#define BO_ED25519_SIGN
static inline void bo_ed25519_setup(uint8_t *seed) {
  memcpy(fdx_seed, seed, 32);
  fd_ed25519_public_from_private(fdx_pk, fdx_seed, fdx_sha512);
}
static inline void bo_ed25519_sign(uint8_t *sg, uint8_t *m, size_t n) { fd_ed25519_sign(sg, m, n, fdx_pk, fdx_seed, fdx_sha512); }
#define BO_ED25519_VERIFY
static inline int bo_ed25519_verify(uint8_t *pk, uint8_t *m, size_t n, uint8_t *sg) {
  return fd_ed25519_verify(m, n, sg, pk, fdx_sha512) == FD_ED25519_SUCCESS;
}

/* P-256 verification only.  The driver's signatures are those of
   hacl-pulse, whose s may be high, so the high-s-accepting entry point is
   the one that matches the other contenders' ECDSA verify. */
static uint8_t fdx_p256_pk[33];
#define BO_P256_VERIFY
static inline void bo_p256_setup(uint8_t *sk, uint8_t *pk, uint8_t *peer) {
  (void)sk; (void)peer;
  fdx_p256_pk[0] = 2 | (pk[63] & 1);
  memcpy(fdx_p256_pk + 1, pk, 32);
}
static inline int bo_p256_verify(uint8_t *m, size_t n, uint8_t *sg) {
  return fd_secp256r1_verify_allow_high_s(m, n, sg, fdx_p256_pk, fdx_sha256) == FD_SECP256R1_SUCCESS;
}
