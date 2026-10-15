#define _DEFAULT_SOURCE 1
/* hacl-pulse against other libraries.
 *
 * One driver, compiled once per library against an ops header (OPS) that
 * defines bo_* entry points and a BO_<ROW> macro for each row the library
 * supports.  Rows a library does not have are simply absent from its CSV.
 *
 * Every binary also links hacl-pulse, which plays two roles: it generates
 * all key material (so every library works on the same keys, messages and
 * nonces), and it is the oracle.  Before a row is timed, the library's
 * output is checked against hacl-pulse's -- byte for byte where the
 * operation is deterministic, by cross-verification where it is not (ECDSA
 * signatures are verified by hacl-pulse; ML-KEM ciphertexts are
 * decapsulated by the other side) -- and the binary aborts on any mismatch,
 * so a row can never be measuring something different from its label.
 *
 * Keys are expanded or loaded once, outside the timed region, wherever the
 * library's API allows it: Ed25519 signs with a pre-expanded key (except
 * Firedancer, whose API takes the seed), AES-GCM with a pre-computed key
 * schedule, RSA with a loaded key (except hacl-pulse, whose API takes the
 * key as bytes on every call).
 *
 * CSV: impl,bench,bytes,ns_per_op,mb_per_s  (same as bench.c)
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "Hacl.h"
#include "../rsakey.inc"

#define MAXBUF (1 << 18)
static uint8_t msg[MAXBUF + 64];

#include OPS

static volatile uint64_t sink = 0;

static double now_sec(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

volatile uint64_t canary_sink;
static double canary_ns(void) {
  double t = now_sec();
  uint64_t x = 1;
  for (uint64_t i = 0; i < 200000000ULL; i++) x += (x >> 3) | 1;
  canary_sink = x;
  return (now_sec() - t) * 1e9;
}

static void report(const char *name, size_t bytes, double secs) {
  double ns = secs * 1e9;
  if (bytes)
    printf("%s,%s,%zu,%.2f,%.2f\n", IMPL_NAME, name, bytes, ns, bytes / secs / 1e6);
  else
    printf("%s,%s,0,%.2f,\n", IMPL_NAME, name, ns);
  fflush(stdout);
}

#define TIME(name_, bytes_, body_)                                             \
  do {                                                                         \
    uint64_t iters = 1;                                                        \
    double t = 0;                                                              \
    for (;;) {                                                                 \
      t = now_sec();                                                           \
      for (uint64_t i_ = 0; i_ < iters; i_++) { body_; }                       \
      t = now_sec() - t;                                                       \
      if (t > 0.05 || iters > (1u << 30)) break;                               \
      iters *= 2;                                                              \
    }                                                                          \
    double best = t / (double)iters;                                           \
    for (int r_ = 0; r_ < 4; r_++) {                                           \
      double s_ = now_sec();                                                   \
      for (uint64_t i_ = 0; i_ < iters; i_++) { body_; }                       \
      s_ = (now_sec() - s_) / (double)iters;                                   \
      if (s_ < best) best = s_;                                                \
    }                                                                          \
    report(name_, (size_t)(bytes_), best);                                     \
  } while (0)

static const size_t sizes[] = {1024, 262144};
#define NSIZES (sizeof(sizes) / sizeof(sizes[0]))

static uint8_t C[MAXBUF + 64], RC[MAXBUF + 64];
static uint8_t O[256], RO[256], T[16], RT[16];
static uint8_t key32[32], key16[16], nonce24[24], nonce12[12];

#define BULK(name_, call_)                                                     \
  do {                                                                         \
    for (unsigned s_ = 0; s_ < NSIZES; s_++) {                                 \
      size_t n = sizes[s_];                                                    \
      TIME(name_, n, { call_; sink += O[0] + C[0]; });                         \
    }                                                                          \
  } while (0)

static void fail(const char *what) {
  fprintf(stderr, "%s: %s does not agree with hacl-pulse\n", IMPL_NAME, what);
  exit(1);
}

static void same(const char *what, const uint8_t *a, const uint8_t *b, size_t len) {
  if (memcmp(a, b, len)) fail(what);
}

static void fill(uint8_t *p, size_t n, unsigned seed) {
  uint64_t x = 0x9e3779b97f4a7c15ULL ^ seed;
  for (size_t i = 0; i < n; i++) {
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    p[i] = (uint8_t)x;
  }
}

#define CK 1024 /* message length used by the agreement checks */

int main(void) {
  fill(msg, sizeof msg, 1);
  fill(key32, sizeof key32, 2);
  fill(key16, sizeof key16, 3);
  fill(nonce24, sizeof nonce24, 4);
  fill(nonce12, sizeof nonce12, 5);
  bo_init();

  printf("impl,bench,bytes,ns_per_op,mb_per_s\n");
  double canary_before = canary_ns();

  /* ---------------- hashes ---------------- */
#ifdef BO_MD5
  Hacl_Hash_MD5_md5(RO, msg, CK); bo_md5(O, msg, CK); same("md5", O, RO, 16);
  BULK("md5", bo_md5(O, msg, n));
#endif
#ifdef BO_SHA1
  Hacl_Hash_SHA1_sha1(RO, msg, CK); bo_sha1(O, msg, CK); same("sha1", O, RO, 20);
  BULK("sha1", bo_sha1(O, msg, n));
#endif
#ifdef BO_SHA256
  Hacl_Hash_SHA2_sha256(RO, msg, CK); bo_sha256(O, msg, CK); same("sha2-256", O, RO, 32);
  BULK("sha2-256", bo_sha256(O, msg, n));
#endif
#ifdef BO_SHA512
  Hacl_Hash_SHA2_sha512(RO, msg, CK); bo_sha512(O, msg, CK); same("sha2-512", O, RO, 64);
  BULK("sha2-512", bo_sha512(O, msg, n));
#endif
#ifdef BO_SHA3_256
  Hacl_Hash_SHA3_sha3_256(RO, msg, CK); bo_sha3_256(O, msg, CK); same("sha3-256", O, RO, 32);
  BULK("sha3-256", bo_sha3_256(O, msg, n));
#endif
#ifdef BO_SHAKE128
  Hacl_Hash_SHA3_shake128(RO, 32, msg, CK); bo_shake128(O, 32, msg, CK); same("shake128", O, RO, 32);
  BULK("shake128", bo_shake128(O, 32, msg, n));
#endif
#ifdef BO_BLAKE2B
  Hacl_Hash_Blake2_Named_blake2b_512(RO, NULL, 0, msg, CK); bo_blake2b(O, msg, CK); same("blake2b", O, RO, 64);
  BULK("blake2b", bo_blake2b(O, msg, n));
#endif
#ifdef BO_BLAKE2S
  Hacl_Hash_Blake2_Named_blake2s_256(RO, NULL, 0, msg, CK); bo_blake2s(O, msg, CK); same("blake2s", O, RO, 32);
  BULK("blake2s", bo_blake2s(O, msg, n));
#endif

  /* ---------------- MACs ---------------- */
#ifdef BO_HMAC256
  Hacl_HMAC_hmac_sha256(RO, key32, 32, msg, CK); bo_hmac256(O, key32, msg, CK); same("hmac-sha2-256", O, RO, 32);
  BULK("hmac-sha2-256", bo_hmac256(O, key32, msg, n));
#endif
#ifdef BO_HMAC512
  Hacl_HMAC_hmac_sha512(RO, key32, 32, msg, CK); bo_hmac512(O, key32, msg, CK); same("hmac-sha2-512", O, RO, 64);
  BULK("hmac-sha2-512", bo_hmac512(O, key32, msg, n));
#endif
#ifdef BO_POLY1305
  Hacl_Poly1305_mac(RO, msg, CK, key32); bo_poly1305(O, msg, CK, key32); same("poly1305", O, RO, 16);
  BULK("poly1305", bo_poly1305(O, msg, n, key32));
#endif

  /* ---------------- ciphers and AEADs ---------------- */
#ifdef BO_CHACHA20
  Hacl_Chacha20_encrypt(RC, msg, CK, key32, nonce12, 0); bo_chacha20(C, msg, CK, key32, nonce12);
  same("chacha20", C, RC, CK);
  BULK("chacha20", bo_chacha20(C, msg, n, key32, nonce12));
#endif
#ifdef BO_SALSA20
  Hacl_Salsa20_encrypt(RC, msg, CK, key32, nonce12, 0); bo_salsa20(C, msg, CK, key32, nonce12);
  same("salsa20", C, RC, CK);
  BULK("salsa20", bo_salsa20(C, msg, n, key32, nonce12));
#endif
#ifdef BO_CHACHAPOLY
  Hacl_Chacha20Poly1305_encrypt(RC, RT, msg, CK, msg, 16, key32, nonce12);
  bo_chachapoly(C, T, msg, CK, msg, 16, key32, nonce12);
  same("chacha20poly1305 ciphertext", C, RC, CK); same("chacha20poly1305 tag", T, RT, 16);
  BULK("chacha20poly1305-enc", bo_chachapoly(C, T, msg, n, msg, 16, key32, nonce12));
#endif
#ifdef BO_SECRETBOX
  Hacl_NaCl_crypto_secretbox_easy(RC, msg, CK, nonce24, key32); bo_secretbox(C, msg, CK, nonce24, key32);
#ifdef BO_SECRETBOX_RESULT /* the box lives in the contender's own buffer */
  memcpy(C, BO_SECRETBOX_RESULT, CK + 16);
#endif
  same("nacl-secretbox-easy", C, RC, CK + 16);
  BULK("nacl-secretbox-easy", bo_secretbox(C, msg, n, nonce24, key32));
#endif
#ifdef BO_AES128GCM
  {
    static uint8_t ek[176], hk[128];
    Hacl_AES_GCM_aes128_expand(ek, hk, key16);
    memcpy(RC, msg, CK);
    Hacl_AES_GCM_aes128_encrypt_expanded(RT, RC, CK, ek, hk, nonce12, 12, msg, 16);
    bo_aes128gcm_setup(key16);
    bo_aes128gcm_enc(C, T, msg, CK, msg, 16, nonce12);
    same("aes128-gcm ciphertext", C, RC, CK); same("aes128-gcm tag", T, RT, 16);
    BULK("aes128-gcm-enc", bo_aes128gcm_enc(C, T, msg, n, msg, 16, nonce12));
  }
#endif
#ifdef BO_AES256GCM
  {
    static uint8_t ek[240], hk[128];
    Hacl_AES_GCM_aes256_expand(ek, hk, key32);
    memcpy(RC, msg, CK);
    Hacl_AES_GCM_aes256_encrypt_expanded(RT, RC, CK, ek, hk, nonce12, 12, msg, 16);
    bo_aes256gcm_setup(key32);
    bo_aes256gcm_enc(C, T, msg, CK, msg, 16, nonce12);
    same("aes256-gcm ciphertext", C, RC, CK); same("aes256-gcm tag", T, RT, 16);
    BULK("aes256-gcm-enc", bo_aes256gcm_enc(C, T, msg, n, msg, 16, nonce12));
  }
#endif

  /* ---------------- Curve25519 / Ed25519 ---------------- */
  {
    uint8_t sk[32], sk2[32], pk2[32], ss[32], rss[32];
    fill(sk, 32, 7);
    fill(sk2, 32, 8);
    Hacl_Curve25519_secret_to_public(pk2, sk2);
    Hacl_Curve25519_scalarmult(rss, sk, pk2);
    (void)ss; (void)rss;
#ifdef BO_X25519
    bo_x25519(ss, sk, pk2); same("x25519", ss, rss, 32);
    TIME("x25519-scalarmult", 0, { bo_x25519(ss, sk, pk2); sink += ss[0]; });
#endif
  }
  {
    uint8_t seed[32], pk[32], sg[64], rsg[64];
    fill(seed, 32, 9);
    Hacl_Ed25519_secret_to_public(pk, seed);
    Hacl_Ed25519_sign(rsg, seed, msg, 64);
    (void)sg; (void)rsg; (void)pk;
#ifdef BO_ED25519_SIGN
    bo_ed25519_setup(seed);
    bo_ed25519_sign(sg, msg, 64); same("ed25519 signature", sg, rsg, 64);
    TIME("ed25519-sign-64B", 0, { bo_ed25519_sign(sg, msg, 64); sink += sg[0]; });
#endif
#ifdef BO_ED25519_VERIFY
    if (!bo_ed25519_verify(pk, msg, 64, rsg)) fail("ed25519 verify (valid)");
    rsg[5] ^= 1;
    if (bo_ed25519_verify(pk, msg, 64, rsg)) fail("ed25519 verify (forged)");
    rsg[5] ^= 1;
    TIME("ed25519-verify-64B", 0, { sink += bo_ed25519_verify(pk, msg, 64, rsg); });
#endif
  }

  /* ---------------- P-256 ---------------- */
  {
    uint8_t sk[32], pk[64], sk2[32], pk2[64], nonce[32], rss[64], ss[32], sg[64], rsg[64];
    fill(sk, 32, 11); sk[0] = 1;
    fill(sk2, 32, 13); sk2[0] = 1;
    fill(nonce, 32, 12); nonce[0] = 1;
    Hacl_P256_Ecdh_dh_initiator(pk, sk);
    Hacl_P256_Ecdh_dh_initiator(pk2, sk2);
    Hacl_P256_Ecdh_dh_responder(rss, pk2, sk);
    Hacl_P256_ecdsa_sign_sha256(rsg, msg, 64, sk, nonce);
    (void)ss; (void)sg; (void)rss; (void)rsg;
#if defined(BO_P256_ECDH) || defined(BO_P256_SIGN) || defined(BO_P256_VERIFY)
    bo_p256_setup(sk, pk, pk2);
#endif
#ifdef BO_P256_ECDH
    bo_p256_ecdh(ss); same("p256 ecdh", ss, rss, 32);
    TIME("p256-ecdh", 0, { sink += bo_p256_ecdh(ss); });
#endif
#ifdef BO_P256_SIGN
    if (!bo_p256_sign(sg, msg, 64)) fail("p256 sign");
    if (!Hacl_P256_ecdsa_verify_sha256(msg, 64, pk, sg, sg + 32)) fail("p256 signature");
    TIME("p256-ecdsa-sign", 0, { sink += bo_p256_sign(sg, msg, 64); });
#endif
#ifdef BO_P256_VERIFY
    if (!bo_p256_verify(msg, 64, rsg)) fail("p256 verify (valid)");
    rsg[40] ^= 1;
    if (bo_p256_verify(msg, 64, rsg)) fail("p256 verify (forged)");
    rsg[40] ^= 1;
    TIME("p256-ecdsa-verify", 0, { sink += bo_p256_verify(msg, 64, rsg); });
#endif
  }

  /* ---------------- secp256k1 ---------------- */
#ifdef BO_K256_SIGN
  {
    uint8_t sk[32], pk[64], h[32], sg[64];
    fill(sk, 32, 21); sk[0] = 1;
    fill(h, 32, 23);
    Hacl_K256_Ecdh_dh_initiator(pk, sk);
    bo_k256_setup(sk);
    if (!bo_k256_sign(sg, h)) fail("k256 sign");
    if (!Hacl_K256_ecdsa_verify_hashed_msg(h, pk, sg, sg + 32)) fail("k256 signature");
    TIME("k256-ecdsa-sign", 0, { sink += bo_k256_sign(sg, h); });
  }
#endif

  /* ---------------- RSA-PSS 2048, SHA-256, empty salt ---------------- */
#ifdef BO_RSA
  {
    uint8_t sg[256], rsg[256];
    Hacl_RSAPSS_sign_sha256(2048, n_b, sizeof d_b, d_b, 0, NULL, 32, msg, rsg);
    bo_rsa_setup(n_b, e_b, sizeof e_b, d_b);
    if (!bo_rsa_sign(sg, msg, 32)) fail("rsa-pss sign");
    same("rsa-pss signature", sg, rsg, 256);
    if (!bo_rsa_verify(rsg, msg, 32)) fail("rsa-pss verify (valid)");
    rsg[100] ^= 1;
    if (bo_rsa_verify(rsg, msg, 32)) fail("rsa-pss verify (forged)");
    rsg[100] ^= 1;
    TIME("rsapss-2048-sign", 0, { sink += bo_rsa_sign(sg, msg, 32); });
    TIME("rsapss-2048-verify", 0, { sink += bo_rsa_verify(rsg, msg, 32); });
  }
#endif

  /* ---------------- FFDHE 2048 ---------------- */
#ifdef BO_FFDHE
  {
    static uint8_t sk_a[256], sk_b[256], pk_a[256], pk_b[256], ss[256], rss[256];
    fill(sk_a, 256, 31); sk_a[0] = 1;
    fill(sk_b, 256, 32); sk_b[0] = 1;
    Hacl_FFDHE_ffdhe2048_secret_to_public(pk_a, sk_a);
    Hacl_FFDHE_ffdhe2048_secret_to_public(pk_b, sk_b);
    Hacl_FFDHE_ffdhe2048_shared_secret(rss, sk_a, pk_b);
    bo_ffdhe_setup(sk_a, pk_a, pk_b);
    if (!bo_ffdhe_ss(ss)) fail("ffdhe derive");
    same("ffdhe shared secret", ss, rss, 256);
    TIME("ffdhe2048-shared-secret", 0, { sink += bo_ffdhe_ss(ss); });
  }
#endif

  /* ---------------- ML-KEM-768 ---------------- */
#ifdef BO_MLKEM768
  {
    static uint8_t ek[1184], dk[2400], ct[1088], rct[1088];
    uint8_t d[32], z[32], m[32], ss[32], rss[32];
    fill(d, 32, 61); fill(z, 32, 62); fill(m, 32, 63);
    Hacl_MLKEM768_keypair(ek, dk, d, z);
    Hacl_MLKEM768_enc(rct, rss, ek, m);
    bo_mlkem768_setup(ek, dk);
    bo_mlkem768_dec(ss, rct); same("ml-kem-768 decapsulate", ss, rss, 32);
    bo_mlkem768_enc(ct, ss); Hacl_MLKEM768_dec(rss, ct, dk); same("ml-kem-768 encapsulate", ss, rss, 32);
    TIME("mlkem768-keypair", 0, { bo_mlkem768_keygen(); sink += 1; });
    TIME("mlkem768-encapsulate", 0, { bo_mlkem768_enc(ct, ss); sink += ss[0]; });
    TIME("mlkem768-decapsulate", 0, { bo_mlkem768_dec(ss, rct); sink += ss[0]; });
  }
#endif

  {
    double canary_after = canary_ns();
    double c = canary_before < canary_after ? canary_before : canary_after;
    double spread = (canary_after > canary_before ? canary_after / canary_before
                                                  : canary_before / canary_after);
    printf("%s,canary,0,%.2f,%.4f\n", IMPL_NAME, c, spread);
  }
  if (sink == 0x123456789) printf("unreachable\n");
  return 0;
}
