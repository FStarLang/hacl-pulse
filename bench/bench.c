#define _DEFAULT_SOURCE 1
/* A like-for-like benchmark of hacl-pulse's extracted C against HACL*'s.
 *
 * The same driver is compiled twice, once against each library, through a
 * shim header that maps each library's entry points onto one set of names.
 * Both binaries are built with the same compiler and the same flags, and
 * print the same CSV: impl,bench,bytes,ns_per_op,mb_per_s.
 *
 * Each measurement auto-scales the iteration count to ~50 ms, then takes the
 * best of five such rounds, which is the usual way to get the "no interference"
 * number out of a noisy machine.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include SHIM

#include "rsakey.inc"

static volatile uint64_t sink = 0;

static double now_sec(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return ts.tv_sec + 1e-9 * ts.tv_nsec;
}

/* A fixed amount of work with a serial dependence chain, so its run time is
   a direct reading of the core's clock and of any interference it is
   suffering.  It is measured before and after the suite and reported as an
   ordinary row: a comparison whose canaries disagree is a comparison between
   two machine states, not between two libraries. */
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

#define TIME(name_, bytes_, body_) TIME_MIN(name_, bytes_, 1, body_)

/* min_ is a power of two; every iteration count is then a multiple of it, so
   a body that cycles through min_ inputs runs each of them equally often. */
#define TIME_MIN(name_, bytes_, min_, body_)                                   \
  do {                                                                         \
    uint64_t iters = (min_);                                                   \
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
      s_ = (now_sec() - s_) / (double)iters;                                    \
      if (s_ < best) best = s_;                                                \
    }                                                                          \
    report(name_, (size_t)(bytes_), best);                                     \
  } while (0)

static const size_t sizes[] = {64, 1024, 16384, 262144};
#define NSIZES (sizeof(sizes) / sizeof(sizes[0]))

#define BULK(name_, call_)                                                     \
  do {                                                                         \
    for (unsigned s_ = 0; s_ < NSIZES; s_++) {                                 \
      size_t n = sizes[s_];                                                    \
      char nm[64];                                                             \
      snprintf(nm, sizeof nm, "%s", name_);                                    \
      TIME(nm, n, { call_; sink += out[0]; });                                 \
    }                                                                          \
  } while (0)

#define MAXBUF (1 << 18)

static uint8_t msg[MAXBUF + 64];
static uint8_t ct[MAXBUF + 64];
static uint8_t pt[MAXBUF + 64];
static uint8_t out[256];
static uint8_t key32[32], key16[16], nonce24[24], nonce12[12], tag16[16];

static void fill(uint8_t *p, size_t n, unsigned seed) {
  uint64_t x = 0x9e3779b97f4a7c15ULL ^ seed;
  for (size_t i = 0; i < n; i++) {
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    p[i] = (uint8_t)x;
  }
}

int main(void) {
  bs_global_init();
  fill(msg, sizeof msg, 1);
  fill(key32, sizeof key32, 2);
  fill(key16, sizeof key16, 3);
  fill(nonce24, sizeof nonce24, 4);
  fill(nonce12, sizeof nonce12, 5);

  printf("impl,bench,bytes,ns_per_op,mb_per_s\n");
  double canary_before = canary_ns();

  /* ---------------- hashes ---------------- */
  BULK("md5", bs_md5(out, msg, n));
  BULK("sha1", bs_sha1(out, msg, n));
  BULK("sha2-256", bs_sha256(out, msg, n));
  BULK("sha2-512", bs_sha512(out, msg, n));
  BULK("sha3-256", bs_sha3_256(out, msg, n));
  BULK("sha3-512", bs_sha3_512(out, msg, n));
  BULK("shake128", bs_shake128(out, 32, msg, n));
  BULK("blake2b", bs_blake2b(out, msg, n));
  BULK("blake2s", bs_blake2s(out, msg, n));

  /* ---------------- streaming ---------------- */
  {
    bs_sha256_state st;
    memset(&st, 0, sizeof st);
    TIME("sha2-256-stream-1KiB-chunks", 262144,
         { bs_sha256_stream(&st, out, msg, 262144, 1024); sink += out[0]; });
    TIME("sha2-256-stream-64B-chunks", 16384,
         { bs_sha256_stream(&st, out, msg, 16384, 64); sink += out[0]; });
  }

  /* ---------------- MACs and KDFs ---------------- */
  BULK("hmac-sha2-256", bs_hmac_sha256(out, key32, 32, msg, n));
  BULK("hmac-sha2-512", bs_hmac_sha512(out, key32, 32, msg, n));
  TIME("hkdf-extract-sha2-256", 0, { bs_hkdf_extract_sha256(out, key32, 32, msg, 32); sink += out[0]; });
  TIME("hkdf-expand-sha2-256-64B", 0, { bs_hkdf_expand_sha256(out, 64, key32, 32, msg, 16); sink += out[0]; });

  /* ---------------- symmetric ---------------- */
  BULK("chacha20", bs_chacha20(ct, msg, n, key32, nonce12));
  BULK("salsa20", bs_salsa20(ct, msg, n, key32, nonce12 /* 8 bytes used */));
  BULK("poly1305", bs_poly1305(out, msg, n, key32));
  BULK("chacha20poly1305-enc", bs_chachapoly_enc(ct, tag16, msg, n, msg, 16, key32, nonce12));
  {
    bs_chachapoly_enc(ct, tag16, msg, 16384, msg, 16, key32, nonce12);
    TIME("chacha20poly1305-dec", 16384,
         { sink += bs_chachapoly_dec(pt, ct, 16384, tag16, msg, 16, key32, nonce12); });
  }
  BULK("nacl-secretbox-easy", bs_secretbox_easy(ct, msg, n, nonce24, key32));

  /* ---------------- AES-GCM ---------------- */
  bs_aes128gcm_setup(key16);
  bs_aes256gcm_setup(key32);
  BULK("aes128-gcm-enc", bs_aes128gcm_enc(ct, tag16, msg, n, msg, 16, key16, nonce12));
  BULK("aes256-gcm-enc", bs_aes256gcm_enc(ct, tag16, msg, n, msg, 16, key32, nonce12));
  {
    memcpy(pt, msg, 16384);
    bs_aes128gcm_enc(ct, tag16, pt, 16384, msg, 16, key16, nonce12);
    TIME("aes128-gcm-dec", 16384,
         { sink += bs_aes128gcm_dec(pt, ct, 16384, tag16, msg, 16, key16, nonce12); });
  }

  /* ---------------- Curve25519 / Ed25519 ---------------- */
  {
    uint8_t sk[32], pk[32], ss[32], sg[64];
    fill(sk, 32, 7);
    bs_x25519_base(pk, sk);
    TIME("x25519-base", 0, { bs_x25519_base(out, sk); sink += out[0]; });
    TIME("x25519-scalarmult", 0, { bs_x25519(ss, sk, pk); sink += ss[0]; });
#ifdef HAVE_REF_EXTRAS
    TIME("x25519-scalarmult-asm", 0, { bs_x25519_64(ss, sk, pk); sink += ss[0]; });
#endif
    bs_ed25519_keygen(pk, sk);
    TIME("ed25519-keygen", 0, { bs_ed25519_keygen(out, sk); sink += out[0]; });
    bs_ed25519_sign(sg, sk, msg, 64);
    TIME("ed25519-sign-64B", 0, { bs_ed25519_sign(sg, sk, msg, 64); sink += sg[0]; });
    if (!bs_ed25519_verify(pk, msg, 64, sg)) fprintf(stderr, "ed25519 self-check failed\n");
    TIME("ed25519-verify-64B", 0, { sink += bs_ed25519_verify(pk, msg, 64, sg); });
  }

  /* ---------------- P-256 ---------------- */
  {
    uint8_t sk[32], pk[64], ss[64], sg[64], nonce[32];
    fill(sk, 32, 11); sk[0] = 1;
    fill(nonce, 32, 12); nonce[0] = 1;
    if (!bs_p256_dh_i(pk, sk)) fprintf(stderr, "p256 keygen failed\n");
    TIME("p256-dh-initiator", 0, { sink += bs_p256_dh_i(ss, sk); });
    TIME("p256-dh-responder", 0, { sink += bs_p256_dh_r(ss, pk, sk); });
    if (!bs_p256_sign(sg, msg, 64, sk, nonce)) fprintf(stderr, "p256 sign failed\n");
    TIME("p256-ecdsa-sign", 0, { sink += bs_p256_sign(sg, msg, 64, sk, nonce); });
    if (!bs_p256_verify(msg, 64, pk, sg, sg + 32)) fprintf(stderr, "p256 verify self-check failed\n");
    TIME("p256-ecdsa-verify", 0, { sink += bs_p256_verify(msg, 64, pk, sg, sg + 32); });
  }

  /* ---------------- K-256 ---------------- */
  {
    uint8_t sk[32], pk[64], ss[64], sg[64], nonce[32], h[32];
    fill(sk, 32, 21); sk[0] = 1;
    fill(nonce, 32, 22); nonce[0] = 1;
    fill(h, 32, 23);
    if (!bs_k256_dh_i(pk, sk)) fprintf(stderr, "k256 keygen failed\n");
    TIME("k256-secret-to-public", 0, { sink += bs_k256_dh_i(ss, sk); });
    TIME("k256-ecdh", 0, { sink += bs_k256_dh_r(ss, pk, sk); });
    if (!bs_k256_sign(sg, h, sk, nonce)) fprintf(stderr, "k256 sign failed\n");
    TIME("k256-ecdsa-sign", 0, { sink += bs_k256_sign(sg, h, sk, nonce); });
    if (!bs_k256_verify(h, pk, sg)) fprintf(stderr, "k256 verify self-check failed\n");
    TIME("k256-ecdsa-verify", 0, { sink += bs_k256_verify(h, pk, sg); });
  }

  /* ---------------- RSA-PSS 2048 ---------------- */
  {
    uint8_t sgnt[256];
    if (!bs_rsapss_sign(2048, n_b, sizeof e_b, e_b, sizeof d_b, d_b, 0, NULL, 32, msg, sgnt))
      fprintf(stderr, "rsapss sign failed\n");
    if (!bs_rsapss_verify(2048, n_b, sizeof e_b, e_b, 0, sgnt, 32, msg))
      fprintf(stderr, "rsapss verify self-check failed\n");
    TIME("rsapss-2048-sign", 0, { sink += bs_rsapss_sign(2048, n_b, sizeof e_b, e_b, sizeof d_b, d_b, 0, NULL, 32, msg, sgnt); });
    TIME("rsapss-2048-verify", 0, { sink += bs_rsapss_verify(2048, n_b, sizeof e_b, e_b, 0, sgnt, 32, msg); });
  }

  /* ---------------- FFDHE 2048 ---------------- */
  {
    static uint8_t sk_a[256], sk_b[256], pk_a[256], pk_b[256], ss[256];
    fill(sk_a, 256, 31); sk_a[0] = 1;
    fill(sk_b, 256, 32); sk_b[0] = 1;
    bs_ffdhe2048_pub(pk_a, sk_a);
    bs_ffdhe2048_pub(pk_b, sk_b);
    TIME("ffdhe2048-secret-to-public", 0, { bs_ffdhe2048_pub(pk_a, sk_a); sink += pk_a[0]; });
    if (!bs_ffdhe2048_ss(ss, sk_a, pk_b)) fprintf(stderr, "ffdhe self-check failed\n");
    TIME("ffdhe2048-shared-secret", 0, { sink += bs_ffdhe2048_ss(ss, sk_a, pk_b); });
  }

  /* ---------------- ML-KEM and ML-DSA ----------------
   * Every operation cycles through NPQ different inputs: key generation
   * through NPQ seeds, encapsulation through NPQ messages, decapsulation
   * through NPQ ciphertexts, signing and verification through NPQ messages
   * (and their signatures).  With one fixed input the branch predictor learns
   * the outcome of every rejection-sampling test across the timing loop, and
   * a sampler whose acceptance test is a branch looks several times faster
   * than it is on fresh input (REPORT.md Part 85). */
#define NPQ 64
#ifdef BS_HAVE_MLKEM
  {
    static uint8_t kek[1568], kdk[3168], kct[1568], kss[32], kcts[NPQ][1568];
    static uint8_t kek2[1568], kdk2[3168];
    static uint8_t kd[NPQ][32], kz[32], km[NPQ][32];
    uint64_t k = 0;
    fill(&kd[0][0], sizeof kd, 61);
    fill(kz, 32, 62);
    fill(&km[0][0], sizeof km, 63);
#define MLKEM_ROWS(bits_)                                                      \
    do {                                                                       \
      bs_mlkem##bits_##_keypair(kek, kdk, kd[0], kz);                          \
      for (int j = 0; j < NPQ; j++)                                            \
        bs_mlkem##bits_##_enc(kcts[j], kss, kek, km[j]);                       \
      TIME_MIN("mlkem" #bits_ "-keypair", 0, NPQ,                              \
           { bs_mlkem##bits_##_keypair(kek2, kdk2, kd[k % NPQ], kz); k++;      \
             sink += kek2[0]; });                                               \
      TIME_MIN("mlkem" #bits_ "-encapsulate", 0, NPQ,                          \
           { bs_mlkem##bits_##_enc(kct, kss, kek, km[k % NPQ]); k++;           \
             sink += kss[0]; });                                               \
      TIME_MIN("mlkem" #bits_ "-decapsulate", 0, NPQ,                          \
           { bs_mlkem##bits_##_dec(kss, kcts[k % NPQ], kdk); k++;              \
             sink += kss[0]; });                                               \
    } while (0)
    MLKEM_ROWS(512);
    MLKEM_ROWS(768);
    MLKEM_ROWS(1024);
#undef MLKEM_ROWS
  }
#endif

#ifdef BS_HAVE_MLDSA
  {
    static uint8_t dpk[2592], dsk[4896], dsg[4627], dsgs[NPQ][4627], dpk2[2592], dsk2[4896];
    static uint8_t dxi[NPQ][32], drnd[32];
    uint64_t k = 0;
    fill(&dxi[0][0], sizeof dxi, 71);
    fill(drnd, 32, 72);
#define MLDSA_ROWS(n_)                                                         \
    do {                                                                       \
      bs_mldsa##n_##_keypair(dpk, dsk, dxi[0]);                                \
      for (int j = 0; j < NPQ; j++)                                            \
        if (!bs_mldsa##n_##_sign(dsgs[j], dsk, msg + j, 32, drnd) ||           \
            !bs_mldsa##n_##_verify(dpk, msg + j, 32, dsgs[j]))                 \
          fprintf(stderr, "mldsa" #n_ " self-check failed\n");                \
      TIME_MIN("mldsa" #n_ "-keypair", 0, NPQ,                                 \
           { bs_mldsa##n_##_keypair(dpk2, dsk2, dxi[k % NPQ]); k++;            \
             sink += dpk2[0]; });                                              \
      TIME_MIN("mldsa" #n_ "-sign", 0, NPQ,                                    \
           { sink += bs_mldsa##n_##_sign(dsg, dsk, msg + (k % NPQ), 32, drnd); \
             k++; });                                                          \
      TIME_MIN("mldsa" #n_ "-verify", 0, NPQ,                                  \
           { sink += bs_mldsa##n_##_verify(dpk, msg + (k % NPQ), 32,           \
                                           dsgs[k % NPQ]); k++; });            \
    } while (0)
    MLDSA_ROWS(44);
    MLDSA_ROWS(65);
    MLDSA_ROWS(87);
#undef MLDSA_ROWS
  }
#endif
#undef NPQ

  /* ---------------- HMAC-DRBG ---------------- */
  {
    static bs_drbg d;
    uint8_t ent[64], non[32];
    fill(ent, 64, 41);
    fill(non, 32, 42);
    memset(&d, 0, sizeof d);
    bs_drbg_init(&d, ent, 32, non, 16);
    /* The reseed interval is 1024 generates, after which generate becomes a
       no-op that returns false, so instantiation is folded into the unit. */
    TIME("hmac-drbg-sha2-256-instantiate+gen-1KiB", 1024,
         { bs_drbg_init(&d, ent, 32, non, 16); sink += bs_drbg_gen(&d, ct, 1024); });
  }

  /* ---------------- bignum ---------------- */
  {
    static bs_bnctx c;
    static uint8_t a[256], b[256];
    fill(a, 256, 51); a[0] = 1;          /* < n, since n's top byte is 0xcd */
    fill(b, 256, 52); b[0] |= 0x80;      /* a full 2048-bit exponent */
    bs_bn2048_setup(&c, n_b, a, b);
    TIME("bn2048-modexp-consttime", 0, { bs_bn2048_modexp(&c, 2048); sink += BS_BN_RES(c); });
#ifdef HAVE_REF_EXTRAS
    TIME("bn2048-modexp-consttime-32bit-limbs", 0, { bs_bn2048_modexp32(&c, 2048); sink += (uint64_t)c.res[0]; });
#endif
  }

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
