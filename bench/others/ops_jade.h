/* libjade (formosa-crypto, release 2023.05-2): Jasmin implementations
 * shipped as pre-generated assembly, linked directly.  Every row uses the
 * fastest variant the release has for this CPU.  libjade's Kyber is the
 * round-3 version, not ML-KEM, so there is no ML-KEM row. */
#include <stdint.h>

#define IMPL_NAME "libjade"

int jade_hash_sha256_amd64_ref(uint8_t *, const uint8_t *, uint64_t);
int jade_hash_sha512_amd64_ref(uint8_t *, const uint8_t *, uint64_t);
int jade_hash_sha3_256_amd64_avx2(uint8_t *, const uint8_t *, uint64_t);
int jade_xof_shake128_amd64_avx2(uint8_t *, uint64_t, const uint8_t *, uint64_t);
int jade_stream_chacha_chacha20_ietf_amd64_avx2_xor(uint8_t *, const uint8_t *, uint64_t, const uint8_t *, const uint8_t *);
int jade_stream_salsa20_salsa20_amd64_avx2_xor(uint8_t *, const uint8_t *, uint64_t, const uint8_t *, const uint8_t *);
int jade_onetimeauth_poly1305_amd64_avx2(uint8_t *, const uint8_t *, uint64_t, const uint8_t *);
int jade_secretbox_xsalsa20poly1305_amd64_avx2(uint8_t *, const uint8_t *, uint64_t, const uint8_t *, const uint8_t *);
int jade_scalarmult_curve25519_amd64_mulx(uint8_t *, const uint8_t *, const uint8_t *);

static void bo_init(void) {}

#define BO_SHA256
static inline void bo_sha256(uint8_t *o, uint8_t *m, size_t n) { jade_hash_sha256_amd64_ref(o, m, n); }
#define BO_SHA512
static inline void bo_sha512(uint8_t *o, uint8_t *m, size_t n) { jade_hash_sha512_amd64_ref(o, m, n); }
#define BO_SHA3_256
static inline void bo_sha3_256(uint8_t *o, uint8_t *m, size_t n) { jade_hash_sha3_256_amd64_avx2(o, m, n); }
#define BO_SHAKE128
static inline void bo_shake128(uint8_t *o, size_t ol, uint8_t *m, size_t n) { jade_xof_shake128_amd64_avx2(o, ol, m, n); }

#define BO_POLY1305
static inline void bo_poly1305(uint8_t *o, uint8_t *m, size_t n, uint8_t *k) { jade_onetimeauth_poly1305_amd64_avx2(o, m, n, k); }
#define BO_CHACHA20
static inline void bo_chacha20(uint8_t *c, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { jade_stream_chacha_chacha20_ietf_amd64_avx2_xor(c, m, n, v, k); }
#define BO_SALSA20
static inline void bo_salsa20(uint8_t *c, uint8_t *m, size_t n, uint8_t *k, uint8_t *v) { jade_stream_salsa20_salsa20_amd64_avx2_xor(c, m, n, v, k); }

/* NaCl calling convention: the plaintext is preceded by 32 zero bytes and
   the box by 16, so the message is staged once into a padded buffer (the
   driver's message never changes) and the box is left where libjade
   writes it: 16 zero bytes, then tag || ciphertext, as in secretbox_easy. */
static uint8_t jd_in[(1 << 18) + 64 + 32], jd_out[(1 << 18) + 64 + 32];
static const uint8_t *jd_src;
static size_t jd_have;
#define BO_SECRETBOX
#define BO_SECRETBOX_RESULT (jd_out + 16)
static inline void bo_secretbox(uint8_t *c, uint8_t *m, size_t n, uint8_t *v, uint8_t *k) {
  (void)c;
  if (m != jd_src || n > jd_have) {
    memcpy(jd_in + 32, m, n);
    jd_src = m;
    jd_have = n;
  }
  jade_secretbox_xsalsa20poly1305_amd64_avx2(jd_out, jd_in, n + 32, v, k);
}

#define BO_X25519
static inline void bo_x25519(uint8_t *o, uint8_t *s, uint8_t *p) { jade_scalarmult_curve25519_amd64_mulx(o, s, p); }
