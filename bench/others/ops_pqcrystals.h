/* pq-crystals/dilithium, the ML-DSA reference code: ref/ (portable C) or,
 * with -DPQ_AVX2, avx2/ (C + AVX2 assembly).  Each parameter set is its own
 * build of the sources (-DDILITHIUM_MODE=2/3/5), with namespaced symbols.
 *
 * keypair() draws its seed from randombytes(), which this header provides:
 * it hands out the seed of the current key generation, so keys come from
 * the same 32-byte seed as everybody else's.  Signing is
 * signature_internal with rnd = 0 and the pure ML-DSA prefix 0x00 0x00
 * (empty context), i.e. FIPS 204 ML-DSA.Sign, deterministic variant -- the
 * same computation crypto_sign_signature does without
 * DILITHIUM_RANDOMIZED_SIGNING, without its randombytes() call. */
#include <stdint.h>
#include <stddef.h>

#ifdef PQ_AVX2
#define IMPL_NAME "pqcrystals-avx2"
#define PQ_FN(m_, f_) pqcrystals_dilithium##m_##_avx2_##f_
#else
#define IMPL_NAME "pqcrystals-ref"
#define PQ_FN(m_, f_) pqcrystals_dilithium##m_##_ref_##f_
#endif

static const uint8_t *pq_seed;
void randombytes(uint8_t *out, size_t outlen);
void randombytes(uint8_t *out, size_t outlen) {
  if (!pq_seed || outlen != 32) { fprintf(stderr, IMPL_NAME ": unexpected randombytes\n"); exit(1); }
  memcpy(out, pq_seed, 32);
}

static void bo_init(void) {}

#define PQ_MLDSA(P_, M_, PK_, SK_, SG_)                                        \
  int PQ_FN(M_, keypair)(uint8_t *pk, uint8_t *sk);                              \
  int PQ_FN(M_, signature_internal)(uint8_t *sig, size_t *siglen, const uint8_t *m, \
                                    size_t mlen, const uint8_t *pre, size_t prelen, \
                                    const uint8_t *rnd, const uint8_t *sk);      \
  int PQ_FN(M_, verify)(const uint8_t *sig, size_t siglen, const uint8_t *m,     \
                        size_t mlen, const uint8_t *ctx, size_t ctxlen,          \
                        const uint8_t *pk);                                      \
  static uint8_t pq_dsa##P_##_pk[PK_], pq_dsa##P_##_sk[SK_], pq_dsa##P_##_sk2[SK_]; \
  static inline void bo_mldsa##P_##_keygen(uint8_t *pk, uint8_t *xi) {          \
    pq_seed = xi;                                                                \
    PQ_FN(M_, keypair)(pk, pq_dsa##P_##_sk2);                                    \
    pq_seed = NULL;                                                              \
  }                                                                              \
  static inline void bo_mldsa##P_##_setup(uint8_t *pk, uint8_t *sk) {           \
    memcpy(pq_dsa##P_##_pk, pk, PK_); memcpy(pq_dsa##P_##_sk, sk, SK_);          \
  }                                                                              \
  static inline int bo_mldsa##P_##_sign(uint8_t *sg, uint8_t *m, size_t n) {     \
    static const uint8_t pre[2] = {0, 0}, rnd[32] = {0};                         \
    size_t l;                                                                    \
    return PQ_FN(M_, signature_internal)(sg, &l, m, n, pre, 2, rnd, pq_dsa##P_##_sk) == 0; \
  }                                                                              \
  static inline int bo_mldsa##P_##_verify(uint8_t *m, size_t n, uint8_t *sg) {   \
    return PQ_FN(M_, verify)(sg, SG_, m, n, NULL, 0, pq_dsa##P_##_pk) == 0; \
  }
#define BO_MLDSA44
#define BO_MLDSA65
#define BO_MLDSA87
PQ_MLDSA(44, 2, 1312, 2560, 2420)
PQ_MLDSA(65, 3, 1952, 4032, 3309)
PQ_MLDSA(87, 5, 2592, 4896, 4627)
