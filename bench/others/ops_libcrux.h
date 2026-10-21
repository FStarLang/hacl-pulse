/* libcrux-ml-dsa (Cryspen; Rust, with hax-extracted F* proofs of parts of
 * it) through the C ABI in others/libcrux: key generation from a 32-byte
 * seed, deterministic ML-DSA.Sign (rnd = 0) with an empty context.  Its
 * portable or AVX2 code is chosen at run time; this machine gets AVX2.
 * Keys and signatures are copied into libcrux's own types on every call
 * (a few KB of memcpy). */
#include <stdint.h>
#include <stddef.h>
#define IMPL_NAME "libcrux"

static void bo_init(void) {}

#define LC_MLDSA(P_, PK_, SK_)                                                   \
  void libcrux_mldsa##P_##_keypair(uint8_t *pk, uint8_t *sk, const uint8_t *xi); \
  int32_t libcrux_mldsa##P_##_sign(uint8_t *sig, const uint8_t *sk, const uint8_t *m, size_t n); \
  int32_t libcrux_mldsa##P_##_verify(const uint8_t *pk, const uint8_t *m, size_t n, const uint8_t *sig); \
  static uint8_t lc_dsa##P_##_pk[PK_], lc_dsa##P_##_sk[SK_], lc_dsa##P_##_sk2[SK_]; \
  static inline void bo_mldsa##P_##_keygen(uint8_t *pk, uint8_t *xi) {          \
    libcrux_mldsa##P_##_keypair(pk, lc_dsa##P_##_sk2, xi);                       \
  }                                                                              \
  static inline void bo_mldsa##P_##_setup(uint8_t *pk, uint8_t *sk) {           \
    memcpy(lc_dsa##P_##_pk, pk, PK_); memcpy(lc_dsa##P_##_sk, sk, SK_);          \
  }                                                                              \
  static inline int bo_mldsa##P_##_sign(uint8_t *sg, uint8_t *m, size_t n) {     \
    return libcrux_mldsa##P_##_sign(sg, lc_dsa##P_##_sk, m, n) == 0;             \
  }                                                                              \
  static inline int bo_mldsa##P_##_verify(uint8_t *m, size_t n, uint8_t *sg) {   \
    return libcrux_mldsa##P_##_verify(lc_dsa##P_##_pk, m, n, sg) == 0;           \
  }
#define BO_MLDSA44
#define BO_MLDSA65
#define BO_MLDSA87
LC_MLDSA(44, 1312, 2560)
LC_MLDSA(65, 1952, 4032)
LC_MLDSA(87, 2592, 4896)
