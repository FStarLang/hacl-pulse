/* mldsa-native (pq-code-package), the C + x86-64 AVX2 assembly ML-DSA that
 * AWS-LC also imports; built here directly, as one compilation unit per
 * parameter set (its "monolithic multilevel" build), with the native
 * arithmetic and FIPS202 backends.  Needs, on the command line:
 *   -DMLD_CONFIG_MULTILEVEL_BUILD -DMLD_CONFIG_USE_NATIVE_BACKEND_ARITH
 *   -DMLD_CONFIG_USE_NATIVE_BACKEND_FIPS202 -I <mldsa-native>/mldsa
 * and mldsa_native_asm.S assembled with the same flags plus
 * -DMLD_CONFIG_MULTILEVEL_WITH_SHARED.
 *
 * Keys come from keypair_internal (a 32-byte seed); signing is
 * signature_internal with rnd = 0 and the pure ML-DSA prefix 0x00 0x00
 * (empty context) -- exactly FIPS 204 ML-DSA.Sign, deterministic variant. */
#include <stdint.h>
#include <stddef.h>
#define IMPL_NAME "mldsa-native"

int randombytes(uint8_t *out, size_t outlen);
int randombytes(uint8_t *out, size_t outlen) {
  (void)out; (void)outlen;
  fprintf(stderr, "mldsa-native: unexpected randombytes\n");
  exit(1);
}

#define MLD_CONFIG_MULTILEVEL_WITH_SHARED
#define MLD_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#define MLD_CONFIG_PARAMETER_SET 44
#include "mldsa_native.c"
#undef MLD_CONFIG_MULTILEVEL_WITH_SHARED
#undef MLD_CONFIG_PARAMETER_SET
#define MLD_CONFIG_MULTILEVEL_NO_SHARED
#define MLD_CONFIG_PARAMETER_SET 65
#include "mldsa_native.c"
#undef MLD_CONFIG_MONOBUILD_KEEP_SHARED_HEADERS
#undef MLD_CONFIG_PARAMETER_SET
#define MLD_CONFIG_PARAMETER_SET 87
#include "mldsa_native.c"
#undef MLD_CONFIG_PARAMETER_SET

static void bo_init(void) {}
static void mn_die(const char *w) { fprintf(stderr, "mldsa-native: %s failed\n", w); exit(1); }

#define MN_MLDSA(P_, PK_, SK_)                                                   \
  static uint8_t mn_dsa##P_##_pk[PK_], mn_dsa##P_##_sk[SK_], mn_dsa##P_##_sk2[SK_]; \
  static inline void bo_mldsa##P_##_keygen(uint8_t *pk, uint8_t *xi) {          \
    if (PQCP_MLDSA_NATIVE_MLDSA##P_##_keypair_internal(pk, mn_dsa##P_##_sk2, xi)) \
      mn_die("ml-dsa-" #P_ " keypair_internal");                                 \
  }                                                                              \
  static inline void bo_mldsa##P_##_setup(uint8_t *pk, uint8_t *sk) {           \
    memcpy(mn_dsa##P_##_pk, pk, PK_); memcpy(mn_dsa##P_##_sk, sk, SK_);          \
  }                                                                              \
  static inline int bo_mldsa##P_##_sign(uint8_t *sg, uint8_t *m, size_t n) {     \
    static const uint8_t pre[2] = {0, 0}, rnd[32] = {0};                         \
    return PQCP_MLDSA_NATIVE_MLDSA##P_##_signature_internal(sg, m, n, pre, 2, rnd, \
                                                            mn_dsa##P_##_sk, 0) == 0; \
  }                                                                              \
  static inline int bo_mldsa##P_##_verify(uint8_t *m, size_t n, uint8_t *sg) {   \
    return PQCP_MLDSA_NATIVE_MLDSA##P_##_verify(sg, m, n, NULL, 0, mn_dsa##P_##_pk) == 0; \
  }
#define BO_MLDSA44
#define BO_MLDSA65
#define BO_MLDSA87
MN_MLDSA(44, 1312, 2560)
MN_MLDSA(65, 1952, 4032)
MN_MLDSA(87, 2592, 4896)
