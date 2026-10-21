/* The 512-bit vector type and the AVX-512F intrinsics.
 *
 * This file is trusted, not verified.  It is the C half of
 * lib/Hacl.Vec512.fst: every function here realizes one `assume val` there,
 * and the postcondition written on that `assume val` is an axiom of the
 * library.  `tests/test_vec512.c` checks each of them against a scalar
 * transcription on random inputs.
 *
 * Everything except `Hacl_Vec512_supported` carries `target("avx512f")`, and
 * so does every generated function that reaches it.  On a target that is not
 * x86, `Hacl_Vec512_supported` is false and the rest of this file is
 * unreachable; the bodies are there so that the program links.
 */

#ifndef HACL_VEC512_H
#define HACL_VEC512_H

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#if defined(__x86_64__) || defined(__i386__)

#include <immintrin.h>

typedef __m512i Hacl_Vec512_t;

#define HACL_VEC512 \
  __attribute__((target("avx512f"), always_inline)) static inline

/* Unaligned, because an F* array carries no alignment. */
HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_load(uint8_t *p) {
  return _mm512_loadu_si512((const void *)p);
}

HACL_VEC512 void Hacl_Vec512_store(uint8_t *p, Hacl_Vec512_t x) {
  _mm512_storeu_si512((void *)p, x);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_zero(void) {
  return _mm512_setzero_si512();
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_bcast(uint32_t x) {
  return _mm512_set1_epi32((int)x);
}

/* `_mm512_set_epi32` takes its arguments from the top lane down. */
HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_iota(void) {
  return _mm512_set_epi32(15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1,
                          0);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_add32(Hacl_Vec512_t a,
                                            Hacl_Vec512_t b) {
  return _mm512_add_epi32(a, b);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_xor(Hacl_Vec512_t a, Hacl_Vec512_t b) {
  return _mm512_xor_si512(a, b);
}

/* `_mm512_rol_epi32` wants an immediate.  Every call site passes a literal,
 * so after inlining exactly one case survives; the variable-count rotate
 * covers anything else. */
HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_rotl(Hacl_Vec512_t a, uint32_t s) {
  switch (s) {
  case 16: return _mm512_rol_epi32(a, 16);
  case 12: return _mm512_rol_epi32(a, 12);
  case 8: return _mm512_rol_epi32(a, 8);
  case 7: return _mm512_rol_epi32(a, 7);
  default: return _mm512_rolv_epi32(a, _mm512_set1_epi32((int)s));
  }
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_unpacklo32(Hacl_Vec512_t a,
                                                 Hacl_Vec512_t b) {
  return _mm512_unpacklo_epi32(a, b);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_unpackhi32(Hacl_Vec512_t a,
                                                 Hacl_Vec512_t b) {
  return _mm512_unpackhi_epi32(a, b);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_unpacklo64(Hacl_Vec512_t a,
                                                 Hacl_Vec512_t b) {
  return _mm512_unpacklo_epi64(a, b);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_unpackhi64(Hacl_Vec512_t a,
                                                 Hacl_Vec512_t b) {
  return _mm512_unpackhi_epi64(a, b);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_sel_lo(Hacl_Vec512_t a,
                                             Hacl_Vec512_t b) {
  return _mm512_shuffle_i32x4(a, b, 0x44);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_sel_hi(Hacl_Vec512_t a,
                                             Hacl_Vec512_t b) {
  return _mm512_shuffle_i32x4(a, b, 0xEE);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_sel_even(Hacl_Vec512_t a,
                                               Hacl_Vec512_t b) {
  return _mm512_shuffle_i32x4(a, b, 0x88);
}

HACL_VEC512 Hacl_Vec512_t Hacl_Vec512_sel_odd(Hacl_Vec512_t a,
                                              Hacl_Vec512_t b) {
  return _mm512_shuffle_i32x4(a, b, 0xDD);
}

static inline bool Hacl_Vec512_supported(void) {
#if defined(__GNUC__)
  __builtin_cpu_init();
  return __builtin_cpu_supports("avx512f");
#else
  return false;
#endif
}

#else /* not x86 */

typedef struct {
  uint32_t w[16];
} Hacl_Vec512_t;

/* Unreachable: every caller is guarded by Hacl_Vec512_supported.  They are
 * defined rather than merely declared so that the program links. */
static inline Hacl_Vec512_t Hacl_Vec512_zero(void) {
  Hacl_Vec512_t r;
  memset(&r, 0, sizeof r);
  return r;
}
static inline Hacl_Vec512_t Hacl_Vec512_load(uint8_t *p) {
  Hacl_Vec512_t r;
  memcpy(&r, p, 64);
  return r;
}
static inline void Hacl_Vec512_store(uint8_t *p, Hacl_Vec512_t x) {
  memcpy(p, &x, 64);
}
static inline Hacl_Vec512_t Hacl_Vec512_bcast(uint32_t x) {
  Hacl_Vec512_t r;
  for (int i = 0; i < 16; i++) r.w[i] = x;
  return r;
}
static inline Hacl_Vec512_t Hacl_Vec512_iota(void) {
  Hacl_Vec512_t r;
  for (int i = 0; i < 16; i++) r.w[i] = (uint32_t)i;
  return r;
}
static inline Hacl_Vec512_t Hacl_Vec512_rotl(Hacl_Vec512_t a, uint32_t s) {
  (void)s;
  return a;
}
#define HACL_VEC512_STUB2(name)                                              \
  static inline Hacl_Vec512_t name(Hacl_Vec512_t a, Hacl_Vec512_t b) {       \
    (void)b;                                                                 \
    return a;                                                                \
  }
HACL_VEC512_STUB2(Hacl_Vec512_add32)
HACL_VEC512_STUB2(Hacl_Vec512_xor)
HACL_VEC512_STUB2(Hacl_Vec512_unpacklo32)
HACL_VEC512_STUB2(Hacl_Vec512_unpackhi32)
HACL_VEC512_STUB2(Hacl_Vec512_unpacklo64)
HACL_VEC512_STUB2(Hacl_Vec512_unpackhi64)
HACL_VEC512_STUB2(Hacl_Vec512_sel_lo)
HACL_VEC512_STUB2(Hacl_Vec512_sel_hi)
HACL_VEC512_STUB2(Hacl_Vec512_sel_even)
HACL_VEC512_STUB2(Hacl_Vec512_sel_odd)
#undef HACL_VEC512_STUB2
static inline bool Hacl_Vec512_supported(void) { return false; }

#endif

#endif /* HACL_VEC512_H */
