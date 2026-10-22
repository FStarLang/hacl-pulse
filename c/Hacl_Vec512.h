/* The 512-bit vector type and the AVX-512F intrinsics.
 *
 * This file is trusted, not verified.  It is the C half of
 * lib/Hacl.Vec512.fst: every function here realizes one `assume val` there,
 * and the postcondition written on that `assume val` is an axiom of the
 * library.  `tests/test_vec512.c` checks each of them against a scalar
 * transcription on random inputs.
 *
 * Everything except `Hacl_Vec512_supported` carries `target("avx512f")`, and
 * so does every generated function that reaches it, by way of the
 * `CPrologue` and `custard_c_closure_prologue` attributes on the F* side.
 * All of it is x86-64 only: those functions also carry
 * `custard_c_closure_guard "defined(__x86_64__)"`, and their callers test the
 * `Hacl.X64.x86_64` flag, which is printed as the same `#if`.  On any other
 * target this header defines nothing.
 */

#ifndef HACL_VEC512_H
#define HACL_VEC512_H

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#if defined(__x86_64__)

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

#endif

#endif /* HACL_VEC512_H */
