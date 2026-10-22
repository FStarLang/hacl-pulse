/* Timing audit of the library's masked selections.
 *
 * F* proves that these functions compute the right answer.  It cannot
 * prove that they take the same time for every value of the secret,
 * because that is not a property of the program's semantics: it is a
 * property of the machine code the C compiler chose to emit, and the
 * compiler is free to turn a masked select back into a branch.  It has
 * done exactly that once already -- see test_launder.c and the section
 * "The compiler is allowed to undo a constant-time algorithm" in
 * design/notes.md -- so the question has to be asked of each one, empirically,
 * against the compiler that is actually being used.
 *
 * The method is the same throughout: run the shipped function once per
 * value of the secret it selects on, take the minimum over several
 * repetitions, and fail if the fastest and slowest values differ by more
 * than a threshold.  The repetitions are the outer loop and the values the
 * inner one, so that a stretch of interference -- another tenant, a clock
 * change -- slows one sample of every value rather than every sample of
 * one value, and the minimum discards it.  Timing each value's
 * repetitions back to back made the x25519 row fail on whichever scalar
 * happened to be running during a 60 ms stall, on CI as well as here.  A masked select is flat to a few percent.  A branch
 * on the secret is not.
 *
 * The thresholds are deliberately loose.  This is a timing test on a
 * shared machine; it is meant to catch a compiler rewriting the
 * algorithm, which shows up as tens of percent, not to resolve a cache
 * effect.
 */

#define _DEFAULT_SOURCE
#define _POSIX_C_SOURCE 199309L

#include <stdio.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#include "Hacl.h"

static double now_ns(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (double)t.tv_sec * 1e9 + (double)t.tv_nsec;
}

#define REPS 7

static int failures = 0;

/* Report the per-value timings and decide.  Prints at most the first
   sixteen values; the spread is over all of them. */
static void verdict(const char *name, int nvalues, const double *ns,
                    double threshold) {
  double lo = ns[0], hi = ns[0];
  int argmin = 0, argmax = 0;
  for (int i = 0; i < nvalues; i++) {
    if (ns[i] < lo) { lo = ns[i]; argmin = i; }
    if (ns[i] > hi) { hi = ns[i]; argmax = i; }
  }
  double spread = (hi - lo) / lo * 100.0;
  printf("  %-26s", name);
  if (nvalues <= 16) {
    for (int i = 0; i < nvalues; i++) printf(" %7.2f", ns[i]);
  } else {
    printf(" min %7.2f at %3d, max %7.2f at %3d", lo, argmin, hi, argmax);
  }
  printf("   spread %6.1f%%  %s\n", spread, spread > threshold ? "LEAK" : "ok");
  if (spread > threshold) failures++;
}

/* --- the secret-indexed table read ------------------------------------ */

/* This is the one that was caught.  It is covered in detail by
   test_launder.c at the five-limb width that Ed25519 and secp256k1 use;
   here it is checked at the four-limb width that P-256 uses, because the
   limb count is what decides whether the compiler finds the unrolled scan
   small enough to specialise. */
static void audit_table_select(void) {
  uint64_t tbl[16 * 4], res[4];
  uint64_t s = 0x243f6a8885a308d3ULL;
  for (int i = 0; i < 16 * 4; i++) {
    s = s * 6364136223846793005ULL + 1442695040888963407ULL;
    tbl[i] = s;
  }
  double ns[16];
  for (int d = 0; d < 16; d++) ns[d] = 1e30;
  for (int r = 0; r < REPS; r++) {
    for (int d = 0; d < 16; d++) {
      double t0 = now_ns();
      for (long k = 0; k < 200000; k++)
        Hacl_Bignum_Base_table_select(res, tbl, 4, (uint64_t)d);
      double dt = (now_ns() - t0) / 200000.0;
      if (dt < ns[d]) ns[d] = dt;
    }
  }
  verdict("table_select n=4", 16, ns, 75.0);
}

/* --- the Montgomery ladder ------------------------------------------- */

/* The ladder's only data-dependent choice is a conditional swap on each
   bit of the scalar.  `cswap` itself is CInline and so has no external
   definition to call; the whole scalar multiplication is checked instead,
   which is the stronger statement anyway -- if any of the 255 swaps
   branched, a scalar of all-zero bits and a scalar of all-one bits would
   not take the same time. */
static void audit_x25519(void) {
  static const uint8_t patterns[6] = { 0x00, 0xff, 0x55, 0xaa, 0x0f, 0xf0 };
  uint8_t base[32], out[32], scalar[32];
  double ns[6];
  memset(base, 0, sizeof base);
  base[0] = 9;
  for (int v = 0; v < 6; v++) ns[v] = 1e30;
  /* Short batches, many rounds: a batch is about a millisecond. */
  for (int r = 0; r < 5 * REPS; r++) {
    for (int v = 0; v < 6; v++) {
      memset(scalar, patterns[v], sizeof scalar);
      double t0 = now_ns();
      for (long k = 0; k < 20; k++) Hacl_Curve25519_scalarmult(out, scalar, base);
      double dt = (now_ns() - t0) / 20.0;
      if (dt < ns[v]) ns[v] = dt;
    }
  }
  verdict("x25519 (by scalar)", 6, ns, 10.0);
}

/* --- the bignum comparisons ------------------------------------------- */

/* Both scan the whole number and accumulate; an early exit at the first
   differing limb would leak how far two secrets agree.  The secret here is
   the position of that first difference. */
static void audit_bignum_compare(void) {
  uint64_t a[32], b[32];
  double eq[9], lt[9];
  for (int i = 0; i < 32; i++) a[i] = 0x5555555555555555ULL;
  for (int p = 0; p < 9; p++) eq[p] = lt[p] = 1e30;
  for (int r = 0; r < REPS; r++) {
    for (int p = 0; p < 9; p++) {
      memcpy(b, a, sizeof a);
      if (p < 8) b[p * 4] = a[p * 4] ^ 1ULL;
      double t0 = now_ns();
      for (long k = 0; k < 200000; k++) {
        uint64_t v = Hacl_Bignum_Base_eq_mask(a, b, 32);
        __asm__ volatile("" :: "r"(v));
      }
      double dt = (now_ns() - t0) / 200000.0;
      if (dt < eq[p]) eq[p] = dt;
      t0 = now_ns();
      for (long k = 0; k < 200000; k++) {
        uint64_t v = Hacl_Bignum_Base_lt_mask(a, b, 32);
        __asm__ volatile("" :: "r"(v));
      }
      dt = (now_ns() - t0) / 200000.0;
      if (dt < lt[p]) lt[p] = dt;
    }
  }
  verdict("bn eq_mask", 9, eq, 20.0);
  verdict("bn lt_mask", 9, lt, 20.0);
}

/* --- ML-KEM's ciphertext comparison ----------------------------------- */

/* The Fujisaki-Okamoto transform re-encrypts and compares; if the compare
   stopped at the first differing byte, the implicit-rejection branch would
   be distinguishable and the KEM would lose CCA security. */
static void audit_mlkem_compare(void) {
  static uint8_t a[1088], b[1088];
  double ns[9];
  for (int i = 0; i < 1088; i++) a[i] = (uint8_t)i;
  for (int p = 0; p < 9; p++) ns[p] = 1e30;
  for (int r = 0; r < REPS; r++) {
    for (int p = 0; p < 9; p++) {
      memcpy(b, a, sizeof a);
      if (p < 8) b[p * 136] = (uint8_t)(a[p * 136] ^ 1u);
      double t0 = now_ns();
      for (long k = 0; k < 20000; k++) {
        uint8_t v = Hacl_Impl_Select_eq_mask_bytes(a, b, 1088);
        __asm__ volatile("" :: "r"(v));
      }
      double dt = (now_ns() - t0) / 20000.0;
      if (dt < ns[p]) ns[p] = dt;
    }
  }
  verdict("mlkem eq_mask_bytes", 9, ns, 20.0);
}

/* --- the AES S-box ---------------------------------------------------- */

/* There is no S-box table: the inverse is computed in the field, which is
   seven squarings and eight multiplications, each of which is eight masked
   selects on a bit of a secret byte.  That is a lot of two-way selects on
   secret data, and the secret ranges over only 256 values, which is the
   condition that invites a compiler to enumerate them. */
static void audit_aes_sbox(void) {
  double ns[256];
  for (int v = 0; v < 256; v++) ns[v] = 1e30;
  for (int r = 0; r < REPS; r++) {
    for (int v = 0; v < 256; v++) {
      double t0 = now_ns();
      for (long k = 0; k < 100000; k++) {
        uint8_t y = Hacl_AES_Core_sbox_impl((uint8_t)v);
        __asm__ volatile("" :: "r"(y));
      }
      double dt = (now_ns() - t0) / 100000.0;
      if (dt < ns[v]) ns[v] = dt;
    }
  }
  verdict("aes sbox", 256, ns, 20.0);
}

int main(void) {
  printf("constant-time audit (ns per call, by value of the secret)\n");
  audit_table_select();
  audit_x25519();
  audit_bignum_compare();
  audit_mlkem_compare();
  audit_aes_sbox();
  if (failures) {
    printf("FAIL: %d masked selection(s) are not flat in the secret\n", failures);
    return 1;
  }
  printf("ok: every audited selection is flat in the secret\n");
  return 0;
}
