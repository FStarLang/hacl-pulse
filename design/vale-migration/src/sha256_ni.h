/* SHA-256 compression using the SHA-NI extensions, via intrinsics.
 *
 * Measured at exact parity (1.00x) with dist/vale/sha256-x86_64-*.S on both
 * gcc and clang. Bit-exact against both the Vale routine and HACL*'s
 * portable C.
 *
 * Prototype for evaluating a Vale -> C migration; see ../README.md.
 */

#ifndef SHA256_NI_H
#define SHA256_NI_H

#include <stdint.h>

/* Processes num_blocks 64-byte blocks, updating the 8-word state in place.
 * state is in the usual a..h order. Padding/length are the caller's problem,
 * exactly like Vale's sha256_update. */
void sha256_ni_update(uint32_t *state, const uint8_t *data, uint64_t num_blocks);

#endif /* SHA256_NI_H */
