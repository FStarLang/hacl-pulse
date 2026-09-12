/* Platform entropy.
 *
 * This file and its implementation are handwritten C, and are part of the
 * trusted computing base: nothing about them is verified, and the quality of
 * everything seeded from here rests on the operating system's generator.
 *
 * The library itself never calls this.  Every primitive that needs random
 * bytes -- key generation, nonces, the DRBG's entropy input -- takes them as
 * an argument, so that the verified code stays a pure function of its inputs
 * and so that callers who have their own entropy source can use it.  This is
 * the source of last resort, for callers who do not.
 */

#ifndef HACL_RANDOM_H
#define HACL_RANDOM_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

/* Fill `buf[0 .. len)` with bytes from the operating system's generator.
 *
 * Returns `true` on success.  On failure `buf` is left in an unspecified
 * state and must not be used; a caller that cannot proceed without entropy
 * should abort rather than fall back to anything weaker.
 *
 *   - Windows: BCryptGenRandom with the system-preferred RNG.
 *   - Linux, FreeBSD, macOS and friends: getrandom / getentropy, retried on
 *     EINTR, falling back to /dev/urandom if the syscall is unavailable.
 *
 * Blocks, on a freshly booted system, until the kernel pool is initialized.
 * That is the intended behaviour: a non-blocking read of an uninitialized
 * pool is exactly the failure this interface exists to prevent.
 */
bool Hacl_Random_bytes(uint8_t *buf, size_t len);

#if defined(__cplusplus)
}
#endif

#endif /* HACL_RANDOM_H */
