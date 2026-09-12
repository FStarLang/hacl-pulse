/* Platform entropy.  See Hacl_Random.h; this file is trusted, not verified. */

/* The library is built with -std=c11, which hides everything outside ISO C;
 * syscall(), getentropy() and ssize_t all need a feature-test macro. */
#if !defined(_WIN32) && !defined(_WIN64)
#define _GNU_SOURCE
#define _DEFAULT_SOURCE
#endif

#include "Hacl_Random.h"

#if defined(_WIN32) || defined(_WIN64)

#include <windows.h>
#include <bcrypt.h>

bool Hacl_Random_bytes(uint8_t *buf, size_t len) {
  while (len > 0) {
    /* BCryptGenRandom takes a ULONG. */
    ULONG chunk = len > 0xffffffffUL ? 0xffffffffUL : (ULONG)len;
    if (!BCRYPT_SUCCESS(BCryptGenRandom(NULL, buf, chunk,
                                        BCRYPT_USE_SYSTEM_PREFERRED_RNG)))
      return false;
    buf += chunk;
    len -= chunk;
  }
  return true;
}

#else

#include <errno.h>
#include <stdio.h>
#include <sys/types.h>
#include <unistd.h>

#if defined(__linux__)
#include <sys/syscall.h>
#elif defined(__FreeBSD__) || defined(__APPLE__) || defined(__OpenBSD__)
#include <sys/random.h>
#endif

/* One attempt at the kernel interface.  Returns the number of bytes written,
 * or -1 if the interface is unavailable (in which case the caller falls back
 * to /dev/urandom) -- a distinction ENOSYS makes for us on Linux, where a
 * binary may well run on a kernel older than the headers it was built
 * against. */
static ssize_t kernel_bytes(uint8_t *buf, size_t len) {
#if defined(__linux__) && defined(SYS_getrandom)
  /* getrandom() caps a single call at 33554431 bytes. */
  if (len > 33554431)
    len = 33554431;
  return syscall(SYS_getrandom, buf, len, 0);
#elif defined(__FreeBSD__) || defined(__APPLE__) || defined(__OpenBSD__)
  /* getentropy() caps a single call at 256 bytes. */
  if (len > 256)
    len = 256;
  return getentropy(buf, len) == 0 ? (ssize_t)len : -1;
#else
  (void)buf;
  (void)len;
  errno = ENOSYS;
  return -1;
#endif
}

static bool urandom_bytes(uint8_t *buf, size_t len) {
  FILE *f = fopen("/dev/urandom", "rb");
  if (f == NULL)
    return false;
  size_t got = fread(buf, 1, len, f);
  fclose(f);
  return got == len;
}

bool Hacl_Random_bytes(uint8_t *buf, size_t len) {
  size_t done = 0;
  while (done < len) {
    ssize_t got = kernel_bytes(buf + done, len - done);
    if (got < 0) {
      if (errno == EINTR)
        continue;
      /* No kernel interface here: one shot at /dev/urandom for the rest. */
      return urandom_bytes(buf + done, len - done);
    }
    done += (size_t)got;
  }
  return true;
}

#endif
