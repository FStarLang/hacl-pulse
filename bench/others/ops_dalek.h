/* The dalek-cryptography Rust crates (curve25519-dalek 4, x25519-dalek 2,
 * ed25519-dalek 2), through the small staticlib in dalek/, built with
 * LTO and -C target-cpu=native.  curve25519-dalek picks its AVX2 backend at
 * run time; its AVX-512 IFMA backend needs a CPU this machine lacks. */
#include <stdint.h>

#define IMPL_NAME "dalek"

void dalek_x25519(uint8_t *out, const uint8_t *sk, const uint8_t *pk);
void *dalek_ed25519_key(const uint8_t *seed);
void dalek_ed25519_public(const void *k, uint8_t *pk);
void dalek_ed25519_sign(const void *k, uint8_t *sig, const uint8_t *m, size_t n);
int dalek_ed25519_verify(const uint8_t *pk, const uint8_t *m, size_t n, const uint8_t *sig);

static void bo_init(void) {}

#define BO_X25519
static inline void bo_x25519(uint8_t *o, uint8_t *s, uint8_t *p) { dalek_x25519(o, s, p); }

static void *dk_key;
#define BO_ED25519_SIGN
static inline void bo_ed25519_setup(uint8_t *seed) { dk_key = dalek_ed25519_key(seed); }
static inline void bo_ed25519_sign(uint8_t *sg, uint8_t *m, size_t n) { dalek_ed25519_sign(dk_key, sg, m, n); }
#define BO_ED25519_VERIFY
static inline int bo_ed25519_verify(uint8_t *pk, uint8_t *m, size_t n, uint8_t *sg) { return dalek_ed25519_verify(pk, m, n, sg); }
