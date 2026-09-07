# MAC and key-derivation APIs: HMAC, HKDF, and Poly1305

This document describes the generated public C API for MACs and KDFs in
`dist/gcc-compatible/` for reimplementers. Primary headers: `Hacl_HMAC.h`,
`Hacl_HMAC_Blake2b_256.h`, `Hacl_HMAC_Blake2s_128.h`, `Hacl_Streaming_HMAC.h`,
`Hacl_HKDF.h`, `Hacl_HKDF_Blake2b_256.h`, `Hacl_HKDF_Blake2s_128.h`,
`Hacl_MAC_Poly1305.h`, `Hacl_MAC_Poly1305_Simd128.h`,
`Hacl_MAC_Poly1305_Simd256.h`, `EverCrypt_HMAC.h`, `EverCrypt_HKDF.h`, and
`EverCrypt_Poly1305.h`. Internal headers read only for representation notes:
`internal/Hacl_Streaming_HMAC.h` and `internal/Hacl_MAC_Poly1305.h`; anything
from those internal headers is non-public.

Read this with `design/conventions.md` for general C conventions, liveness,
disjointness, allocation ownership, and error-code style. Related sibling docs:
`design/README.md`, `design/api-hashes.md`, `design/api-aead-ciphers.md`,
`design/implementation.md`, and `design/surprises.md`.

## 1. API shapes and offerings

The scoped API offers HMAC over MD5, SHA-1, SHA-2, SHA-3, BLAKE2s, and BLAKE2b;
HKDF extract/expand over SHA-2 and BLAKE2 in `Hacl_*` and over a runtime-selected
EverCrypt subset; and Poly1305 as one-shot and streaming APIs. Poly1305 has
portable, 128-bit SIMD, and 256-bit SIMD modules. HACL module names are fixed
algorithm/implementation entry points; EverCrypt HMAC/HKDF are agile over a
runtime hash enum; EverCrypt Poly1305 multiplexes across compiled CPU backends.

## 2. Shared public selectors and error codes

From `Hacl_Streaming_Types.h`:

```c
#define Spec_Hash_Definitions_SHA2_224 0
#define Spec_Hash_Definitions_SHA2_256 1
#define Spec_Hash_Definitions_SHA2_384 2
#define Spec_Hash_Definitions_SHA2_512 3
#define Spec_Hash_Definitions_SHA1 4
#define Spec_Hash_Definitions_MD5 5
#define Spec_Hash_Definitions_Blake2S 6
#define Spec_Hash_Definitions_Blake2B 7
#define Spec_Hash_Definitions_SHA3_256 8
#define Spec_Hash_Definitions_SHA3_224 9
#define Spec_Hash_Definitions_SHA3_384 10
#define Spec_Hash_Definitions_SHA3_512 11
#define Spec_Hash_Definitions_Shake128 12
#define Spec_Hash_Definitions_Shake256 13

typedef uint8_t Spec_Hash_Definitions_hash_alg;
```

```c
#define Hacl_Streaming_Types_Success 0
#define Hacl_Streaming_Types_InvalidAlgorithm 1
#define Hacl_Streaming_Types_InvalidLength 2
#define Hacl_Streaming_Types_MaximumLengthExceeded 3
#define Hacl_Streaming_Types_OutOfMemory 4

typedef uint8_t Hacl_Streaming_Types_error_code;
```

`Spec_Hash_Definitions_hash_alg` is a byte-sized enum-like type. A C typedef
cannot enforce the F* supported-subset refinements: callers must validate before
agile calls. The scoped streaming APIs return `Hacl_Streaming_Types_error_code`.
Note: Poly1305 public comments say “0 = success, 1 = max length exceeded”, but
the generated code returns the shared constant
`Hacl_Streaming_Types_MaximumLengthExceeded` (`3`).

| Algorithm | `Spec_Hash_Definitions_*` | Hash/tag bytes | HMAC block bytes | HKDF max `len` |
|---|---:|---:|---:|---:|
| MD5 | `MD5`=5 | 16 | 64 | not public |
| SHA1 | `SHA1`=4 | 20 | 64 | 5100 |
| SHA2-224 | `SHA2_224`=0 | 28 | 64 | not public |
| SHA2-256 | `SHA2_256`=1 | 32 | 64 | 8160 |
| SHA2-384 | `SHA2_384`=2 | 48 | 128 | 12240 |
| SHA2-512 | `SHA2_512`=3 | 64 | 128 | 16320 |
| SHA3-224 | `SHA3_224`=9 | 28 | 144 | not public |
| SHA3-256 | `SHA3_256`=8 | 32 | 136 | not public |
| SHA3-384 | `SHA3_384`=10 | 48 | 104 | not public |
| SHA3-512 | `SHA3_512`=11 | 64 | 72 | not public |
| BLAKE2s | `Blake2S`=6 | 32 | 64 | 8160 |
| BLAKE2b | `Blake2B`=7 | 64 | 128 | 16320 |

## 3. Common preconditions

Unless a function states a narrower condition, inputs are live for the exact
length parameter, outputs are live for the exact output length and are modified,
and `void` functions do not validate preconditions at runtime. HMAC keys follow
standard HMAC handling: if `key_len > block_len`, the key is first hashed to
`HashLen`; otherwise it is zero-padded to `block_len`. The F* `keysized`
condition is `key_len` below the hash max input length and
`key_len + block_len < 2^32`.

For fixed HMAC, `dst` is disjoint from `key`; `dst`/`data` overlap is tolerated
by the spec. `data_len + block_len < 2^32`. For HKDF extract, `prk` is disjoint
from `salt` and `ikm`. For HKDF expand, `okm` is disjoint from `prk`,
`prklen >= HashLen`, and `len <= 255*HashLen`. For Poly1305 one-shot, `output`
is disjoint from `input` and `key`; key is exactly 32 bytes (`r || s`) and tag is
16 bytes.

## 4. HMAC fixed one-shot inventory

All functions return `void` and write the full HMAC tag. Buffer lengths and
limits are exactly those in the table above. The vector-width suffixes `_128` and
`_256` name implementation width, not tag size.

### `Hacl_HMAC_compute_md5`
```c
void
Hacl_HMAC_compute_md5(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-MD5. `dst` 16 bytes, key block 64 bytes.

### `Hacl_HMAC_compute_sha1`
```c
void
Hacl_HMAC_compute_sha1(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA1. `dst` 20 bytes, key block 64 bytes.

### `Hacl_HMAC_compute_sha2_224`
```c
void
Hacl_HMAC_compute_sha2_224(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA2-224. `dst` 28 bytes, key block 64 bytes.

### `Hacl_HMAC_compute_sha2_256`
```c
void
Hacl_HMAC_compute_sha2_256(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA2-256. `dst` 32 bytes, key block 64 bytes.

### `Hacl_HMAC_compute_sha2_384`
```c
void
Hacl_HMAC_compute_sha2_384(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA2-384. `dst` 48 bytes, key block 128 bytes.

### `Hacl_HMAC_compute_sha2_512`
```c
void
Hacl_HMAC_compute_sha2_512(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA2-512. `dst` 64 bytes, key block 128 bytes.

### `Hacl_HMAC_compute_sha3_224`
```c
void
Hacl_HMAC_compute_sha3_224(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA3-224. `dst` 28 bytes, key block/rate 144 bytes.

### `Hacl_HMAC_compute_sha3_256`
```c
void
Hacl_HMAC_compute_sha3_256(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA3-256. `dst` 32 bytes, key block/rate 136 bytes.

### `Hacl_HMAC_compute_sha3_384`
```c
void
Hacl_HMAC_compute_sha3_384(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA3-384. `dst` 48 bytes, key block/rate 104 bytes.

### `Hacl_HMAC_compute_sha3_512`
```c
void
Hacl_HMAC_compute_sha3_512(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-SHA3-512. `dst` 64 bytes, key block/rate 72 bytes.

### `Hacl_HMAC_compute_blake2s_32`
```c
void
Hacl_HMAC_compute_blake2s_32(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-BLAKE2s, portable/scalar implementation. `dst` 32 bytes, key
block 64 bytes.

### `Hacl_HMAC_compute_blake2b_32`
```c
void
Hacl_HMAC_compute_blake2b_32(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-BLAKE2b, portable/scalar implementation. `dst` 64 bytes, key
block 128 bytes.

### `Hacl_HMAC_Blake2b_256_compute_blake2b_256`
```c
void
Hacl_HMAC_Blake2b_256_compute_blake2b_256(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-BLAKE2b using the 256-bit vectorized BLAKE2b module. `dst` 64
bytes, key block 128 bytes. Availability is build/target dependent.

### `Hacl_HMAC_Blake2s_128_compute_blake2s_128`
```c
void
Hacl_HMAC_Blake2s_128_compute_blake2s_128(
  uint8_t *dst,
  uint8_t *key,
  uint32_t key_len,
  uint8_t *data,
  uint32_t data_len
);
```
Semantics: HMAC-BLAKE2s using the 128-bit vectorized BLAKE2s module. `dst` 32
bytes, key block 64 bytes. Availability is build/target dependent.

## 5. HKDF fixed inventory

HKDF extract computes `PRK = HMAC(salt, ikm)` and writes exactly `HashLen` bytes.
HKDF expand computes output blocks `T(1) || T(2) || ...` using a one-byte counter,
so `len <= 255*HashLen` is mandatory. All fixed functions return `void`.

### `Hacl_HKDF_expand_sha2_256`
```c
void
Hacl_HKDF_expand_sha2_256(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);
```
SHA2-256 expand. `okm` `len`, `prk` `prklen >= 32`, `info` `infolen`,
`len <= 8160`.

### `Hacl_HKDF_extract_sha2_256`
```c
void
Hacl_HKDF_extract_sha2_256(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);
```
SHA2-256 extract. `prk` 32, `salt` `saltlen`, `ikm` `ikmlen`.

### `Hacl_HKDF_expand_sha2_384`
```c
void
Hacl_HKDF_expand_sha2_384(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);
```
SHA2-384 expand. `okm` `len`, `prk` `prklen >= 48`, `info` `infolen`,
`len <= 12240`.

### `Hacl_HKDF_extract_sha2_384`
```c
void
Hacl_HKDF_extract_sha2_384(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);
```
SHA2-384 extract. `prk` 48, `salt` `saltlen`, `ikm` `ikmlen`.

### `Hacl_HKDF_expand_sha2_512`
```c
void
Hacl_HKDF_expand_sha2_512(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);
```
SHA2-512 expand. `okm` `len`, `prk` `prklen >= 64`, `info` `infolen`,
`len <= 16320`.

### `Hacl_HKDF_extract_sha2_512`
```c
void
Hacl_HKDF_extract_sha2_512(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);
```
SHA2-512 extract. `prk` 64, `salt` `saltlen`, `ikm` `ikmlen`.

### `Hacl_HKDF_expand_blake2s_32`
```c
void
Hacl_HKDF_expand_blake2s_32(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);
```
BLAKE2s portable expand. `okm` `len`, `prk` `prklen >= 32`, `info` `infolen`,
`len <= 8160`.

### `Hacl_HKDF_extract_blake2s_32`
```c
void
Hacl_HKDF_extract_blake2s_32(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);
```
BLAKE2s portable extract. `prk` 32, `salt` `saltlen`, `ikm` `ikmlen`.

### `Hacl_HKDF_expand_blake2b_32`
```c
void
Hacl_HKDF_expand_blake2b_32(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);
```
BLAKE2b portable expand. `okm` `len`, `prk` `prklen >= 64`, `info` `infolen`,
`len <= 16320`.

### `Hacl_HKDF_extract_blake2b_32`
```c
void
Hacl_HKDF_extract_blake2b_32(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);
```
BLAKE2b portable extract. `prk` 64, `salt` `saltlen`, `ikm` `ikmlen`.

### `Hacl_HKDF_Blake2b_256_expand_blake2b_256`
```c
void
Hacl_HKDF_Blake2b_256_expand_blake2b_256(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);
```
BLAKE2b 256-bit-vector expand. `okm` `len`, `prk` `prklen >= 64`, `info`
`infolen`, `len <= 16320`.

### `Hacl_HKDF_Blake2b_256_extract_blake2b_256`
```c
void
Hacl_HKDF_Blake2b_256_extract_blake2b_256(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);
```
BLAKE2b 256-bit-vector extract. `prk` 64, `salt` `saltlen`, `ikm` `ikmlen`.

### `Hacl_HKDF_Blake2s_128_expand_blake2s_128`
```c
void
Hacl_HKDF_Blake2s_128_expand_blake2s_128(
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);
```
BLAKE2s 128-bit-vector expand. `okm` `len`, `prk` `prklen >= 32`, `info`
`infolen`, `len <= 8160`.

### `Hacl_HKDF_Blake2s_128_extract_blake2s_128`
```c
void
Hacl_HKDF_Blake2s_128_extract_blake2s_128(
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);
```
BLAKE2s 128-bit-vector extract. `prk` 32, `salt` `saltlen`, `ikm` `ikmlen`.

## 6. Streaming HMAC lifecycle and types

The streaming HMAC layer is generated from the shared `Hacl.Streaming.Functor`.
It fixes a runtime implementation selector and key length at allocation time,
then supports reset-with-new-key, update, digest-without-consuming, free, and
copy.

### Public HACL implementation enum

```c
#define Hacl_Agile_Hash_MD5 0
#define Hacl_Agile_Hash_SHA1 1
#define Hacl_Agile_Hash_SHA2_224 2
#define Hacl_Agile_Hash_SHA2_256 3
#define Hacl_Agile_Hash_SHA2_384 4
#define Hacl_Agile_Hash_SHA2_512 5
#define Hacl_Agile_Hash_SHA3_224 6
#define Hacl_Agile_Hash_SHA3_256 7
#define Hacl_Agile_Hash_SHA3_384 8
#define Hacl_Agile_Hash_SHA3_512 9
#define Hacl_Agile_Hash_Blake2S_32 10
#define Hacl_Agile_Hash_Blake2S_128 11
#define Hacl_Agile_Hash_Blake2B_32 12
#define Hacl_Agile_Hash_Blake2B_256 13

typedef uint8_t Hacl_Agile_Hash_impl;
```

This enum selects an implementation, not only a hash algorithm. BLAKE2s-32 and
BLAKE2s-128 both implement BLAKE2s; BLAKE2b-32 and BLAKE2b-256 both implement
BLAKE2b. The `_128`/`_256` BLAKE2 choices may be rejected at allocation if the
build cannot compile that vector width.

### Public streaming HMAC types

```c
typedef struct Hacl_Agile_Hash_state_s_s Hacl_Agile_Hash_state_s;

typedef struct Hacl_Streaming_HMAC_Definitions_index_s
{
  Hacl_Agile_Hash_impl fst;
  uint32_t snd;
}
Hacl_Streaming_HMAC_Definitions_index;

typedef struct Hacl_Streaming_HMAC_Definitions_two_state_s
{
  uint32_t fst;
  Hacl_Agile_Hash_state_s *snd;
  Hacl_Agile_Hash_state_s *thd;
}
Hacl_Streaming_HMAC_Definitions_two_state;

typedef struct Hacl_Streaming_HMAC_agile_state_s Hacl_Streaming_HMAC_agile_state;
```

`Hacl_Agile_Hash_state_s` and `Hacl_Streaming_HMAC_agile_state` are abstract in
the public header. `Hacl_Streaming_HMAC_Definitions_index` is a concrete public
pair `(impl, key_length)`. `Hacl_Streaming_HMAC_Definitions_two_state` is public
but representation-oriented: `fst` is key length, `snd`/`thd` are inner/outer
hash states; callers should not own/free them separately.

Internal-only tags and layout (non-public):

```c
#define Hacl_Agile_Hash_MD5_a 0
#define Hacl_Agile_Hash_SHA1_a 1
#define Hacl_Agile_Hash_SHA2_224_a 2
#define Hacl_Agile_Hash_SHA2_256_a 3
#define Hacl_Agile_Hash_SHA2_384_a 4
#define Hacl_Agile_Hash_SHA2_512_a 5
#define Hacl_Agile_Hash_SHA3_224_a 6
#define Hacl_Agile_Hash_SHA3_256_a 7
#define Hacl_Agile_Hash_SHA3_384_a 8
#define Hacl_Agile_Hash_SHA3_512_a 9
#define Hacl_Agile_Hash_Blake2S_a 10
#define Hacl_Agile_Hash_Blake2S_128_a 11
#define Hacl_Agile_Hash_Blake2B_a 12
#define Hacl_Agile_Hash_Blake2B_256_a 13
```

```c
typedef struct Hacl_Streaming_HMAC_agile_state_s
{
  Hacl_Streaming_HMAC_Definitions_two_state block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_HMAC_agile_state;
```

`total_len` counts the initialized HMAC key block, so it starts at `block_len`
while the user message is empty. Usable streamed message bytes are at most
`max_input_len64(hash) - block_len`: `2^61-1 - block_len` for MD5/SHA1/SHA2-224/
SHA2-256, and `2^64-1 - block_len` for SHA2-384/SHA2-512/SHA3/BLAKE2.

### Streaming HMAC public functions

#### `Hacl_Streaming_HMAC_s1`
```c
Hacl_Agile_Hash_state_s
*Hacl_Streaming_HMAC_s1(
  Hacl_Streaming_HMAC_Definitions_index i,
  Hacl_Streaming_HMAC_Definitions_two_state s
);
```
Returns the borrowed inner hash-state pointer from `s`. `s` must match `i`.

#### `Hacl_Streaming_HMAC_s2`
```c
Hacl_Agile_Hash_state_s
*Hacl_Streaming_HMAC_s2(
  Hacl_Streaming_HMAC_Definitions_index i,
  Hacl_Streaming_HMAC_Definitions_two_state s
);
```
Returns the borrowed outer hash-state pointer from `s`. `s` must match `i`.

#### `Hacl_Streaming_HMAC_index_of_state`
```c
Hacl_Streaming_HMAC_Definitions_index
Hacl_Streaming_HMAC_index_of_state(Hacl_Streaming_HMAC_Definitions_two_state s);
```
Returns `(implementation, key_length)` by value from a valid two-state.

#### `Hacl_Streaming_HMAC_malloc_`
```c
Hacl_Streaming_Types_error_code
Hacl_Streaming_HMAC_malloc_(
  Hacl_Agile_Hash_impl impl,
  uint8_t *key,
  uint32_t key_length,
  Hacl_Streaming_HMAC_agile_state **dst
);
```
Allocates and initializes a state. `key` is `key_length` bytes; `dst` points to
one writable state-pointer slot. Returns `Success` and writes `*dst`,
`InvalidAlgorithm` for unavailable `Blake2B_256`/vec256 or `Blake2S_128`/vec128
builds, or `OutOfMemory`. Key length is fixed for later reset/copy.

#### `Hacl_Streaming_HMAC_get_impl`
```c
Hacl_Streaming_HMAC_Definitions_index
Hacl_Streaming_HMAC_get_impl(Hacl_Streaming_HMAC_agile_state *s);
```
Returns the implementation selector and fixed key length of live valid `s`.

#### `Hacl_Streaming_HMAC_reset`
```c
Hacl_Streaming_Types_error_code
Hacl_Streaming_HMAC_reset(
  Hacl_Streaming_HMAC_agile_state *state,
  uint8_t *key,
  uint32_t key_length
);
```
Reinitializes `state` with a new key and empty message. `key` is `key_length`
bytes. Returns `Success`, or `InvalidLength` if `key_length` differs from the
allocation-time key length. State remains allocated.

#### `Hacl_Streaming_HMAC_update`
```c
Hacl_Streaming_Types_error_code
Hacl_Streaming_HMAC_update(
  Hacl_Streaming_HMAC_agile_state *state,
  uint8_t *chunk,
  uint32_t chunk_len
);
```
Appends `chunk_len` bytes from live `chunk`, disjoint from the state footprint.
Returns `Success` or `MaximumLengthExceeded` if the internal total length would
exceed the underlying hash maximum.

#### `Hacl_Streaming_HMAC_digest`
```c
Hacl_Streaming_Types_error_code
Hacl_Streaming_HMAC_digest(
  Hacl_Streaming_HMAC_agile_state *state,
  uint8_t *output,
  uint32_t digest_length
);
```
Computes the current HMAC without consuming `state`. `output` is the full digest
length for the selected implementation (no truncation). The generated C ignores
`digest_length`; the F* type requires the correct output length. Returns
`Success` or `OutOfMemory` for temporary-state allocation failure.

#### `Hacl_Streaming_HMAC_free`
```c
void Hacl_Streaming_HMAC_free(Hacl_Streaming_HMAC_agile_state *state);
```
Frees an owned state from `malloc_` or `copy`. Borrowed sub-pointers become
invalid. Returns nothing.

#### `Hacl_Streaming_HMAC_copy`
```c
Hacl_Streaming_HMAC_agile_state
*Hacl_Streaming_HMAC_copy(Hacl_Streaming_HMAC_agile_state *state);
```
Deep-copies a live state, including buffered partial block and inner/outer hash
states. Returns an owned state or `NULL` on allocation failure. Copy preserves
the exact implementation and key length; it cannot copy across implementations.

## 7. Poly1305 inventory and state machine

Poly1305 key length is exactly 32 bytes, split as `r || s`; the first half is
clamped/used as `r`, and the second half is the final addition key. Tag/output
length is exactly 16 bytes. Streaming message length is capped at `0xffffffff`
bytes; `update` returns `MaximumLengthExceeded` if appending would exceed it.

The three HACL modules are separate compiled entry points: portable,
128-bit-vector, and 256-bit-vector. They are not runtime-dispatched. Runtime
multiplexing happens in `EverCrypt_Poly1305_mac`.

### Public Poly1305 types

```c
typedef struct Hacl_MAC_Poly1305_state_t_s Hacl_MAC_Poly1305_state_t;
typedef struct Hacl_MAC_Poly1305_Simd128_state_t_s Hacl_MAC_Poly1305_Simd128_state_t;
typedef struct Hacl_MAC_Poly1305_Simd256_state_t_s Hacl_MAC_Poly1305_Simd256_state_t;
```

All are abstract in public headers. Portable internal non-public layout:

```c
typedef struct Hacl_MAC_Poly1305_state_t_s
{
  uint64_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
  uint8_t *p_key;
}
Hacl_MAC_Poly1305_state_t;
```

### Portable `Hacl_MAC_Poly1305.h`

#### `Hacl_MAC_Poly1305_malloc`
```c
Hacl_MAC_Poly1305_state_t *Hacl_MAC_Poly1305_malloc(uint8_t *key);
```
Allocates/initializes state. `key` 32 bytes. Returns owned state or `NULL`.

#### `Hacl_MAC_Poly1305_reset`
```c
void Hacl_MAC_Poly1305_reset(Hacl_MAC_Poly1305_state_t *state, uint8_t *key);
```
Reinitializes state with `key` 32 bytes and empty message. Returns nothing.

#### `Hacl_MAC_Poly1305_update`
```c
Hacl_Streaming_Types_error_code
Hacl_MAC_Poly1305_update(Hacl_MAC_Poly1305_state_t *state, uint8_t *chunk, uint32_t chunk_len);
```
Appends `chunk_len` bytes. Returns `Success` or `MaximumLengthExceeded`.

#### `Hacl_MAC_Poly1305_digest`
```c
void Hacl_MAC_Poly1305_digest(Hacl_MAC_Poly1305_state_t *state, uint8_t *output);
```
Writes current 16-byte tag without consuming state. Returns nothing.

#### `Hacl_MAC_Poly1305_free`
```c
void Hacl_MAC_Poly1305_free(Hacl_MAC_Poly1305_state_t *state);
```
Frees owned state. Returns nothing.

#### `Hacl_MAC_Poly1305_mac`
```c
void Hacl_MAC_Poly1305_mac(uint8_t *output, uint8_t *input, uint32_t input_len, uint8_t *key);
```
One-shot portable MAC. `output` 16, `input` `input_len`, `key` 32. Returns
nothing.

### `Hacl_MAC_Poly1305_Simd128.h`

#### `Hacl_MAC_Poly1305_Simd128_malloc`
```c
Hacl_MAC_Poly1305_Simd128_state_t *Hacl_MAC_Poly1305_Simd128_malloc(uint8_t *key);
```
Allocates/initializes 128-bit SIMD state. `key` 32 bytes. Returns state or NULL.

#### `Hacl_MAC_Poly1305_Simd128_reset`
```c
void Hacl_MAC_Poly1305_Simd128_reset(Hacl_MAC_Poly1305_Simd128_state_t *state, uint8_t *key);
```
Reinitializes with `key` 32 bytes. Returns nothing.

#### `Hacl_MAC_Poly1305_Simd128_update`
```c
Hacl_Streaming_Types_error_code
Hacl_MAC_Poly1305_Simd128_update(
  Hacl_MAC_Poly1305_Simd128_state_t *state,
  uint8_t *chunk,
  uint32_t chunk_len
);
```
Appends bytes. Returns `Success` or `MaximumLengthExceeded`.

#### `Hacl_MAC_Poly1305_Simd128_digest`
```c
void
Hacl_MAC_Poly1305_Simd128_digest(Hacl_MAC_Poly1305_Simd128_state_t *state, uint8_t *output);
```
Writes 16-byte tag. Returns nothing.

#### `Hacl_MAC_Poly1305_Simd128_free`
```c
void Hacl_MAC_Poly1305_Simd128_free(Hacl_MAC_Poly1305_Simd128_state_t *state);
```
Frees owned state. Returns nothing.

#### `Hacl_MAC_Poly1305_Simd128_mac`
```c
void
Hacl_MAC_Poly1305_Simd128_mac(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key
);
```
One-shot 128-bit SIMD MAC. `output` 16, `input` `input_len`, `key` 32.

### `Hacl_MAC_Poly1305_Simd256.h`

#### `Hacl_MAC_Poly1305_Simd256_malloc`
```c
Hacl_MAC_Poly1305_Simd256_state_t *Hacl_MAC_Poly1305_Simd256_malloc(uint8_t *key);
```
Allocates/initializes 256-bit SIMD state. `key` 32 bytes. Returns state or NULL.

#### `Hacl_MAC_Poly1305_Simd256_reset`
```c
void Hacl_MAC_Poly1305_Simd256_reset(Hacl_MAC_Poly1305_Simd256_state_t *state, uint8_t *key);
```
Reinitializes with `key` 32 bytes. Returns nothing.

#### `Hacl_MAC_Poly1305_Simd256_update`
```c
Hacl_Streaming_Types_error_code
Hacl_MAC_Poly1305_Simd256_update(
  Hacl_MAC_Poly1305_Simd256_state_t *state,
  uint8_t *chunk,
  uint32_t chunk_len
);
```
Appends bytes. Returns `Success` or `MaximumLengthExceeded`.

#### `Hacl_MAC_Poly1305_Simd256_digest`
```c
void
Hacl_MAC_Poly1305_Simd256_digest(Hacl_MAC_Poly1305_Simd256_state_t *state, uint8_t *output);
```
Writes 16-byte tag. Returns nothing.

#### `Hacl_MAC_Poly1305_Simd256_free`
```c
void Hacl_MAC_Poly1305_Simd256_free(Hacl_MAC_Poly1305_Simd256_state_t *state);
```
Frees owned state. Returns nothing.

#### `Hacl_MAC_Poly1305_Simd256_mac`
```c
void
Hacl_MAC_Poly1305_Simd256_mac(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key
);
```
One-shot 256-bit SIMD MAC. `output` 16, `input` `input_len`, `key` 32.

## 8. EverCrypt agile and multiplexing APIs

EverCrypt HMAC/HKDF support only SHA1, SHA2-256, SHA2-384, SHA2-512, BLAKE2s,
and BLAKE2b. MD5, SHA2-224, all SHA3 variants, SHAKE128/256, and other byte
values are unsupported. `EverCrypt_HMAC_is_supported_alg` exposes the query;
HKDF has no separate query but uses the same supported set. Passing unsupported
values to generated `void` agile functions reaches a KaRaMeL incomplete-match
abort (`KRML_HOST_EXIT(253U)`) rather than returning an error.

### `EverCrypt_HMAC_is_supported_alg`
```c
bool EverCrypt_HMAC_is_supported_alg(Spec_Hash_Definitions_hash_alg uu___);
```
Returns true for SHA1, SHA2-256/384/512, BLAKE2s, and BLAKE2b; false otherwise.

```c
typedef Spec_Hash_Definitions_hash_alg EverCrypt_HMAC_supported_alg;
```
This typedef is public but not runtime-enforcing.

### `EverCrypt_HMAC_compute`
```c
void
EverCrypt_HMAC_compute(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *mac,
  uint8_t *key,
  uint32_t keylen,
  uint8_t *data,
  uint32_t datalen
);
```
Computes agile one-shot HMAC. `mac` length is HashLen for `a`: SHA1 20,
SHA2-256/BLAKE2s 32, SHA2-384 48, SHA2-512/BLAKE2b 64. `key` is `keylen`,
`data` is `datalen`. `key` is disjoint from `mac`; `mac`/`data` overlap is
allowed. Key and data near 4GB must satisfy the HMAC size conditions.

### `EverCrypt_HKDF_expand`
```c
void
EverCrypt_HKDF_expand(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *okm,
  uint8_t *prk,
  uint32_t prklen,
  uint8_t *info,
  uint32_t infolen,
  uint32_t len
);
```
Agile HKDF-Expand. Supported `a` as above. `okm` is `len`; `prk` is `prklen >=
HashLen`; `info` is `infolen`; `okm` is disjoint from `prk`. Bounds: SHA1 5100,
SHA2-256/BLAKE2s 8160, SHA2-384 12240, SHA2-512/BLAKE2b 16320.

### `EverCrypt_HKDF_extract`
```c
void
EverCrypt_HKDF_extract(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *prk,
  uint8_t *salt,
  uint32_t saltlen,
  uint8_t *ikm,
  uint32_t ikmlen
);
```
Agile HKDF-Extract. `prk` is HashLen bytes; `salt` is `saltlen`; `ikm` is
`ikmlen`; `prk` is disjoint from `salt` and `ikm`.

### `EverCrypt_Poly1305_mac`
```c
void EverCrypt_Poly1305_mac(uint8_t *output, uint8_t *input, uint32_t input_len, uint8_t *key);
```
One-shot Poly1305 with runtime backend multiplexing. `output` 16 bytes, `input`
`input_len` bytes, `key` 32 bytes; output is disjoint from input and key. The
generated code checks `EverCrypt_AutoConfig2_has_vec256()` and uses
`Hacl_MAC_Poly1305_Simd256_mac` if compiled/available, else checks vec128 and
uses `Hacl_MAC_Poly1305_Simd128_mac`, else falls back to Vale Poly1305 when
compiled or to portable `Hacl_MAC_Poly1305_mac`.

## 9. Notes for reimplementers

- HACL exposes separate compiled modules per vector width; do not infer runtime
  dispatch from names like `Simd128` or `Blake2b_256`.
- BLAKE2 HMAC/HKDF `_128`/`_256` suffixes indicate vector width, not output
  size: BLAKE2s outputs 32 bytes and BLAKE2b outputs 64 bytes.
- Streaming HMAC uses a runtime-tagged agile state and fixes key length in the
  index so reset/copy never change allocation size.
- Streaming HMAC `digest_length` is not a truncation parameter; write the full
  digest or reject in a safer reimplementation.
- HKDF expand is bounded by the one-byte counter: `255 * HashLen`.
- Use `EverCrypt_HMAC_is_supported_alg` before EverCrypt HMAC/HKDF. Streaming
  HMAC has no query but reports unavailable vector BLAKE2 choices via
  `InvalidAlgorithm`. EverCrypt Poly1305 performs its own CPU-feature dispatch.
- Generated C often aborts for enum cases ruled out by F* refinements. A
  reimplementation in a less-refined language should validate and return a
  recoverable error instead.
