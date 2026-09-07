# Hash-function public API: HACL* and EverCrypt

This chapter documents the public hash API generated in `dist/gcc-compatible/` for a reimplementation. It follows the conventions in [conventions.md](conventions.md) and should be read with [architecture.md](architecture.md), [implementation.md](implementation.md), and [surprises.md](surprises.md). Sibling API chapters: [api-macs-kdf.md](api-macs-kdf.md), [api-aead-ciphers.md](api-aead-ciphers.md), [api-curves.md](api-curves.md), [api-bignum.md](api-bignum.md), and [api-pq-hpke-random.md](api-pq-hpke-random.md). If present, [README.md](README.md) is the index.

## 1. Overview

Algorithms exposed by the headers in this scope:

| Family | Public variants | Digest bytes | Block/rate bytes | Status |
|---|---:|---:|---:|---|
| MD5 | `Spec_Hash_Definitions_MD5` | 16 | 64 | Legacy/deprecated; kept for compatibility. |
| SHA-1 | `Spec_Hash_Definitions_SHA1` | 20 | 64 | Legacy/deprecated; kept for compatibility. |
| SHA-2 | SHA-224, SHA-256, SHA-384, SHA-512 | 28, 32, 48, 64 | 64, 64, 128, 128 | Fixed-length hashes. |
| SHA-3 | SHA3-224, SHA3-256, SHA3-384, SHA3-512 | 28, 32, 48, 64 | rates 144, 136, 104, 72 | Keccak sponge hashes. |
| SHAKE | SHAKE128, SHAKE256 | caller-chosen | rates 168, 136 | Extendable-output functions (XOFs). |
| BLAKE2 | BLAKE2s, BLAKE2b | 1..32, 1..64 (defaults 32, 64) | 64, 128 | Keyed or unkeyed. |

The public API has four shapes:

1. **One-shot hash**: a function hashes an entire input buffer into an output buffer.
2. **Core/block/update-level API**: lower-level state and block routines for SHA-3/SHAKE are public; most MD/SHA-2/BLAKE2 core functions are in `internal/` headers and are not public ABI.
3. **Streaming/incremental API**: `malloc`/`reset`/`update`/`digest`/`free`/`copy`, with algorithm-specific state objects. `digest` does not consume the state.
4. **SIMD-parallel multi-buffer API**: SHA-2 4x/8x, SHA-3 4x, and SIMD BLAKE2 variants process several equal-length messages in parallel.

Unless stated otherwise, all pointers must be live, non-NULL, suitably aligned for their C type, and point to the number of bytes documented below. Output buffers must not overlap input buffers for one-shot and multi-buffer calls; state buffers must not overlap input/output buffers. `malloc`-style functions can return `NULL` on allocation failure.

## 2. Public data types and constants

### 2.1 Hash algorithm enumeration (`Hacl_Streaming_Types.h`)

This is not a C `enum`; it is a `uint8_t` plus macros. Numeric values are ABI.

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

`Spec.Hash.Definitions` says the source inductive is append-only; the odd SHA3 order is deliberate: SHA3-256 was emitted before SHA3-224.

### 2.2 Streaming error codes (`Hacl_Streaming_Types.h`)

```c
#define Hacl_Streaming_Types_Success 0
#define Hacl_Streaming_Types_InvalidAlgorithm 1
#define Hacl_Streaming_Types_InvalidLength 2
#define Hacl_Streaming_Types_MaximumLengthExceeded 3
#define Hacl_Streaming_Types_OutOfMemory 4

typedef uint8_t Hacl_Streaming_Types_error_code;
```

Most HACL streaming `update` functions return `Hacl_Streaming_Types_Success` or `Hacl_Streaming_Types_MaximumLengthExceeded`; some header comments still say “0 = success, 1 = max length exceeded”, which is stale relative to the public constants.

### 2.3 Generic MD streaming states

Public header:

```c
typedef struct Hacl_Streaming_MD_state_32_s Hacl_Streaming_MD_state_32;

typedef struct Hacl_Streaming_MD_state_64_s Hacl_Streaming_MD_state_64;
```

Internal definition, for implementers only (`dist/gcc-compatible/internal/Hacl_Streaming_Types.h`):

```c
typedef struct Hacl_Streaming_MD_state_32_s
{
  uint32_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_MD_state_32;

typedef struct Hacl_Streaming_MD_state_64_s
{
  uint64_t *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Streaming_MD_state_64;
```

Clients should treat both as abstract. The concrete fields are useful for reimplementers: a word-array compression state, a partial-block buffer, and a 64-bit total length.

### 2.4 Algorithm-specific streaming state aliases

```c
typedef Hacl_Streaming_MD_state_32 Hacl_Hash_MD5_state_t;
typedef Hacl_Streaming_MD_state_32 Hacl_Hash_SHA1_state_t;
typedef Hacl_Streaming_MD_state_32 Hacl_Hash_SHA2_state_t_224;
typedef Hacl_Streaming_MD_state_32 Hacl_Hash_SHA2_state_t_256;
typedef Hacl_Streaming_MD_state_64 Hacl_Hash_SHA2_state_t_384;
typedef Hacl_Streaming_MD_state_64 Hacl_Hash_SHA2_state_t_512;
typedef struct Hacl_Hash_SHA3_state_t_s Hacl_Hash_SHA3_state_t;
```

The SHA-3 public type is incomplete. Internal definition:

```c
typedef struct Hacl_Hash_SHA3_hash_buf_s
{
  Spec_Hash_Definitions_hash_alg fst;
  uint64_t *snd;
}
Hacl_Hash_SHA3_hash_buf;

typedef struct Hacl_Hash_SHA3_state_t_s
{
  Hacl_Hash_SHA3_hash_buf block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Hash_SHA3_state_t;
```

### 2.5 BLAKE2 parameter and state types

Public BLAKE2 parameter type is shared by BLAKE2b and BLAKE2s C APIs:

```c
typedef struct Hacl_Hash_Blake2b_blake2_params_s
{
  uint8_t digest_length;
  uint8_t key_length;
  uint8_t fanout;
  uint8_t depth;
  uint32_t leaf_length;
  uint64_t node_offset;
  uint8_t node_depth;
  uint8_t inner_length;
  uint8_t *salt;
  uint8_t *personal;
}
Hacl_Hash_Blake2b_blake2_params;

typedef struct Hacl_Hash_Blake2b_index_s
{
  uint8_t key_length;
  uint8_t digest_length;
  bool last_node;
}
Hacl_Hash_Blake2b_index;
```

Buffer lengths inside `params`: for BLAKE2b, `salt` and `personal` point to 16 bytes each; for BLAKE2s, 8 bytes each. `digest_length` is 1..64 for BLAKE2b and 1..32 for BLAKE2s. `key_length` is 0..64 for BLAKE2b and 0..32 for BLAKE2s. Defaults are unkeyed, fanout 1, depth 1, zero salt/personal, default digest length.

Public state declarations are abstract:

```c
typedef struct Hacl_Hash_Blake2b_block_state_t_s Hacl_Hash_Blake2b_block_state_t;
typedef struct Hacl_Hash_Blake2b_state_t_s Hacl_Hash_Blake2b_state_t;
typedef struct Hacl_Hash_Blake2s_block_state_t_s Hacl_Hash_Blake2s_block_state_t;
typedef struct Hacl_Hash_Blake2s_state_t_s Hacl_Hash_Blake2s_state_t;
typedef struct Hacl_Hash_Blake2b_Simd256_block_state_t_s Hacl_Hash_Blake2b_Simd256_block_state_t;
typedef struct Hacl_Hash_Blake2b_Simd256_state_t_s Hacl_Hash_Blake2b_Simd256_state_t;
typedef struct Hacl_Hash_Blake2s_Simd128_block_state_t_s Hacl_Hash_Blake2s_Simd128_block_state_t;
typedef struct Hacl_Hash_Blake2s_Simd128_state_t_s Hacl_Hash_Blake2s_Simd128_state_t;
```

Internal portable BLAKE2b layout:

```c
typedef struct Hacl_Hash_Blake2b_block_state_t_s
{
  uint8_t fst;
  uint8_t snd;
  bool thd;
  Hacl_Streaming_Types_two_pointers f3;
}
Hacl_Hash_Blake2b_block_state_t;

typedef struct Hacl_Hash_Blake2b_state_t_s
{
  Hacl_Hash_Blake2b_block_state_t block_state;
  uint8_t *buf;
  uint64_t total_len;
}
Hacl_Hash_Blake2b_state_t;
```

Portable BLAKE2s and SIMD BLAKE2 internal layouts differ; do not assume these state objects are layout-compatible.

### 2.6 BLAKE2 size macros

```c
#define HACL_HASH_BLAKE2B_BLOCK_BYTES (128U)
#define HACL_HASH_BLAKE2B_OUT_BYTES (64U)
#define HACL_HASH_BLAKE2B_KEY_BYTES (64U)
#define HACL_HASH_BLAKE2B_SALT_BYTES (16U)
#define HACL_HASH_BLAKE2B_PERSONAL_BYTES (16U)
#define HACL_HASH_BLAKE2S_BLOCK_BYTES (64U)
#define HACL_HASH_BLAKE2S_OUT_BYTES (32U)
#define HACL_HASH_BLAKE2S_KEY_BYTES (32U)
#define HACL_HASH_BLAKE2S_SALT_BYTES (8U)
#define HACL_HASH_BLAKE2S_PERSONAL_BYTES (8U)
#define HACL_HASH_BLAKE2B_SIMD256_BLOCK_BYTES (128U)
#define HACL_HASH_BLAKE2B_SIMD256_OUT_BYTES (64U)
#define HACL_HASH_BLAKE2B_SIMD256_KEY_BYTES (64U)
#define HACL_HASH_BLAKE2B_SIMD256_SALT_BYTES (16U)
#define HACL_HASH_BLAKE2B_SIMD256_PERSONAL_BYTES (16U)
#define HACL_HASH_BLAKE2S_SIMD128_BLOCK_BYTES (64U)
#define HACL_HASH_BLAKE2S_SIMD128_OUT_BYTES (32U)
#define HACL_HASH_BLAKE2S_SIMD128_KEY_BYTES (32U)
#define HACL_HASH_BLAKE2S_SIMD128_SALT_BYTES (8U)
#define HACL_HASH_BLAKE2S_SIMD128_PERSONAL_BYTES (8U)
```

### 2.7 SHA-2 multi-buffer tuple types (`Hacl_SHA2_Types.h`)

```c
typedef struct Hacl_Hash_SHA2_uint8_2p_s
{
  uint8_t *fst;
  uint8_t *snd;
}
Hacl_Hash_SHA2_uint8_2p;

typedef struct Hacl_Hash_SHA2_uint8_3p_s
{
  uint8_t *fst;
  Hacl_Hash_SHA2_uint8_2p snd;
}
Hacl_Hash_SHA2_uint8_3p;

typedef struct Hacl_Hash_SHA2_uint8_4p_s
{
  uint8_t *fst;
  Hacl_Hash_SHA2_uint8_3p snd;
}
Hacl_Hash_SHA2_uint8_4p;

typedef uint8_t *Hacl_Hash_SHA2_bufx1;

typedef Hacl_Hash_SHA2_uint8_4p Hacl_Hash_SHA2_bufx4;
```

A `Hacl_Hash_SHA2_uint8_4p` contains four pointers: `fst`, `snd.fst`, `snd.snd.fst`, `snd.snd.snd`.

### 2.8 EverCrypt hash states

Public:

```c
typedef struct EverCrypt_Hash_state_s_s EverCrypt_Hash_state_s;
typedef struct EverCrypt_Hash_Incremental_state_t_s EverCrypt_Hash_Incremental_state_t;
```

Internal tags and layout (`internal/EverCrypt_Hash.h`), non-public but useful for understanding multiplexing:

```c
#define EverCrypt_Hash_MD5_s 0
#define EverCrypt_Hash_SHA1_s 1
#define EverCrypt_Hash_SHA2_224_s 2
#define EverCrypt_Hash_SHA2_256_s 3
#define EverCrypt_Hash_SHA2_384_s 4
#define EverCrypt_Hash_SHA2_512_s 5
#define EverCrypt_Hash_SHA3_224_s 6
#define EverCrypt_Hash_SHA3_256_s 7
#define EverCrypt_Hash_SHA3_384_s 8
#define EverCrypt_Hash_SHA3_512_s 9
#define EverCrypt_Hash_Blake2S_s 10
#define EverCrypt_Hash_Blake2S_128_s 11
#define EverCrypt_Hash_Blake2B_s 12
#define EverCrypt_Hash_Blake2B_256_s 13

typedef uint8_t EverCrypt_Hash_state_s_tags;

typedef struct EverCrypt_Hash_Incremental_state_t_s
{
  EverCrypt_Hash_state_s *block_state;
  uint8_t *buf;
  uint64_t total_len;
}
EverCrypt_Hash_Incremental_state_t;
```

EverCrypt multiplexes portable C for all fixed-length hashes and optimized implementations where configured. Documentation names SHAEXT/SHA-NI for SHA2-224/SHA2-256. Internal tags also include SIMD BLAKE2s-128 and BLAKE2b-256 states.

### 2.9 EverCrypt digest length macros

```c
#define MD5_HASH_LEN (16U)
#define SHA1_HASH_LEN (20U)
#define SHA2_224_HASH_LEN (28U)
#define SHA2_256_HASH_LEN (32U)
#define SHA2_384_HASH_LEN (48U)
#define SHA2_512_HASH_LEN (64U)
#define SHA3_224_HASH_LEN (28U)
#define SHA3_256_HASH_LEN (32U)
#define SHA3_384_HASH_LEN (48U)
#define SHA3_512_HASH_LEN (64U)
#define BLAKE2S_HASH_LEN (32U)
#define BLAKE2B_HASH_LEN (64U)
```

## 3. Size and limit summary

| Algorithm | Enum | Output bytes | Block/rate bytes | Word bytes | Max total input |
|---|---:|---:|---:|---:|---:|
| MD5 | 5 | 16 | 64 | 4 | 2^61 - 1 |
| SHA1 | 4 | 20 | 64 | 4 | 2^61 - 1 |
| SHA2-224 | 0 | 28 | 64 | 4 | 2^61 - 1 |
| SHA2-256 | 1 | 32 | 64 | 4 | 2^61 - 1 |
| SHA2-384 | 2 | 48 | 128 | 8 | 2^125 - 1 |
| SHA2-512 | 3 | 64 | 128 | 8 | 2^125 - 1 |
| BLAKE2s | 6 | 1..32, default 32 | 64 | 4 | 2^64 - 1 in the spec; C streaming tracks `uint64_t` |
| BLAKE2b | 7 | 1..64, default 64 | 128 | 8 | 2^128 - 1 in the spec; C streaming tracks `uint64_t` |
| SHA3-224 | 9 | 28 | 144 | 8 lanes | no F* max-input bound; C lengths are `uint32_t` per call |
| SHA3-256 | 8 | 32 | 136 | 8 lanes | same |
| SHA3-384 | 10 | 48 | 104 | 8 lanes | same |
| SHA3-512 | 11 | 64 | 72 | 8 lanes | same |
| SHAKE128 | 12 | caller-chosen | 168 | 8 lanes | same |
| SHAKE256 | 13 | caller-chosen | 136 | 8 lanes | same |

## 4. Complete inventory table

| Header | Functions |
|---|---|
| `Hacl_Hash_MD5.h` | `Hacl_Hash_MD5_malloc`, `reset`, `update`, `digest`, `free`, `copy`, `hash` |
| `Hacl_Hash_SHA1.h` | `Hacl_Hash_SHA1_malloc`, `reset`, `update`, `digest`, `free`, `copy`, `hash` |
| `Hacl_Hash_SHA2.h` | SHA2-224/256/384/512 streaming lifecycle and one-shot functions |
| `Hacl_Hash_SHA3.h` | agile SHA3/SHAKE streaming, one-shot SHA3/SHAKE, and SHAKE128 low-level state/absorb/squeeze helpers |
| `Hacl_Hash_SHA3_Simd256.h` | 4-way SHA3/SHAKE and 4-way SHAKE128 low-level helpers |
| `Hacl_Hash_Blake2b.h` | BLAKE2b streaming lifecycle, keyed allocation/reset, info, one-shot keyed/parameterized hashing |
| `Hacl_Hash_Blake2s.h` | BLAKE2s streaming lifecycle, keyed allocation/reset, info, one-shot keyed/parameterized hashing |
| `Hacl_Hash_Blake2b_Simd256.h` | SIMD256 BLAKE2b streaming and one-shot API |
| `Hacl_Hash_Blake2s_Simd128.h` | SIMD128 BLAKE2s streaming and one-shot API |
| `Hacl_SHA2_Vec128.h` | 4-way SHA2-224 and SHA2-256 one-shot |
| `Hacl_SHA2_Vec256.h` | 8-way SHA2-224/256 and 4-way SHA2-384/512 one-shot |
| `Hacl_Hash_Base.h` | hash size helper functions |
| `EverCrypt_Hash.h` | agile incremental hash API and agile one-shot hash |

## 5. Common streaming lifecycle contract

The streaming APIs generated by the common streaming functor follow this lifecycle:

1. **Allocate**: `*_malloc...` returns a heap object or `NULL`. The state has initial algorithm parameters and represents an empty input.
2. **Reset**: `*_reset...` reinitializes an allocated state to empty input. For BLAKE2, the reset flavor must match the original allocation choice and must not change `digest_length`, `key_length`, or `last_node`.
3. **Update**: `*_update(state, chunk, chunk_len)` absorbs `chunk_len` bytes from `chunk`. It returns `Hacl_Streaming_Types_Success` or `Hacl_Streaming_Types_MaximumLengthExceeded`. On success the state total length increases; on error the state should be treated as unchanged for reimplementation purposes.
4. **Digest**: `*_digest(state, output)` writes the current digest but **does not consume or invalidate** the state. More updates may follow.
5. **Copy**: `*_copy(state)` deep-copies a state and preserves parameters; it returns a newly allocated state or `NULL`.
6. **Free**: `*_free(state)` releases the state and its internal buffers. Do not use the pointer afterwards.

Streaming maximum total input: MD5/SHA1/SHA2-224/SHA2-256 enforce 2^61-1 bytes; SHA2-384/SHA2-512 enforce 2^125-1 bytes at the specification level, although the public C state stores a 64-bit total; BLAKE2 tracks total input and exposes maximum-length errors, with BLAKE2s bounded by 2^64-1 in the spec and BLAKE2b by 2^128-1 in the spec. SHA3/SHAKE streaming uses a 64-bit total and `update` returns `MaximumLengthExceeded` on `uint64_t` overflow; the public spec does not impose the Merkle-Damgard length-encoding bounds.

## 6. Generic helper functions (`Hacl_Hash_Base.h`)

### `Hacl_Hash_Definitions_word_len`

```c
uint32_t Hacl_Hash_Definitions_word_len(Spec_Hash_Definitions_hash_alg a);
```

Returns internal word size in bytes for MD5/SHA1/SHA2 only: 4 for MD5, SHA1, SHA2-224, SHA2-256; 8 for SHA2-384, SHA2-512. Other algorithms fall into the generated incomplete-match failure path in the C implementation.

### `Hacl_Hash_Definitions_block_len`

```c
uint32_t Hacl_Hash_Definitions_block_len(Spec_Hash_Definitions_hash_alg a);
```

Returns block/rate bytes: MD5/SHA1/SHA2-224/SHA2-256/BLAKE2s = 64; SHA2-384/SHA2-512/BLAKE2b = 128; SHA3-224 = 144; SHA3-256/SHAKE256 = 136; SHA3-384 = 104; SHA3-512 = 72; SHAKE128 = 168. Invalid algorithms abort via incomplete match.

### `Hacl_Hash_Definitions_hash_word_len`

```c
uint32_t Hacl_Hash_Definitions_hash_word_len(Spec_Hash_Definitions_hash_alg a);
```

Returns digest length in words for MD5/SHA1/SHA2 only: MD5 4, SHA1 5, SHA2-224 7, SHA2-256 8, SHA2-384 6, SHA2-512 8. Other algorithms are not supported by this helper.

### `Hacl_Hash_Definitions_hash_len`

```c
uint32_t Hacl_Hash_Definitions_hash_len(Spec_Hash_Definitions_hash_alg a);
```

Returns fixed digest bytes for MD5, SHA1, SHA2, SHA3, and BLAKE2 defaults. It has no case for SHAKE because SHAKE output length is caller-chosen.

## 7. MD5 public functions (`Hacl_Hash_MD5.h`)

MD5 digest is 16 bytes; block size is 64 bytes; maximum input length is 2^61-1. MD5 is present for compatibility only.

### `Hacl_Hash_MD5_malloc`

```c
Hacl_Streaming_MD_state_32 *Hacl_Hash_MD5_malloc(void);
```

Allocates an MD5 streaming state. Returns a live state or `NULL`. Free with `Hacl_Hash_MD5_free`.

### `Hacl_Hash_MD5_reset`

```c
void Hacl_Hash_MD5_reset(Hacl_Streaming_MD_state_32 *state);
```

Resets `state` to empty MD5 input. `state` must be live and allocated by the MD5 API.

### `Hacl_Hash_MD5_update`

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_MD5_update(Hacl_Streaming_MD_state_32 *state, uint8_t *chunk, uint32_t chunk_len);
```

Absorbs `chunk_len` bytes from `chunk`. `chunk` points to `chunk_len` bytes and must not alias the state. Returns success or maximum-length-exceeded if total input since reset would exceed 2^61-1 bytes.

### `Hacl_Hash_MD5_digest`

```c
void Hacl_Hash_MD5_digest(Hacl_Streaming_MD_state_32 *state, uint8_t *output);
```

Writes 16 digest bytes to `output`. Does not consume `state`; output must not alias state internals.

### `Hacl_Hash_MD5_free`

```c
void Hacl_Hash_MD5_free(Hacl_Streaming_MD_state_32 *state);
```

Frees an MD5 state previously allocated by `Hacl_Hash_MD5_malloc` or `copy`.

### `Hacl_Hash_MD5_copy`

```c
Hacl_Streaming_MD_state_32 *Hacl_Hash_MD5_copy(Hacl_Streaming_MD_state_32 *state);
```

Deep-copies a live MD5 state. Returns a newly allocated state or `NULL`; caller owns it.

### `Hacl_Hash_MD5_hash`

```c
void Hacl_Hash_MD5_hash(uint8_t *output, uint8_t *input, uint32_t input_len);
```

One-shot MD5. `input` is `input_len` bytes; `output` is 16 bytes. Input and output must be disjoint. `input_len` is a 32-bit length and is below the 2^61-1 MD5 bound.

## 8. SHA-1 public functions (`Hacl_Hash_SHA1.h`)

SHA-1 digest is 20 bytes; block size is 64 bytes; maximum input length is 2^61-1. SHA-1 is present for compatibility only.

### `Hacl_Hash_SHA1_malloc`

```c
Hacl_Streaming_MD_state_32 *Hacl_Hash_SHA1_malloc(void);
```

Allocates a SHA-1 streaming state or returns `NULL`.

### `Hacl_Hash_SHA1_reset`

```c
void Hacl_Hash_SHA1_reset(Hacl_Streaming_MD_state_32 *state);
```

Resets a live SHA-1 state to empty input.

### `Hacl_Hash_SHA1_update`

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_SHA1_update(Hacl_Streaming_MD_state_32 *state, uint8_t *chunk, uint32_t chunk_len);
```

Absorbs `chunk_len` bytes from `chunk`; returns success or maximum-length-exceeded at 2^61-1 total bytes.

### `Hacl_Hash_SHA1_digest`

```c
void Hacl_Hash_SHA1_digest(Hacl_Streaming_MD_state_32 *state, uint8_t *output);
```

Writes 20 bytes to `output`. The state remains usable.

### `Hacl_Hash_SHA1_free`

```c
void Hacl_Hash_SHA1_free(Hacl_Streaming_MD_state_32 *state);
```

Frees a SHA-1 state.

### `Hacl_Hash_SHA1_copy`

```c
Hacl_Streaming_MD_state_32 *Hacl_Hash_SHA1_copy(Hacl_Streaming_MD_state_32 *state);
```

Deep-copies a SHA-1 state; returns `NULL` on allocation failure.

### `Hacl_Hash_SHA1_hash`

```c
void Hacl_Hash_SHA1_hash(uint8_t *output, uint8_t *input, uint32_t input_len);
```

One-shot SHA-1. `input` is `input_len` bytes; `output` is 20 bytes; buffers are disjoint.

## 9. SHA-2 public functions (`Hacl_Hash_SHA2.h`)

SHA2-224 and SHA2-256 use `Hacl_Streaming_MD_state_32` and 64-byte blocks, with maximum total input 2^61-1. SHA2-384 and SHA2-512 use `Hacl_Streaming_MD_state_64` and 128-byte blocks, with specification maximum 2^125-1.

### SHA2-256

```c
Hacl_Streaming_MD_state_32 *Hacl_Hash_SHA2_malloc_256(void);
```

Allocates an empty SHA2-256 state; returns `NULL` on allocation failure.

```c
Hacl_Streaming_MD_state_32 *Hacl_Hash_SHA2_copy_256(Hacl_Streaming_MD_state_32 *state);
```

Deep-copies a SHA2-256 state; new state must be freed with `Hacl_Hash_SHA2_free_256`.

```c
void Hacl_Hash_SHA2_reset_256(Hacl_Streaming_MD_state_32 *state);
```

Resets to empty SHA2-256 input.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_SHA2_update_256(
  Hacl_Streaming_MD_state_32 *state,
  uint8_t *input,
  uint32_t input_len
);
```

Absorbs `input_len` bytes. Returns success or maximum-length-exceeded if total would exceed 2^61-1.

```c
void Hacl_Hash_SHA2_digest_256(Hacl_Streaming_MD_state_32 *state, uint8_t *output);
```

Writes 32 digest bytes; state remains valid.

```c
void Hacl_Hash_SHA2_free_256(Hacl_Streaming_MD_state_32 *state);
```

Frees a SHA2-256/224-compatible 32-bit streaming state.

```c
void Hacl_Hash_SHA2_hash_256(uint8_t *output, uint8_t *input, uint32_t input_len);
```

One-shot SHA2-256. `output` is 32 bytes; `input` is `input_len` bytes; buffers are disjoint.

### SHA2-224

```c
Hacl_Streaming_MD_state_32 *Hacl_Hash_SHA2_malloc_224(void);
```

Allocates an empty SHA2-224 state.

```c
void Hacl_Hash_SHA2_reset_224(Hacl_Streaming_MD_state_32 *state);
```

Resets to empty SHA2-224 input.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_SHA2_update_224(
  Hacl_Streaming_MD_state_32 *state,
  uint8_t *input,
  uint32_t input_len
);
```

Absorbs `input_len` bytes; returns maximum-length-exceeded past 2^61-1 total bytes.

```c
void Hacl_Hash_SHA2_digest_224(Hacl_Streaming_MD_state_32 *state, uint8_t *output);
```

Writes 28 digest bytes; state remains valid.

```c
void Hacl_Hash_SHA2_free_224(Hacl_Streaming_MD_state_32 *state);
```

Frees a SHA2-224 state.

```c
void Hacl_Hash_SHA2_hash_224(uint8_t *output, uint8_t *input, uint32_t input_len);
```

One-shot SHA2-224. `output` is 28 bytes; `input` is `input_len` bytes; buffers are disjoint.

There is no public `Hacl_Hash_SHA2_copy_224` in this header.

### SHA2-512

```c
Hacl_Streaming_MD_state_64 *Hacl_Hash_SHA2_malloc_512(void);
```

Allocates an empty SHA2-512 state.

```c
Hacl_Streaming_MD_state_64 *Hacl_Hash_SHA2_copy_512(Hacl_Streaming_MD_state_64 *state);
```

Deep-copies a SHA2-512 state.

```c
void Hacl_Hash_SHA2_reset_512(Hacl_Streaming_MD_state_64 *state);
```

Resets to empty SHA2-512 input.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_SHA2_update_512(
  Hacl_Streaming_MD_state_64 *state,
  uint8_t *input,
  uint32_t input_len
);
```

Absorbs `input_len` bytes. Returns maximum-length-exceeded if total would exceed 2^125-1.

```c
void Hacl_Hash_SHA2_digest_512(Hacl_Streaming_MD_state_64 *state, uint8_t *output);
```

Writes 64 digest bytes; state remains valid.

```c
void Hacl_Hash_SHA2_free_512(Hacl_Streaming_MD_state_64 *state);
```

Frees a SHA2-512/384-compatible 64-bit streaming state.

```c
void Hacl_Hash_SHA2_hash_512(uint8_t *output, uint8_t *input, uint32_t input_len);
```

One-shot SHA2-512. `output` is 64 bytes; `input` is `input_len` bytes; buffers are disjoint.

### SHA2-384

```c
Hacl_Streaming_MD_state_64 *Hacl_Hash_SHA2_malloc_384(void);
```

Allocates an empty SHA2-384 state.

```c
void Hacl_Hash_SHA2_reset_384(Hacl_Streaming_MD_state_64 *state);
```

Resets to empty SHA2-384 input.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_SHA2_update_384(
  Hacl_Streaming_MD_state_64 *state,
  uint8_t *input,
  uint32_t input_len
);
```

Absorbs `input_len` bytes. Returns maximum-length-exceeded past 2^125-1 total bytes.

```c
void Hacl_Hash_SHA2_digest_384(Hacl_Streaming_MD_state_64 *state, uint8_t *output);
```

Writes 48 digest bytes; state remains valid.

```c
void Hacl_Hash_SHA2_free_384(Hacl_Streaming_MD_state_64 *state);
```

Frees a SHA2-384 state.

```c
void Hacl_Hash_SHA2_hash_384(uint8_t *output, uint8_t *input, uint32_t input_len);
```

One-shot SHA2-384. `output` is 48 bytes; `input` is `input_len` bytes; buffers are disjoint.

There is no public `Hacl_Hash_SHA2_copy_384` in this header.

### Non-public SHA-2 core functions

`dist/gcc-compatible/internal/Hacl_Hash_SHA2.h` contains `sha*_init`, `sha*_update_nblocks`, `sha*_update_last`, and `sha*_finish`. These are internal headers, not part of the public header set in this document. Reimplementers may model them as compression-core operations, but bindings should not expose them as public HACL API.

## 10. SHA-3 and SHAKE public functions (`Hacl_Hash_SHA3.h`)

Fixed SHA3 digest sizes: SHA3-224 28 bytes, SHA3-256 32, SHA3-384 48, SHA3-512 64. Rates: 144, 136, 104, 72 bytes. SHAKE output length is caller-chosen; rates are SHAKE128 168 and SHAKE256 136 bytes.

### Agile SHA3/SHAKE streaming helpers

```c
Spec_Hash_Definitions_hash_alg Hacl_Hash_SHA3_get_alg(Hacl_Hash_SHA3_state_t *s);
```

Returns the algorithm embedded in `s`. `s` is a live SHA3 state.

```c
Hacl_Hash_SHA3_state_t *Hacl_Hash_SHA3_malloc(Spec_Hash_Definitions_hash_alg a);
```

Allocates a SHA3/SHAKE state for `a`. Valid algorithms are SHA3-224/256/384/512 and Shake128/Shake256. Returns `NULL` for allocation failure (and reimplementations should return `NULL` or an invalid-algorithm error path for invalid `a`).

```c
void Hacl_Hash_SHA3_free(Hacl_Hash_SHA3_state_t *state);
```

Frees a SHA3/SHAKE streaming state.

```c
Hacl_Hash_SHA3_state_t *Hacl_Hash_SHA3_copy(Hacl_Hash_SHA3_state_t *state);
```

Deep-copies the current state and algorithm; returns `NULL` on allocation failure.

```c
void Hacl_Hash_SHA3_reset(Hacl_Hash_SHA3_state_t *state);
```

Resets to the empty input for the state's embedded algorithm.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_SHA3_update(Hacl_Hash_SHA3_state_t *state, uint8_t *chunk, uint32_t chunk_len);
```

Absorbs `chunk_len` bytes from `chunk`. `chunk` points to `chunk_len` bytes and is disjoint from the state. Return is a streaming error code; SHA3/SHAKE normally has no Merkle-Damgard maximum-length error in the spec.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_SHA3_digest(Hacl_Hash_SHA3_state_t *state, uint8_t *output);
```

For fixed SHA3 states, writes `Hacl_Hash_SHA3_hash_len(state)` bytes to `output` and does not consume state. For SHAKE states, use `squeeze` to choose an output length; reimplementations should return `InvalidAlgorithm` if `digest` is called where no fixed digest length exists.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_SHA3_squeeze(Hacl_Hash_SHA3_state_t *s, uint8_t *dst, uint32_t l);
```

For SHAKE states, writes `l` output bytes to `dst`. `l` must be nonzero; the C implementation returns `Hacl_Streaming_Types_InvalidLength` for `l == 0`. The state represents absorbed input and is not consumed because the implementation finalizes a copy. For fixed SHA3 states, it returns `InvalidAlgorithm`.

```c
uint32_t Hacl_Hash_SHA3_block_len(Hacl_Hash_SHA3_state_t *s);
```

Returns the rate in bytes for the state's algorithm: 144/136/104/72/168/136.

```c
uint32_t Hacl_Hash_SHA3_hash_len(Hacl_Hash_SHA3_state_t *s);
```

Returns fixed digest length for SHA3 states (28/32/48/64). Do not call on SHAKE states: the generated C helper has no SHAKE case and aborts through the incomplete-match path. Use `squeeze` with an explicit `l` instead.

```c
bool Hacl_Hash_SHA3_is_shake(Hacl_Hash_SHA3_state_t *s);
```

Returns true for Shake128 and Shake256 states.

### SHA3/SHAKE one-shot functions

```c
void
Hacl_Hash_SHA3_shake128(
  uint8_t *output,
  uint32_t outputByteLen,
  uint8_t *input,
  uint32_t inputByteLen
);
```

One-shot SHAKE128. `input` is `inputByteLen` bytes; `output` is `outputByteLen` bytes. Input and output are disjoint.

```c
void
Hacl_Hash_SHA3_shake256(
  uint8_t *output,
  uint32_t outputByteLen,
  uint8_t *input,
  uint32_t inputByteLen
);
```

One-shot SHAKE256. `input` is `inputByteLen` bytes; `output` is `outputByteLen` bytes.

```c
void Hacl_Hash_SHA3_sha3_224(uint8_t *output, uint8_t *input, uint32_t inputByteLen);
```

One-shot SHA3-224. `output` is 28 bytes; `input` is `inputByteLen` bytes; buffers are disjoint.

```c
void Hacl_Hash_SHA3_sha3_256(uint8_t *output, uint8_t *input, uint32_t inputByteLen);
```

One-shot SHA3-256. `output` is 32 bytes.

```c
void Hacl_Hash_SHA3_sha3_384(uint8_t *output, uint8_t *input, uint32_t inputByteLen);
```

One-shot SHA3-384. `output` is 48 bytes.

```c
void Hacl_Hash_SHA3_sha3_512(uint8_t *output, uint8_t *input, uint32_t inputByteLen);
```

One-shot SHA3-512. `output` is 64 bytes.

### SHA3/SHAKE low-level public functions

```c
void Hacl_Hash_SHA3_absorb_inner_32(uint32_t rateInBytes, uint8_t *b, uint64_t *s);
```

Absorbs one block at `rateInBytes` into a Keccak state. `s` points to `uint64_t[25]` (200 bytes). `b` points to at least `rateInBytes` bytes. Intended for low-level use; caller must choose a valid Keccak rate.

```c
uint64_t *Hacl_Hash_SHA3_state_malloc(void);
```

Allocates a raw 200-byte Keccak state buffer (`uint64_t[25]`) or returns `NULL`.

```c
void Hacl_Hash_SHA3_state_free(uint64_t *s);
```

Frees a raw state allocated by `Hacl_Hash_SHA3_state_malloc`.

```c
void
Hacl_Hash_SHA3_shake128_absorb_nblocks(uint64_t *state, uint8_t *input, uint32_t inputByteLen);
```

`state` is `uint64_t[25]`. `input` is `inputByteLen` bytes. Processes the full 168-byte SHAKE128 blocks at the start of `input`; ignores any final partial block.

```c
void
Hacl_Hash_SHA3_shake128_absorb_final(uint64_t *state, uint8_t *input, uint32_t inputByteLen);
```

`state` is `uint64_t[25]`. `input` is `inputByteLen` bytes. Processes only the final partial SHAKE128 block (less than 168 bytes); full-block bytes at the start are ignored. Pass the full input length including ignored full blocks.

```c
void
Hacl_Hash_SHA3_shake128_squeeze_nblocks(
  uint64_t *state,
  uint8_t *output,
  uint32_t outputByteLen
);
```

`state` is `uint64_t[25]`. `output` is `outputByteLen` bytes. Produces complete 168-byte SHAKE128 output blocks; ignores any final partial output request.

## 11. SHA-3 SIMD256 4-way functions (`Hacl_Hash_SHA3_Simd256.h`)

All functions process four independent equal-length messages in parallel. Each `inputN` points to `inputByteLen` bytes; each `outputN` points to the fixed digest length or `outputByteLen` bytes. All lanes use the same lengths. SIMD state is `Lib_IntVector_Intrinsics_vec256[25]`, representing four Keccak states.

```c
void
Hacl_Hash_SHA3_Simd256_absorb_inner_256(
  uint32_t rateInBytes,
  Hacl_Hash_SHA2_uint8_4p b,
  Lib_IntVector_Intrinsics_vec256 *s
);
```

Absorbs one `rateInBytes` block from each of four pointers packed in `b` into the 4-way state `s`. `s` has 25 vector lanes.

```c
void
Hacl_Hash_SHA3_Simd256_shake128(
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3,
  uint32_t outputByteLen,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t inputByteLen
);
```

4-way one-shot SHAKE128. Each output is `outputByteLen` bytes; each input is `inputByteLen` bytes.

```c
void
Hacl_Hash_SHA3_Simd256_shake256(
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3,
  uint32_t outputByteLen,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t inputByteLen
);
```

4-way one-shot SHAKE256.

```c
void
Hacl_Hash_SHA3_Simd256_sha3_224(
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t inputByteLen
);
```

4-way SHA3-224; each output is 28 bytes.

```c
void
Hacl_Hash_SHA3_Simd256_sha3_256(
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t inputByteLen
);
```

4-way SHA3-256; each output is 32 bytes.

```c
void
Hacl_Hash_SHA3_Simd256_sha3_384(
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t inputByteLen
);
```

4-way SHA3-384; each output is 48 bytes.

```c
void
Hacl_Hash_SHA3_Simd256_sha3_512(
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t inputByteLen
);
```

4-way SHA3-512; each output is 64 bytes.

```c
Lib_IntVector_Intrinsics_vec256 *Hacl_Hash_SHA3_Simd256_state_malloc(void);
```

Allocates a 4-way 200-byte-per-lane state (`vec256[25]`) or returns `NULL`.

```c
void Hacl_Hash_SHA3_Simd256_state_free(Lib_IntVector_Intrinsics_vec256 *s);
```

Frees a 4-way raw state.

```c
void
Hacl_Hash_SHA3_Simd256_shake128_absorb_nblocks(
  Lib_IntVector_Intrinsics_vec256 *state,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t inputByteLen
);
```

Absorbs complete 168-byte SHAKE128 blocks from each input lane; ignores each final partial block.

```c
void
Hacl_Hash_SHA3_Simd256_shake128_absorb_final(
  Lib_IntVector_Intrinsics_vec256 *state,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint32_t inputByteLen
);
```

Absorbs the final partial SHAKE128 block for each lane; full blocks at the start are ignored.

```c
void
Hacl_Hash_SHA3_Simd256_shake128_squeeze_nblocks(
  Lib_IntVector_Intrinsics_vec256 *state,
  uint8_t *output0,
  uint8_t *output1,
  uint8_t *output2,
  uint8_t *output3,
  uint32_t outputByteLen
);
```

Squeezes complete 168-byte output blocks for each lane; ignores final partial output.

## 12. BLAKE2 public functions

The four BLAKE2 headers have the same shape. The portable BLAKE2b and SIMD256 BLAKE2b use BLAKE2b sizes (block 128, key max 64, digest 1..64). Portable BLAKE2s and SIMD128 BLAKE2s use BLAKE2s sizes (block 64, key max 32, digest 1..32). `params.salt`/`personal` are 16 bytes for BLAKE2b and 8 bytes for BLAKE2s. `digest` returns the configured digest length and does not consume the state.

### BLAKE2b (`Hacl_Hash_Blake2b.h`)

```c
Hacl_Hash_Blake2b_state_t
*Hacl_Hash_Blake2b_malloc_with_params_and_key(
  Hacl_Hash_Blake2b_blake2_params *p,
  bool last_node,
  uint8_t *k
);
```

Allocates a BLAKE2b state with explicit params and key. `p` is live; `k` points to `p->key_length` bytes. `p->key_length <= 64`; `1 <= p->digest_length <= 64`; `p->salt` and `p->personal` are 16 bytes. The returned state locks in `digest_length`, `key_length`, and `last_node`.

```c
Hacl_Hash_Blake2b_state_t *Hacl_Hash_Blake2b_malloc_with_key(uint8_t *k, uint8_t kk);
```

Allocates default-parameter BLAKE2b with key length `kk`. `k` is `kk` bytes; `kk <= 64`; digest length is default 64.

```c
Hacl_Hash_Blake2b_state_t *Hacl_Hash_Blake2b_malloc(void);
```

Allocates default unkeyed BLAKE2b with 64-byte digest.

```c
void
Hacl_Hash_Blake2b_reset_with_key_and_params(
  Hacl_Hash_Blake2b_state_t *s,
  Hacl_Hash_Blake2b_blake2_params *p,
  uint8_t *k
);
```

Resets with parameters and key. `p->digest_length`, `p->key_length`, and `last_node` must match allocation-time values. `k` is `p->key_length` bytes.

```c
void Hacl_Hash_Blake2b_reset_with_key(Hacl_Hash_Blake2b_state_t *s, uint8_t *k);
```

Resets using default parameters and the allocation-time key length. `k` points to that many bytes; digest length must be default 64.

```c
void Hacl_Hash_Blake2b_reset(Hacl_Hash_Blake2b_state_t *s);
```

Resets default unkeyed BLAKE2b; valid when key length 0 and digest length 64.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_Blake2b_update(Hacl_Hash_Blake2b_state_t *state, uint8_t *chunk, uint32_t chunk_len);
```

Absorbs `chunk_len` bytes. Returns success or maximum-length-exceeded. `chunk` is disjoint from state.

```c
uint8_t Hacl_Hash_Blake2b_digest(Hacl_Hash_Blake2b_state_t *s, uint8_t *dst);
```

Writes the configured digest length to `dst` and returns that length. `dst` is at least the returned/configured length (up to 64).

```c
Hacl_Hash_Blake2b_index Hacl_Hash_Blake2b_info(Hacl_Hash_Blake2b_state_t *s);
```

Returns current immutable index: `key_length`, `digest_length`, `last_node`.

```c
void Hacl_Hash_Blake2b_free(Hacl_Hash_Blake2b_state_t *state);
```

Frees a BLAKE2b state.

```c
Hacl_Hash_Blake2b_state_t *Hacl_Hash_Blake2b_copy(Hacl_Hash_Blake2b_state_t *state);
```

Deep-copies a BLAKE2b state, preserving parameters; returns `NULL` on allocation failure.

```c
void
Hacl_Hash_Blake2b_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
);
```

One-shot keyed/unkeyed BLAKE2b. `output` is `output_len` bytes with `1 <= output_len <= 64`; `input` is `input_len` bytes; `key` is `key_len` bytes and `key_len <= 64` (0 allowed). Buffers are disjoint as outputs vs inputs/key.

```c
void
Hacl_Hash_Blake2b_hash_with_key_and_params(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  Hacl_Hash_Blake2b_blake2_params params,
  uint8_t *key
);
```

One-shot BLAKE2b with full parameters. `output` is `params.digest_length` bytes; `input` is `input_len` bytes; `key` is `params.key_length` bytes; salt/personal are 16 bytes.

### BLAKE2s (`Hacl_Hash_Blake2s.h`)

```c
Hacl_Hash_Blake2s_state_t
*Hacl_Hash_Blake2s_malloc_with_params_and_key(
  Hacl_Hash_Blake2b_blake2_params *p,
  bool last_node,
  uint8_t *k
);
```

Allocates BLAKE2s with explicit params. `k` is `p->key_length` bytes; `p->key_length <= 32`; `1 <= p->digest_length <= 32`; salt/personal are 8 bytes.

```c
Hacl_Hash_Blake2s_state_t *Hacl_Hash_Blake2s_malloc_with_key(uint8_t *k, uint8_t kk);
```

Allocates default BLAKE2s with key `k[kk]`; `kk <= 32`; default digest 32.

```c
Hacl_Hash_Blake2s_state_t *Hacl_Hash_Blake2s_malloc(void);
```

Allocates default unkeyed BLAKE2s.

```c
void
Hacl_Hash_Blake2s_reset_with_key_and_params(
  Hacl_Hash_Blake2s_state_t *s,
  Hacl_Hash_Blake2b_blake2_params *p,
  uint8_t *k
);
```

Resets BLAKE2s; immutable allocation-time digest/key length and `last_node` must match.

```c
void Hacl_Hash_Blake2s_reset_with_key(Hacl_Hash_Blake2s_state_t *s, uint8_t *k);
```

Resets default-parameter keyed BLAKE2s with same key length.

```c
void Hacl_Hash_Blake2s_reset(Hacl_Hash_Blake2s_state_t *s);
```

Resets default unkeyed BLAKE2s.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_Blake2s_update(Hacl_Hash_Blake2s_state_t *state, uint8_t *chunk, uint32_t chunk_len);
```

Absorbs `chunk_len` bytes; returns streaming error code.

```c
uint8_t Hacl_Hash_Blake2s_digest(Hacl_Hash_Blake2s_state_t *s, uint8_t *dst);
```

Writes and returns configured digest length (up to 32).

```c
Hacl_Hash_Blake2b_index Hacl_Hash_Blake2s_info(Hacl_Hash_Blake2s_state_t *s);
```

Returns key length, digest length, and last-node flag.

```c
void Hacl_Hash_Blake2s_free(Hacl_Hash_Blake2s_state_t *state);
```

Frees a BLAKE2s state.

```c
Hacl_Hash_Blake2s_state_t *Hacl_Hash_Blake2s_copy(Hacl_Hash_Blake2s_state_t *state);
```

Deep-copies BLAKE2s state.

```c
void
Hacl_Hash_Blake2s_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
);
```

One-shot BLAKE2s. `output` is `output_len` bytes, with `1 <= output_len <= 32` by the BLAKE2s spec and constants (`HACL_HASH_BLAKE2S_OUT_BYTES`). The generated comment says `<= 64`, which appears copied from BLAKE2b. `key_len <= 32`; `input` is `input_len` bytes.

```c
void
Hacl_Hash_Blake2s_hash_with_key_and_params(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  Hacl_Hash_Blake2b_blake2_params params,
  uint8_t *key
);
```

One-shot BLAKE2s with params. `output` is `params.digest_length` bytes (1..32); `key` is `params.key_length` bytes (0..32); salt/personal are 8 bytes.

### BLAKE2b SIMD256 (`Hacl_Hash_Blake2b_Simd256.h`)

The prototypes and contracts mirror portable BLAKE2b, but the state layout uses 256-bit SIMD vectors and the code must only run on CPUs supported by the compiled object.

```c
Hacl_Hash_Blake2b_Simd256_state_t
*Hacl_Hash_Blake2b_Simd256_malloc_with_params_and_key(
  Hacl_Hash_Blake2b_blake2_params *p,
  bool last_node,
  uint8_t *k
);
```

Explicit-parameter SIMD BLAKE2b allocation; key `p->key_length` bytes, digest 1..64, salt/personal 16 bytes.

```c
Hacl_Hash_Blake2b_Simd256_state_t
*Hacl_Hash_Blake2b_Simd256_malloc_with_key(uint8_t *k, uint8_t kk);
```

Default-parameter keyed SIMD BLAKE2b; `kk <= 64`.

```c
Hacl_Hash_Blake2b_Simd256_state_t *Hacl_Hash_Blake2b_Simd256_malloc(void);
```

Default unkeyed SIMD BLAKE2b.

```c
void
Hacl_Hash_Blake2b_Simd256_reset_with_key_and_params(
  Hacl_Hash_Blake2b_Simd256_state_t *s,
  Hacl_Hash_Blake2b_blake2_params *p,
  uint8_t *k
);
```

Reset with matching immutable key/digest/last-node values.

```c
void
Hacl_Hash_Blake2b_Simd256_reset_with_key(Hacl_Hash_Blake2b_Simd256_state_t *s, uint8_t *k);
```

Reset default-parameter keyed state with same key length.

```c
void Hacl_Hash_Blake2b_Simd256_reset(Hacl_Hash_Blake2b_Simd256_state_t *s);
```

Reset default unkeyed state.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_Blake2b_Simd256_update(
  Hacl_Hash_Blake2b_Simd256_state_t *state,
  uint8_t *chunk,
  uint32_t chunk_len
);
```

Absorbs `chunk_len` bytes; returns streaming error code.

```c
uint8_t Hacl_Hash_Blake2b_Simd256_digest(Hacl_Hash_Blake2b_Simd256_state_t *s, uint8_t *dst);
```

Writes/returns digest length, up to 64 bytes.

```c
Hacl_Hash_Blake2b_index Hacl_Hash_Blake2b_Simd256_info(Hacl_Hash_Blake2b_Simd256_state_t *s);
```

Returns immutable key/digest/last-node info.

```c
void Hacl_Hash_Blake2b_Simd256_free(Hacl_Hash_Blake2b_Simd256_state_t *state);
```

Frees SIMD BLAKE2b state.

```c
Hacl_Hash_Blake2b_Simd256_state_t
*Hacl_Hash_Blake2b_Simd256_copy(Hacl_Hash_Blake2b_Simd256_state_t *state);
```

Deep-copies SIMD BLAKE2b state.

```c
void
Hacl_Hash_Blake2b_Simd256_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
);
```

One-shot SIMD BLAKE2b; output 1..64 bytes; key 0..64 bytes.

```c
void
Hacl_Hash_Blake2b_Simd256_hash_with_key_and_params(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  Hacl_Hash_Blake2b_blake2_params params,
  uint8_t *key
);
```

One-shot SIMD BLAKE2b with params.

### BLAKE2s SIMD128 (`Hacl_Hash_Blake2s_Simd128.h`)

The prototypes and contracts mirror portable BLAKE2s, but use 128-bit SIMD state.

```c
Hacl_Hash_Blake2s_Simd128_state_t
*Hacl_Hash_Blake2s_Simd128_malloc_with_params_and_key(
  Hacl_Hash_Blake2b_blake2_params *p,
  bool last_node,
  uint8_t *k
);
```

Explicit-parameter SIMD BLAKE2s allocation. Key `p->key_length` bytes, digest 1..32, salt/personal 8 bytes. The generated comment mentions 128 for S, which is an artifact of SIMD vector width, not BLAKE2s digest/key limits.

```c
Hacl_Hash_Blake2s_Simd128_state_t
*Hacl_Hash_Blake2s_Simd128_malloc_with_key(uint8_t *k, uint8_t kk);
```

Default-parameter keyed SIMD BLAKE2s; `kk <= 32`.

```c
Hacl_Hash_Blake2s_Simd128_state_t *Hacl_Hash_Blake2s_Simd128_malloc(void);
```

Default unkeyed SIMD BLAKE2s.

```c
void
Hacl_Hash_Blake2s_Simd128_reset_with_key_and_params(
  Hacl_Hash_Blake2s_Simd128_state_t *s,
  Hacl_Hash_Blake2b_blake2_params *p,
  uint8_t *k
);
```

Reset with matching immutable key/digest/last-node values.

```c
void
Hacl_Hash_Blake2s_Simd128_reset_with_key(Hacl_Hash_Blake2s_Simd128_state_t *s, uint8_t *k);
```

Reset default-parameter keyed state.

```c
void Hacl_Hash_Blake2s_Simd128_reset(Hacl_Hash_Blake2s_Simd128_state_t *s);
```

Reset default unkeyed state.

```c
Hacl_Streaming_Types_error_code
Hacl_Hash_Blake2s_Simd128_update(
  Hacl_Hash_Blake2s_Simd128_state_t *state,
  uint8_t *chunk,
  uint32_t chunk_len
);
```

Absorbs bytes; returns streaming error code.

```c
uint8_t Hacl_Hash_Blake2s_Simd128_digest(Hacl_Hash_Blake2s_Simd128_state_t *s, uint8_t *dst);
```

Writes/returns digest length, up to 32 bytes.

```c
Hacl_Hash_Blake2b_index Hacl_Hash_Blake2s_Simd128_info(Hacl_Hash_Blake2s_Simd128_state_t *s);
```

Returns immutable key/digest/last-node info.

```c
void Hacl_Hash_Blake2s_Simd128_free(Hacl_Hash_Blake2s_Simd128_state_t *state);
```

Frees SIMD BLAKE2s state.

```c
Hacl_Hash_Blake2s_Simd128_state_t
*Hacl_Hash_Blake2s_Simd128_copy(Hacl_Hash_Blake2s_Simd128_state_t *state);
```

Deep-copies SIMD BLAKE2s state.

```c
void
Hacl_Hash_Blake2s_Simd128_hash_with_key(
  uint8_t *output,
  uint32_t output_len,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *key,
  uint32_t key_len
);
```

One-shot SIMD BLAKE2s. `output_len` 1..32 by BLAKE2s; `key_len` 0..32.

```c
void
Hacl_Hash_Blake2s_Simd128_hash_with_key_and_params(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  Hacl_Hash_Blake2b_blake2_params params,
  uint8_t *key
);
```

One-shot SIMD BLAKE2s with params.

## 13. SHA-2 multi-buffer APIs

These are one-shot SIMD-parallel APIs. All lanes use the same `input_len`. Each input pointer points to `input_len` bytes. Each output pointer points to the per-lane digest length. Outputs should be disjoint from inputs and from each other unless your reimplementation explicitly supports aliasing.

### `Hacl_SHA2_Vec128.h`

```c
void
Hacl_SHA2_Vec128_sha224_4(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3
);
```

Four-way SHA2-224. `dst0..dst3` are 28 bytes each; `input0..input3` are `input_len` bytes each; `input_len < 2^61`.

```c
void
Hacl_SHA2_Vec128_sha256_4(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3
);
```

Four-way SHA2-256. Outputs are 32 bytes each; inputs are `input_len` bytes each.

### `Hacl_SHA2_Vec256.h`

```c
void
Hacl_SHA2_Vec256_sha224_8(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint8_t *dst4,
  uint8_t *dst5,
  uint8_t *dst6,
  uint8_t *dst7,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *input4,
  uint8_t *input5,
  uint8_t *input6,
  uint8_t *input7
);
```

Eight-way SHA2-224. Outputs are 28 bytes each; inputs are `input_len` bytes each.

```c
void
Hacl_SHA2_Vec256_sha256_8(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint8_t *dst4,
  uint8_t *dst5,
  uint8_t *dst6,
  uint8_t *dst7,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3,
  uint8_t *input4,
  uint8_t *input5,
  uint8_t *input6,
  uint8_t *input7
);
```

Eight-way SHA2-256. Outputs are 32 bytes each.

```c
void
Hacl_SHA2_Vec256_sha384_4(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3
);
```

Four-way SHA2-384. Outputs are 48 bytes each; inputs are `input_len` bytes each; spec max is 2^125-1.

```c
void
Hacl_SHA2_Vec256_sha512_4(
  uint8_t *dst0,
  uint8_t *dst1,
  uint8_t *dst2,
  uint8_t *dst3,
  uint32_t input_len,
  uint8_t *input0,
  uint8_t *input1,
  uint8_t *input2,
  uint8_t *input3
);
```

Four-way SHA2-512. Outputs are 64 bytes each.

## 14. EverCrypt agile hash API (`EverCrypt_Hash.h`)

EverCrypt exposes one agile fixed-length hash API over the same `Spec_Hash_Definitions_hash_alg` enumeration. Supported public agile algorithms are fixed-length hashes: MD5, SHA1, SHA2-224/256/384/512, SHA3-224/256/384/512, BLAKE2s, BLAKE2b. SHAKE is not a fixed-length hash for these functions.

EverCrypt uses `EverCrypt_Error_error_code`, not `Hacl_Streaming_Types_error_code`. The relevant return values are `EverCrypt_Error_Success` and `EverCrypt_Error_MaximumLengthExceeded`. Call `EverCrypt_AutoConfig2_init()` before using EverCrypt if you want runtime CPU-feature selection. The documented multiplexing includes portable C for all algorithms and SHAEXT/SHA-NI for SHA2-224/SHA2-256; internal tags also allow SIMD BLAKE2 variants.

### Size helper

```c
uint32_t EverCrypt_Hash_Incremental_hash_len(Spec_Hash_Definitions_hash_alg a);
```

Returns fixed digest length in bytes for `a`: MD5 16, SHA1 20, SHA2-224/SHA3-224 28, SHA2-256/SHA3-256/BLAKE2s 32, SHA2-384/SHA3-384 48, SHA2-512/SHA3-512/BLAKE2b 64. SHAKE is not meaningful here.

### Incremental allocation and lifecycle

```c
EverCrypt_Hash_Incremental_state_t
*EverCrypt_Hash_Incremental_malloc(Spec_Hash_Definitions_hash_alg a);
```

Allocates an agile incremental state for algorithm `a`, choosing the best available implementation. Returns `NULL` on allocation failure. Free with `EverCrypt_Hash_Incremental_free`.

```c
void EverCrypt_Hash_Incremental_reset(EverCrypt_Hash_Incremental_state_t *state);
```

Resets the state to empty input with the same algorithm and selected implementation.

```c
EverCrypt_Error_error_code
EverCrypt_Hash_Incremental_update(
  EverCrypt_Hash_Incremental_state_t *state,
  uint8_t *chunk,
  uint32_t chunk_len
);
```

Absorbs `chunk_len` bytes from `chunk`. Returns `EverCrypt_Error_Success` or `EverCrypt_Error_MaximumLengthExceeded` if total updated data since reset exceeds the algorithm's maximum: 2^61-1 for MD5/SHA1/SHA2-224/SHA2-256, 2^125-1 for SHA2-384/SHA2-512; BLAKE2 limits are algorithmic, and SHA3 has no length-encoding bound in the same sense.

```c
Spec_Hash_Definitions_hash_alg
EverCrypt_Hash_Incremental_alg_of_state(EverCrypt_Hash_Incremental_state_t *s);
```

Returns the algorithm stored in `s`.

```c
void
EverCrypt_Hash_Incremental_digest(EverCrypt_Hash_Incremental_state_t *state, uint8_t *output);
```

Writes the current digest to `output`, whose length is `EverCrypt_Hash_Incremental_hash_len(alg)`. It does not consume the state; more updates may follow.

```c
void EverCrypt_Hash_Incremental_free(EverCrypt_Hash_Incremental_state_t *state);
```

Frees an agile incremental state.

### Agile one-shot

```c
void
EverCrypt_Hash_Incremental_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len
);
```

One-shot agile fixed-length hash. `input` is `input_len` bytes; `output` is `EverCrypt_Hash_Incremental_hash_len(a)` bytes; buffers are disjoint. It dispatches to a selected implementation.

### Internal non-public EverCrypt functions

`internal/EverCrypt_Hash.h` declares `EverCrypt_Hash_update_multi_256` and `EverCrypt_Hash_Incremental_hash_256`; these are not in the public header and should not be treated as public API.

## 15. Notes for reimplementers

- **The public enum is ABI, not syntax.** Preserve the numeric constants exactly if compatibility matters.
- **Streaming digest is non-consuming.** Implement it by copying/finalizing internal state or otherwise ensuring the original state remains updateable.
- **Allocation is part of the contract.** The C API heap-allocates states and may return `NULL`; a safe-language reimplementation can expose ownership types, but C-compatible bindings need the same lifecycle.
- **BLAKE2 parameter identity matters.** After allocation, `digest_length`, `key_length`, and `last_node` cannot change across resets.
- **BLAKE2 public comments have copy/paste artifacts.** BLAKE2s comments mention output/key limits of 64 or SIMD widths 128/256 in places; constants and specs define BLAKE2s max key/output as 32 bytes.
- **Portable and vectorized BLAKE2 state types are distinct.** Do not cast between portable and SIMD states.
- **SHA-3 exposes more low-level surface than SHA-2.** Public SHA3 headers include raw Keccak state allocation and SHAKE128 absorb/squeeze block helpers; SHA-2 core compression functions are internal.
- **SHAKE has an absorb/squeeze split.** Fixed SHA3 uses `digest`; SHAKE uses a caller-chosen output length and has low-level helpers that ignore partial blocks in `*_nblocks` routines.
- **Multi-buffer APIs require equal lengths across lanes.** They take arrays-of-pointers (or nested pointer tuples) and a single length for all lanes.
- **MD5 and SHA-1 are still present.** Treat them as legacy compatibility algorithms, not modern cryptographic choices.
- **EverCrypt is both agile and multiplexing.** It selects portable C or optimized implementations after auto-configuration; the public state remains abstract.
