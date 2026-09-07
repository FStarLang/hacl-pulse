# AEAD, symmetric ciphers, and NaCl APIs
This document inventories the generated public C API for symmetric ciphers,
AEAD, and NaCl-compatible `box`/`secretbox` in `dist/gcc-compatible/`. It is
for reimplementers; for general conventions about integer types, byte buffers,
allocation, and error handling, see `design/conventions.md`. For adjacent API
families see `design/api-hashes.md` and `design/api-macs-kdf.md`; for build and
implementation context see `design/implementation.md`, `design/surprises.md`,
and `design/README.md`.
Primary headers covered here:
- `EverCrypt_AEAD.h`, `EverCrypt_Chacha20Poly1305.h`, `EverCrypt_Cipher.h`,
  `EverCrypt_Error.h`
- `Hacl_AEAD_Chacha20Poly1305.h`,
  `Hacl_AEAD_Chacha20Poly1305_Simd128.h`,
  `Hacl_AEAD_Chacha20Poly1305_Simd256.h`
- `Hacl_Chacha20.h`, `Hacl_Chacha20_Vec32.h`, `Hacl_Chacha20_Vec128.h`,
  `Hacl_Chacha20_Vec256.h`
- `Hacl_Salsa20.h`, `Hacl_AES128.h`, `Hacl_NaCl.h`
Internal headers used only to explain representation and multiplexing:
`dist/gcc-compatible/internal/EverCrypt_AEAD.h`,
`dist/gcc-compatible/internal/Hacl_Spec.h`, and
`dist/gcc-compatible/internal/Vale.h`. Do not treat internal declarations as
public API.
## 1. What exists
| Family | Public C entry points | Implementation kind | Notes |
|---|---:|---|---|
| ChaCha20 stream cipher | HACL and EverCrypt wrappers | Portable C plus vectorized C variants | IETF 96-bit nonce, 32-byte key, 32-bit block counter. |
| ChaCha20-Poly1305 AEAD | HACL one-shot, EverCrypt one-shot/stateful | Portable C, SIMD128, SIMD256, and EverCrypt multiplexing | 32-byte key, 12-byte nonce, 16-byte tag. |
| Salsa20/HSalsa20 | HACL C | Portable C | Used by NaCl secretbox/box construction. |
| NaCl secretbox | HACL C | Portable C | XSalsa20-Poly1305-compatible API, 24-byte nonce, 32-byte key. |
| NaCl box | HACL C | Portable C | X25519 + precomputed secretbox key; 24-byte nonce. |
| AES-GCM AEAD | EverCrypt AEAD | Vale assembly only | No portable C AES-GCM in these headers. Runtime requires Vale support plus AES-NI/PCLMULQDQ/AVX/MOVBE/SSE on x64-style builds. |
| AES-CTR | EverCrypt internal/provider code, not in listed public header inventory | Vale assembly only | Not exposed by `EverCrypt_Cipher.h` in `dist/gcc-compatible/`; listed here because the provider has Vale CTR key expansion/mode code. |
| AES-128 block helper | `Hacl_AES128.h` declarations | Assumed/header-only in this dist, not a shipped portable C implementation | `dist/gcc-compatible/` has `Hacl_AES128.h` but no `Hacl_AES128.c`; see AES section. |
HACL* modules are fixed-algorithm C APIs. EverCrypt modules add agility and, for
some algorithms, runtime multiplexing. In this scope, EverCrypt AEAD supports
only:
- `Spec_Agile_AEAD_AES128_GCM`
- `Spec_Agile_AEAD_AES256_GCM`
- `Spec_Agile_AEAD_CHACHA20_POLY1305`
The enum also contains CCM values for parsing/spec purposes, but the generated
EverCrypt AEAD API returns `EverCrypt_Error_UnsupportedAlgorithm` for them.
## 2. Public types and constants
### 2.1 `Spec_Agile_AEAD_alg`
The public constants are macros in `Hacl_Spec.h`:
```c
#define Spec_Agile_AEAD_AES128_GCM 0
#define Spec_Agile_AEAD_AES256_GCM 1
#define Spec_Agile_AEAD_CHACHA20_POLY1305 2
#define Spec_Agile_AEAD_AES128_CCM 3
#define Spec_Agile_AEAD_AES256_CCM 4
#define Spec_Agile_AEAD_AES128_CCM8 5
#define Spec_Agile_AEAD_AES256_CCM8 6
typedef uint8_t Spec_Agile_AEAD_alg;
```
Meanings and support:
| Constant | Value | Meaning | Supported by EverCrypt AEAD here? | Key | Nonce/IV | Tag |
|---|---:|---|---|---:|---:|---:|
| `Spec_Agile_AEAD_AES128_GCM` | 0 | AES-128-GCM | Yes, if Vale/AES-GCM CPU features available | 16 | see below | 16 |
| `Spec_Agile_AEAD_AES256_GCM` | 1 | AES-256-GCM | Yes, if Vale/AES-GCM CPU features available | 32 | see below | 16 |
| `Spec_Agile_AEAD_CHACHA20_POLY1305` | 2 | RFC 8439 ChaCha20-Poly1305 | Yes | 32 | 12 | 16 |
| `Spec_Agile_AEAD_AES128_CCM` | 3 | AES-128-CCM | No | 16 | not public here | 16 |
| `Spec_Agile_AEAD_AES256_CCM` | 4 | AES-256-CCM | No | 32 | not public here | 16 |
| `Spec_Agile_AEAD_AES128_CCM8` | 5 | AES-128-CCM with 8-byte tag | No | 16 | not public here | 8 |
| `Spec_Agile_AEAD_AES256_CCM8` | 6 | AES-256-CCM with 8-byte tag | No | 32 | not public here | 8 |
AES-GCM IV rule from the F* spec and generated C is `iv_len > 0` and `8 * iv_len <= 2^64 - 1`. With a `uint32_t iv_len`, the upper bound is automatic, so the observed public C check rejects only `iv_len == 0`. Standard GCM protocols usually use 12-byte IVs, but this EverCrypt AEAD path includes IV reduction for non-12-byte IVs.
### 2.2 `Spec_Cipher_Expansion_impl` (internal)
This type is not public: it is in `dist/gcc-compatible/internal/Hacl_Spec.h` and
is used inside the internal AEAD state representation.
```c
#define Spec_Cipher_Expansion_Hacl_CHACHA20 0
#define Spec_Cipher_Expansion_Vale_AES128 1
#define Spec_Cipher_Expansion_Vale_AES256 2
typedef uint8_t Spec_Cipher_Expansion_impl;
```
| Constant | Value | Meaning |
|---|---:|---|
| `Spec_Cipher_Expansion_Hacl_CHACHA20` | 0 | Expanded-key state for HACL ChaCha20-Poly1305. |
| `Spec_Cipher_Expansion_Vale_AES128` | 1 | Expanded-key/key-hash state for Vale AES-128-GCM. |
| `Spec_Cipher_Expansion_Vale_AES256` | 2 | Expanded-key/key-hash state for Vale AES-256-GCM. |
### 2.3 `EverCrypt_AEAD_state_s`
Public header:
```c
typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;
```
The public type is abstract/incomplete. Public callers allocate it only through
`EverCrypt_AEAD_create_in` and free it with `EverCrypt_AEAD_free`.
Internal representation, for reimplementers only:
```c
typedef struct EverCrypt_AEAD_state_s_s
{
  Spec_Cipher_Expansion_impl impl;
  uint8_t *ek;
}
EverCrypt_AEAD_state_s;
```
`impl` selects the expanded-key implementation. `ek` points to implementation
specific expanded key material. This representation is not a stable C API.
### 2.4 `EverCrypt_Error_error_code`
Public header:
```c
#define EverCrypt_Error_Success 0
#define EverCrypt_Error_UnsupportedAlgorithm 1
#define EverCrypt_Error_InvalidKey 2
#define EverCrypt_Error_AuthenticationFailure 3
#define EverCrypt_Error_InvalidIVLength 4
#define EverCrypt_Error_DecodeError 5
#define EverCrypt_Error_MaximumLengthExceeded 6
typedef uint8_t EverCrypt_Error_error_code;
```
| Constant | Value | Meaning in this document |
|---|---:|---|
| `EverCrypt_Error_Success` | 0 | Operation succeeded. |
| `EverCrypt_Error_UnsupportedAlgorithm` | 1 | Algorithm identifier unsupported, or required AES-GCM assembly/CPU features unavailable for runtime-checked AES-GCM paths. |
| `EverCrypt_Error_InvalidKey` | 2 | Stateful AEAD entry point was passed `s == NULL`. |
| `EverCrypt_Error_AuthenticationFailure` | 3 | AEAD/Poly1305/GCM tag check failed during decryption. |
| `EverCrypt_Error_InvalidIVLength` | 4 | IV/nonce length rejected. In this scope this matters for AEAD decrypt/encrypt paths, especially ChaCha20-Poly1305 requiring 12 bytes and AES-GCM requiring standard supported IV shape. |
| `EverCrypt_Error_DecodeError` | 5 | Defined globally; not returned by the functions inventoried here. |
| `EverCrypt_Error_MaximumLengthExceeded` | 6 | Defined globally; length bounds are preconditions for most functions here rather than this being commonly returned. |
NaCl functions do **not** return this enum; they return `0` or `0xffffffff`.
HACL ChaCha20-Poly1305 returns `0` or `1` for detached decrypt.
## 3. Shared buffer and length rules
Unless a function-specific section overrides these rules:
- All `uint8_t *` inputs must point to live buffers of the exact byte length
  stated for that parameter. Null is not accepted except where explicitly noted
  (`EverCrypt_AEAD_encrypt/decrypt` accept `s == NULL` and return
  `InvalidKey`; other pointers are caller preconditions).
- Length parameters are 32-bit byte lengths and must match the corresponding
  buffer length exactly.
- Tags for AEAD and NaCl detached APIs are 16 bytes.
- HACL/EverCrypt stream ciphers are XOR stream ciphers: encrypt and decrypt are
  the same transformation with different names.
- In-place operation means exact same starting pointer and length. The proofs
  generally say `eq_or_disjoint`, not arbitrary partial overlap. Partial overlap
  is not permitted unless explicitly specified by the C implementation you are
  reimplementing; treat it as a caller violation.
- Non-output inputs such as key, nonce, AAD, tag, and state must be disjoint
  from output buffers when the F* preconditions require disjointness.
- For `len == 0`, a zero-length message buffer may be unused at the C level, but
  the specification still treats the buffer as the corresponding zero-length
  live buffer.
## 4. EverCrypt AEAD lifecycle and multiplexing
### 4.1 Lifecycle
1. Choose an algorithm constant.
2. Call `EverCrypt_AEAD_create_in(a, &state, key)`.
3. Reuse `state` for any number of encryptions/decryptions with distinct
   nonce-use discipline supplied by the caller/protocol.
4. Call `EverCrypt_AEAD_free(state)` once.
The state contains expanded key material. AES-GCM states contain Vale-expanded
AES key material and GCM key-hash material; ChaCha20-Poly1305 state stores a
HACL key expansion representation.
The `_expand` functions are one-shot convenience functions: they take a raw key,
expand it internally for one operation, and do not require a persistent state.
They are useful when a key is used once or when stack-like allocation is desired.
The F* interface also has an `alloca`/stack-allocation form for verified code,
but no public `EverCrypt_AEAD_alloc*` prototype appears in the generated header.
The `_no_check` AES-GCM functions skip runtime CPU-feature checks; the caller
must already know the binary was built with Vale and the current CPU supports
AES-GCM instructions. If this is wrong, behavior is not a clean error return
(the generated warning says the program may exit on systems compiled without
Vale support, and an unsupported CPU risks illegal instruction behavior).
### 4.2 Runtime support and error codes
| Path | Algorithms | Runtime checks | Unsupported/feature-missing result |
|---|---|---|---|
| `EverCrypt_AEAD_create_in` | AES-128-GCM, AES-256-GCM, ChaCha20-Poly1305 | AES-GCM checks compile support and CPU features; ChaCha20 always supported | `EverCrypt_Error_UnsupportedAlgorithm` |
| `EverCrypt_AEAD_encrypt/decrypt` | Algorithm embedded in state | State must be non-null and valid; IV checked by implementation | `InvalidKey` for null state; `InvalidIVLength` for rejected IV; decrypt may return `AuthenticationFailure` |
| `*_expand_aes128_gcm` / `*_expand_aes256_gcm` | AES-GCM | Runtime CPU-feature checks | `UnsupportedAlgorithm` if missing |
| `*_expand_aes128_gcm_no_check` / `*_expand_aes256_gcm_no_check` | AES-GCM | None | No graceful feature-missing error; caller assumed support |
| `*_expand_chacha20_poly1305` | ChaCha20-Poly1305 | No hardware check required | No unsupported-algorithm path in its F* contract |
| generic `*_expand` | AES-GCM and ChaCha20-Poly1305 public supported set | Runtime dispatch | `UnsupportedAlgorithm` for unsupported enum or missing AES-GCM support |
AES-GCM CPU feature precondition in the F* layer for Vale x64 is:
`hacl_can_compile_vale` and `aesni_enabled`, `pclmulqdq_enabled`, `avx_enabled`,
`movbe_enabled`, and `sse_enabled`. Internal `Vale.h` exposes low-level feature
probes such as `check_aesni`, `check_avx`, `check_movbe`, and `check_sse`, plus
GCM assembly wrappers; these are not public AEAD APIs.
## 5. EverCrypt AEAD public functions
### 5.1 State predicate (generated helper)
```c
bool EverCrypt_AEAD_uu___is_Ek(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s projectee);
```
- Semantics: generated discriminator/predicate for the internal state value and
  algorithm. It is public because it appears in the generated header, but normal
  C callers should not need it.
- Buffers: none.
- Aliasing: not applicable.
- Return: `true`/`false`.
- Preconditions: `projectee` is passed by value; public callers cannot normally
  construct it because the type is abstract in the public header.
### 5.2 Inspect state algorithm
```c
Spec_Agile_AEAD_alg EverCrypt_AEAD_alg_of_state(EverCrypt_AEAD_state_s *s);
```
- Semantics: returns the AEAD algorithm associated with `s`.
- Buffers: `s` points to a live state created by `EverCrypt_AEAD_create_in`.
- Aliasing: not applicable; no output buffers.
- Return: one of the supported `Spec_Agile_AEAD_alg` constants.
- Preconditions: `s` must be non-null and satisfy the EverCrypt AEAD state
  invariant. This function does not advertise an error return for null state.
### 5.3 Create state / expand key
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_create_in(Spec_Agile_AEAD_alg a, EverCrypt_AEAD_state_s **dst, uint8_t *k);
```
- Semantics: allocate and initialize an AEAD state for algorithm `a`; write its
  address to `*dst`.
- Byte lengths:
  - AES-128-GCM: `k` = 16 bytes.
  - AES-256-GCM: `k` = 32 bytes.
  - ChaCha20-Poly1305: `k` = 32 bytes.
  - `dst`: pointer to one writable pointer slot.
- Aliasing: `dst` must be live and writable; `k` is read only. The allocated
  state is fresh. Do not alias `dst` with `k` storage.
- Return:
  - `EverCrypt_Error_Success`: `*dst` is non-null and must later be freed.
  - `EverCrypt_Error_UnsupportedAlgorithm`: bad/unsupported enum or AES-GCM
    unavailable on this target/CPU.
- Preconditions: `k` has the key length for `a`; `dst` is non-null/live.
### 5.4 Stateful encrypt
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Semantics: encrypt `plain` and authenticate associated data `ad`; write
  `plain_len` bytes to `cipher` and a 16-byte tag to `tag`.
- Byte lengths:
  - `s`: expanded key state.
  - `iv`: `iv_len` bytes. ChaCha20-Poly1305 requires 12. AES-GCM accepts any nonzero `iv_len` allowed by `8 * iv_len <= 2^64 - 1`.
  - `ad`: `ad_len` bytes; `ad_len <= 2^31` from F* precondition.
  - `plain`: `plain_len` bytes.
  - `cipher`: `plain_len` bytes.
  - `tag`: 16 bytes for all supported algorithms.
- Maximum plaintext lengths:
  - ChaCha20-Poly1305: `plain_len <= 2^32 - 1 - 16`.
  - AES-128-GCM/AES-256-GCM: `plain_len <= 2^32 - 1`.
- Aliasing:
  - `plain` and `cipher` may be exactly the same buffer for in-place operation,
    or must be disjoint.
  - `cipher` and `tag` must be disjoint.
  - `iv`, `ad`, `tag`, and state footprint must be disjoint from modified
    outputs as required by the F* preconditions.
  - `plain` must be disjoint from `tag` and `ad`; `ad` disjoint from `cipher`
    and `tag`.
- Return:
  - `Success` on success.
  - `InvalidKey` iff `s == NULL`.
  - Implementation may reject bad IV length with `InvalidIVLength` although the
    public comment emphasizes `InvalidKey` for encryption.
- Preconditions: all lengths match buffers; `iv_len > 0`; algorithm-specific IV
  and max-length rules hold; nonce uniqueness is the caller's cryptographic
  responsibility.
### 5.5 One-shot encrypt with raw AES-128-GCM key, no runtime check
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Semantics: expand 16-byte AES-128 key, encrypt with AES-128-GCM, discard
  expansion.
- Byte lengths: `k` 16; `iv` `iv_len` bytes with `iv_len > 0`; `ad` `ad_len`; `plain`/`cipher` `plain_len`; `tag` 16.
- Aliasing: same as `EverCrypt_AEAD_encrypt`, plus `k` must be disjoint from
  `cipher`; outputs disjoint from AAD/tag as above.
- Return: `Success` for valid operation; no `UnsupportedAlgorithm` path in the
  no-check contract.
- Preconditions: all AES-GCM CPU and compile-time Vale requirements are already
  true; `ad_len <= 2^31`; `plain_len <= 2^32 - 1`.
### 5.6 One-shot encrypt with raw AES-256-GCM key, no runtime check
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes256_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Same as 5.5, except `k` is 32 bytes and the algorithm is AES-256-GCM.
### 5.7 One-shot encrypt with raw AES-128-GCM key, runtime checked
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes128_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Semantics/lengths/aliasing: same as 5.5.
- Return: `Success` or `UnsupportedAlgorithm` if Vale/AES-GCM support is absent.
- Preconditions: `k` 16 bytes; AES-GCM IV length is nonzero; length and disjointness rules hold.
### 5.8 One-shot encrypt with raw AES-256-GCM key, runtime checked
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_aes256_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Same as 5.7, except `k` is 32 bytes and the algorithm is AES-256-GCM.
### 5.9 One-shot encrypt with raw ChaCha20-Poly1305 key
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand_chacha20_poly1305(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Semantics: RFC 8439 ChaCha20-Poly1305 one-shot encryption.
- Byte lengths: `k` 32; `iv` 12 and `iv_len == 12`; `ad` `ad_len`;
  `plain`/`cipher` `plain_len`; `tag` 16.
- Maximum lengths: `plain_len <= 2^32 - 1 - 16`; `ad_len <= 2^31` in the
  EverCrypt AEAD precondition.
- Aliasing: `plain == cipher` allowed; otherwise disjoint. `cipher` disjoint
  from `tag`, `ad`, and `k`; `tag` disjoint from `plain`, `ad`, `iv`, `k`.
- Return: `Success` under preconditions.
### 5.10 Generic one-shot encrypt
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_encrypt_expand(
  Spec_Agile_AEAD_alg a,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *plain,
  uint32_t plain_len,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Semantics: dispatch to AES-128-GCM, AES-256-GCM, or ChaCha20-Poly1305.
- Byte lengths: determined by `a` as in the table in section 2.1.
- Aliasing and preconditions: same as the selected algorithm.
- Return: `Success`, or `UnsupportedAlgorithm` for unsupported enum/missing
  AES-GCM features. Decrypt-only authentication failure is not relevant.
### 5.11 Stateful decrypt
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt(
  EverCrypt_AEAD_state_s *s,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);
```
- Semantics: verify `tag` over `ad` and `cipher`; on success write plaintext to
  `dst`.
- Byte lengths:
  - `iv`: ChaCha20-Poly1305 12 bytes; AES-GCM any nonzero `iv_len` within the spec bound.
  - `ad`: `ad_len` bytes, `ad_len <= 2^31`.
  - `cipher`: `cipher_len` bytes.
  - `dst`: `cipher_len` bytes.
  - `tag`: 16 bytes.
- Maximum ciphertext/plaintext lengths:
  - ChaCha20-Poly1305: `cipher_len + 16 <= 2^32 - 1`.
  - AES-GCM: `cipher_len <= 2^32 - 1`.
- Aliasing:
  - `cipher` and `dst` may be exactly the same buffer, or must be disjoint.
  - `tag` must be disjoint from `dst`, `cipher`, and `ad`.
  - `cipher` and `dst` must be disjoint from `ad`.
  - State footprint must be disjoint from `iv`, `ad`, `tag`, `dst`, `cipher`.
- Return:
  - `Success`: tag valid; plaintext written to `dst`.
  - `InvalidKey`: `s == NULL`.
  - `InvalidIVLength`: nonce/IV length rejected.
  - `AuthenticationFailure`: tag check failed. The F* postcondition allows
    `dst` to be modified even on authentication failure for EverCrypt AEAD; do
    not rely on failed decrypt preserving `dst`.
- Preconditions: all buffers live; lengths match; IV rules hold.
### 5.12 One-shot AES-128-GCM decrypt, no runtime check
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes128_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);
```
- Semantics: expand 16-byte AES-128 key, verify/decrypt AES-128-GCM.
- Lengths: `k` 16; `iv` `iv_len` bytes with `iv_len > 0`; `ad` `ad_len`; `cipher`/`dst` `cipher_len`; `tag` 16.
- Aliasing: `cipher == dst` allowed; otherwise disjoint. `k` disjoint from
  `dst`; `tag` disjoint from `dst`, `cipher`, `ad`; `cipher`/`dst` disjoint
  from `ad`.
- Return: `Success` or `AuthenticationFailure`; no graceful unsupported-feature
  return in the no-check contract.
- Preconditions: AES-GCM Vale/CPU support already true; length rules hold.
### 5.13 One-shot AES-256-GCM decrypt, no runtime check
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes256_gcm_no_check(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);
```
- Same as 5.12, except `k` is 32 bytes and the algorithm is AES-256-GCM.
### 5.14 One-shot AES-128-GCM decrypt, runtime checked
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes128_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);
```
- Semantics/lengths/aliasing: same as 5.12.
- Return: `Success`, `AuthenticationFailure`, or `UnsupportedAlgorithm` if
  AES-GCM support is absent.
### 5.15 One-shot AES-256-GCM decrypt, runtime checked
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_aes256_gcm(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);
```
- Same as 5.14, except `k` is 32 bytes and the algorithm is AES-256-GCM.
### 5.16 One-shot ChaCha20-Poly1305 decrypt
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand_chacha20_poly1305(
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);
```
- Semantics: RFC 8439 ChaCha20-Poly1305 verification/decryption.
- Byte lengths: `k` 32; `iv` 12; `ad` `ad_len`; `cipher`/`dst` `cipher_len`;
  `tag` 16.
- Maximum: `cipher_len + 16 <= 2^32 - 1`; `ad_len <= 2^31`.
- Aliasing: `cipher == dst` allowed, otherwise disjoint; all other AEAD decrypt
  disjointness rules apply.
- Return: `Success` or `AuthenticationFailure` under preconditions.
### 5.17 Generic one-shot decrypt
```c
EverCrypt_Error_error_code
EverCrypt_AEAD_decrypt_expand(
  Spec_Agile_AEAD_alg a,
  uint8_t *k,
  uint8_t *iv,
  uint32_t iv_len,
  uint8_t *ad,
  uint32_t ad_len,
  uint8_t *cipher,
  uint32_t cipher_len,
  uint8_t *tag,
  uint8_t *dst
);
```
- Semantics: dispatch to AES-128-GCM, AES-256-GCM, or ChaCha20-Poly1305.
- Lengths/aliasing: selected algorithm's rules.
- Return: `Success`, `AuthenticationFailure`, or `UnsupportedAlgorithm`.
### 5.18 Free state
```c
void EverCrypt_AEAD_free(EverCrypt_AEAD_state_s *s);
```
- Semantics: free a state allocated by `EverCrypt_AEAD_create_in`.
- Buffers: `s` is one live freeable AEAD state.
- Aliasing: no other use of `s` after free.
- Return: none.
- Preconditions: `s` is non-null, freeable, and not already freed.
## 6. EverCrypt ChaCha20-Poly1305 fixed API
These wrappers expose fixed ChaCha20-Poly1305 without the AEAD state object.
They use the same construction as RFC 8439.
### 6.1 Encrypt
```c
void
EverCrypt_Chacha20Poly1305_aead_encrypt(
  uint8_t *k,
  uint8_t *n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Byte lengths: `k` 32; `n` 12; `aad` `aadlen`; `m`/`cipher` `mlen`; `tag` 16.
- Bounds: `mlen + 16 <= SIZE_MAX`; `aadlen + floor(mlen / 64) <= SIZE_MAX` in
  the F* interface; with generated C `uint32_t` lengths, also respect the
  ChaCha20-Poly1305 maximum `mlen <= 2^32 - 1 - 16`.
- Aliasing: `m == cipher` allowed, otherwise disjoint. `cipher` disjoint from
  `tag`, `k`, `n`, and `aad`; `tag` disjoint from `k` and `n`.
- Return: none.
### 6.2 Decrypt
```c
uint32_t
EverCrypt_Chacha20Poly1305_aead_decrypt(
  uint8_t *k,
  uint8_t *n,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t mlen,
  uint8_t *m,
  uint8_t *cipher,
  uint8_t *tag
);
```
- Byte lengths: `k` 32; `n` 12; `aad` `aadlen`; `cipher`/`m` `mlen`; `tag` 16.
- Aliasing: `m == cipher` allowed, otherwise disjoint.
- Return: `0` on authentication success; `1` on failure.
- Failure output: the fixed HACL/EverCrypt ChaCha20-Poly1305 F* contract does
  not promise the same preservation behavior as every HACL public comment;
  safest reimplementation rule is to not expose unauthenticated plaintext and to
  document whether `m` is preserved on failure.
## 7. HACL ChaCha20-Poly1305 AEAD modules
There are three public modules with identical semantics and different names:
- `Hacl_AEAD_Chacha20Poly1305` portable scalar C.
- `Hacl_AEAD_Chacha20Poly1305_Simd128` vectorized C intended for 128-bit SIMD
  platforms (documentation says Intel AVX; development branch mentions Neon).
- `Hacl_AEAD_Chacha20Poly1305_Simd256` vectorized C intended for AVX2.
All use: key 32 bytes, nonce 12 bytes, tag 16 bytes, AAD `data_len` bytes, and
ciphertext length equal to plaintext length. Encryption/decryption can be
in-place (`input` and `output` same buffer). Decrypt returns `0` on success and
`1` on authentication failure; public comments say `output` remains unchanged on
failure.
### 7.1 Portable encrypt
```c
void
Hacl_AEAD_Chacha20Poly1305_encrypt(
  uint8_t *output,
  uint8_t *tag,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *data,
  uint32_t data_len,
  uint8_t *key,
  uint8_t *nonce
);
```
- `output`: `input_len` bytes ciphertext.
- `tag`: 16 bytes written.
- `input`: `input_len` bytes plaintext.
- `data`: `data_len` bytes AAD.
- `key`: 32 bytes; `nonce`: 12 bytes.
- Aliasing: `input == output` allowed; otherwise disjoint. Avoid any partial
  overlap and keep `tag` separate from message/AAD/key/nonce outputs.
### 7.2 Portable decrypt
```c
uint32_t
Hacl_AEAD_Chacha20Poly1305_decrypt(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *data,
  uint32_t data_len,
  uint8_t *key,
  uint8_t *nonce,
  uint8_t *tag
);
```
- `output`: `input_len` bytes plaintext on success.
- `input`: `input_len` bytes ciphertext.
- `tag`: 16 bytes input.
- Other lengths as in encrypt.
- Return: `0` success; `1` failure. Public comment: on failure `output` remains
  unchanged.
### 7.3 SIMD128 encrypt
```c
void
Hacl_AEAD_Chacha20Poly1305_Simd128_encrypt(
  uint8_t *output,
  uint8_t *tag,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *data,
  uint32_t data_len,
  uint8_t *key,
  uint8_t *nonce
);
```
- Same contract as 7.1; implementation requires the target SIMD support.
### 7.4 SIMD128 decrypt
```c
uint32_t
Hacl_AEAD_Chacha20Poly1305_Simd128_decrypt(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *data,
  uint32_t data_len,
  uint8_t *key,
  uint8_t *nonce,
  uint8_t *tag
);
```
- Same contract as 7.2; return `0` success, `1` failure.
### 7.5 SIMD256 encrypt
```c
void
Hacl_AEAD_Chacha20Poly1305_Simd256_encrypt(
  uint8_t *output,
  uint8_t *tag,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *data,
  uint32_t data_len,
  uint8_t *key,
  uint8_t *nonce
);
```
- Same contract as 7.1; implementation requires AVX2-style SIMD support.
### 7.6 SIMD256 decrypt
```c
uint32_t
Hacl_AEAD_Chacha20Poly1305_Simd256_decrypt(
  uint8_t *output,
  uint8_t *input,
  uint32_t input_len,
  uint8_t *data,
  uint32_t data_len,
  uint8_t *key,
  uint8_t *nonce,
  uint8_t *tag
);
```
- Same contract as 7.2; return `0` success, `1` failure.
## 8. ChaCha20 stream cipher APIs
All ChaCha20 functions here use the IETF layout: 32-byte key, 12-byte nonce, and
32-bit block counter. Output length equals input length. Encryption and
decryption are identical XOR-with-keystream operations.
Counter-overflow rule for reimplementers: the 32-bit block counter must not wrap
within an operation. A conservative public rule is
`ctr + ceil(len / 64) <= 2^32`. The vector F* wrappers additionally require the
initial counter plus the vector lane count to fit before vectorized processing:
for Vec32/scalar lane count 1, Vec128 lane count 4, Vec256 lane count 8.
Aliasing for every function in this section: input and output may be exactly the
same buffer or must be disjoint (`eq_or_disjoint`). Key and nonce are read-only
and must be live 32-byte and 12-byte buffers.
### 8.1 Portable encrypt
```c
void
Hacl_Chacha20_chacha20_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- `out`: `len` bytes ciphertext.
- `text`: `len` bytes plaintext.
- `key`: 32 bytes; `n`: 12 bytes.
- `ctr`: initial 32-bit block counter.
- Return: none.
### 8.2 Portable decrypt
```c
void
Hacl_Chacha20_chacha20_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- Same as 8.1 with ciphertext input and plaintext output.
### 8.3 Vec32 encrypt
```c
void
Hacl_Chacha20_Vec32_chacha20_encrypt_32(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- Same external contract as portable ChaCha20. Vec32 is separately named even
  though its lane count is 1 in the vector meta-code.
### 8.4 Vec32 decrypt
```c
void
Hacl_Chacha20_Vec32_chacha20_decrypt_32(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- Same as 8.3 with ciphertext input.
### 8.5 Vec128 encrypt
```c
void
Hacl_Chacha20_Vec128_chacha20_encrypt_128(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- Same contract as 8.1; vector lane count is 4, so avoid counters near
  `2^32 - 4` and ensure the full message does not wrap.
### 8.6 Vec128 decrypt
```c
void
Hacl_Chacha20_Vec128_chacha20_decrypt_128(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- Same as 8.5 with ciphertext input.
### 8.7 Vec256 encrypt
```c
void
Hacl_Chacha20_Vec256_chacha20_encrypt_256(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- Same contract as 8.1; vector lane count is 8, so avoid counters near
  `2^32 - 8` and ensure the full message does not wrap.
### 8.8 Vec256 decrypt
```c
void
Hacl_Chacha20_Vec256_chacha20_decrypt_256(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- Same as 8.7 with ciphertext input.
### 8.9 EverCrypt ChaCha20 wrapper
```c
void
EverCrypt_Cipher_chacha20(
  uint32_t len,
  uint8_t *dst,
  uint8_t *src,
  uint8_t *key,
  uint8_t *iv,
  uint32_t ctr
);
```
- Semantics: encrypt/decrypt `src` into `dst` using ChaCha20.
- Lengths: `dst`/`src` `len`; `key` 32; `iv` 12.
- Aliasing: `src == dst` allowed, otherwise disjoint.
- Return: none.
- Notes: despite the agile name, this public header exposes only ChaCha20, not
  AES-CTR. AES-CTR support in EverCrypt providers is assembly-backed and not in
  this public header inventory.
## 9. Salsa20 and HSalsa20 APIs
Salsa20 here uses a 32-byte key, an 8-byte nonce for `salsa20_encrypt/decrypt`,
and a 64-bit logical block counter represented by the `uint32_t ctr` public
parameter in this generated API. HSalsa20 uses a 32-byte key and 16-byte nonce
and produces a 32-byte subkey. `salsa20_key_block0` produces the first 64-byte
keystream block for key and 8-byte nonce.
Aliasing: stream cipher input and output may be exactly equal or disjoint. The
helper functions write to `out`; keep `out` separate from key/nonce unless an
implementation explicitly documents otherwise.
### 9.1 Salsa20 encrypt
```c
void
Hacl_Salsa20_salsa20_encrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *text,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- `out`/`text`: `len` bytes.
- `key`: 32 bytes.
- `n`: 8 bytes.
- `ctr`: initial block counter.
- Return: none.
### 9.2 Salsa20 decrypt
```c
void
Hacl_Salsa20_salsa20_decrypt(
  uint32_t len,
  uint8_t *out,
  uint8_t *cipher,
  uint8_t *key,
  uint8_t *n,
  uint32_t ctr
);
```
- Same as 9.1 with ciphertext input.
### 9.3 Salsa20 block 0
```c
void Hacl_Salsa20_salsa20_key_block0(uint8_t *out, uint8_t *key, uint8_t *n);
```
- Semantics: write Salsa20 keystream block zero.
- Lengths: `out` 64 bytes; `key` 32 bytes; `n` 8 bytes.
- Return: none.
### 9.4 HSalsa20
```c
void Hacl_Salsa20_hsalsa20(uint8_t *out, uint8_t *key, uint8_t *n);
```
- Semantics: derive XSalsa20 subkey from key and 16-byte nonce prefix.
- Lengths: `out` 32 bytes; `key` 32 bytes; `n` 16 bytes.
- Return: none.
## 10. AES APIs and caveats
### 10.1 What is available
Public header:
```c
extern void Hacl_AES128_aes128_key_expansion(uint8_t *key, uint8_t *expanded_key);
```
```c
extern void
Hacl_AES128_aes128_encrypt_block(uint16_t *cipher, uint16_t *plain, uint8_t *expanded_key);
```
The F* interface in `code/frodo/Hacl.AES128.fsti` specifies:
- `key`: 16 bytes.
- `expanded_key`: 176 bytes (`11 * 16`).
- `plain`: 8 `uint16_t` words = 16 bytes interpreted as little-endian bytes.
- `cipher`: 8 `uint16_t` words = 16 bytes.
Preconditions from the F* interface:
- Key expansion: `key` and `expanded_key` are live and disjoint.
- Block encryption: `cipher`, `plain`, and `expanded_key` are live. The
  interface does not require `cipher` and `plain` to be disjoint, so in-place
  block encryption is allowed by the specification.
Important caveat: in `dist/gcc-compatible/`, there is a public
`Hacl_AES128.h`, but no corresponding `Hacl_AES128.c`. This is not a general
portable C AES implementation in the distribution. It is an assumed helper
interface used by Frodo-related code paths. Do not reimplement this as if it
were the library's portable AES-GCM or AES-CTR backend.
### 10.2 AES-GCM and AES-CTR
AES-GCM used by EverCrypt AEAD is Vale assembly-backed. Public EverCrypt AEAD
performs runtime checks for supported AES-GCM paths unless a `_no_check` entry
point is used.
AES-CTR is present in EverCrypt provider/Vale code, but not exposed in the
listed `EverCrypt_Cipher.h` public header. If reimplementing a sibling API that
exposes it, treat it as assembly-only in HACL*/EverCrypt and do not infer a
portable C fallback from `Hacl_AES128.h`.
Security caveats:
- AES-GCM nonce reuse under the same key is catastrophic; the API does not track
  nonces.
- Assembly feature checks are part of the safe API contract. `_no_check` is only
  safe behind an equivalent feature gate.
- `Hacl_AES128.h` block encryption alone is not an AEAD or mode API and provides
  no authentication.
## 11. NaCl-compatible APIs
`Hacl_NaCl.h` implements APIs compatible with NaCl/libsodium style names. Return
convention differs from EverCrypt:
- success: `0`
- failure: `0xffffffff` (the `uint32_t` representation of `-1`) for NaCl public
  box/secretbox operations that can fail
Detached APIs separate the 16-byte tag from ciphertext. Easy APIs prepend the
16-byte tag to the ciphertext in a combined buffer. Legacy NaCl padded APIs use
zero-padding conventions described below.
Constants by convention:
| Name | Size |
|---|---:|
| `crypto_secretbox_KEYBYTES` | 32 |
| `crypto_secretbox_NONCEBYTES` | 24 |
| `crypto_secretbox_MACBYTES` | 16 |
| `crypto_box_PUBLICKEYBYTES` | 32 |
| `crypto_box_SECRETKEYBYTES` | 32 |
| `crypto_box_BEFORENMBYTES` | 32 |
| `crypto_box_NONCEBYTES` | 24 |
| `crypto_box_MACBYTES` | 16 |
| `crypto_secretbox_ZEROBYTES` | 32 |
| `crypto_secretbox_BOXZEROBYTES` | 16 |
| `crypto_box_ZEROBYTES` | 32 |
| `crypto_box_BOXZEROBYTES` | 16 |
Zero-padding convention for legacy NaCl `crypto_secretbox`/`crypto_box` (not
separately exposed as named public prototypes in this generated header, but
implemented by the easy/detached constructions): the caller's padded message has
32 leading zero bytes. The padded ciphertext has 16 leading zero bytes followed
by a 16-byte authenticator and encrypted payload. Easy APIs remove this burden:
`easy` writes `tag || cipher` of length `16 + mlen`; `open_easy` consumes the
same and returns only plaintext.
### 11.1 Secretbox detached encrypt
```c
uint32_t
Hacl_NaCl_crypto_secretbox_detached(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);
```
- Semantics: XSalsa20-Poly1305 secretbox encryption with separate tag.
- Lengths: `c` `mlen`; `tag` 16; `m` `mlen`; `n` 24; `k` 32.
- Aliasing: public comment permits `c` and `m` to be the same buffer for
  in-place encryption; otherwise avoid overlap. `tag` separate.
- Return: `0` on success.
### 11.2 Secretbox detached open
```c
uint32_t
Hacl_NaCl_crypto_secretbox_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);
```
- Semantics: verify and decrypt detached secretbox.
- Lengths: `m` `mlen`; `c` `mlen`; `tag` 16; `n` 24; `k` 32.
- Aliasing: `m == c` allowed for in-place decryption.
- Return: `0` on success; `0xffffffff` on authentication failure.
### 11.3 Secretbox easy encrypt
```c
uint32_t
Hacl_NaCl_crypto_secretbox_easy(uint8_t *c, uint8_t *m, uint32_t mlen, uint8_t *n, uint8_t *k);
```
- Semantics: write combined `tag || ciphertext`.
- Lengths: `c` `16 + mlen`; `m` `mlen`; `n` 24; `k` 32.
- Aliasing: not explicitly documented as in-place in the header for easy; use
  non-overlapping `c` and `m` unless matching the exact C implementation.
- Return: `0` on success.
### 11.4 Secretbox easy open
```c
uint32_t
Hacl_NaCl_crypto_secretbox_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *k
);
```
- Semantics: verify combined `tag || ciphertext` and write plaintext.
- Lengths: `c` `clen`; `m` `clen - 16`; `n` 24; `k` 32.
- Preconditions: `clen >= 16`; for a non-empty message, `clen > 16` as the
  older docs phrase it. The implementation passes `clen - 16` to detached open.
- Return: `0` on success; `0xffffffff` on failure.
### 11.5 Box precomputation
```c
uint32_t Hacl_NaCl_crypto_box_beforenm(uint8_t *k, uint8_t *pk, uint8_t *sk);
```
- Semantics: compute a shared 32-byte symmetric key from their public key and my
  secret key. Internally this is X25519 followed by the NaCl box key derivation.
- Lengths: `k` 32 output; `pk` 32 input; `sk` 32 input.
- Aliasing: `k` must be disjoint from `pk` and `sk`.
- Return: `0` on success; `0xffffffff` on failure, e.g. invalid low-order public
  key/shared-secret failure.
### 11.6 Box detached after precomputation
```c
uint32_t
Hacl_NaCl_crypto_box_detached_afternm(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);
```
- Semantics: encrypt using precomputed `k` from `crypto_box_beforenm`.
- Lengths: `c` `mlen`; `tag` 16; `m` `mlen`; `n` 24; `k` 32.
- Aliasing: same as secretbox detached encrypt; `c == m` allowed by underlying
  secretbox style.
- Return: `0` on success.
### 11.7 Box detached encrypt
```c
uint32_t
Hacl_NaCl_crypto_box_detached(
  uint8_t *c,
  uint8_t *tag,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);
```
- Semantics: compute shared key from recipient public key `pk` and sender secret
  key `sk`, then encrypt detached.
- Lengths: `c` `mlen`; `tag` 16; `m` `mlen`; `n` 24; `pk` 32; `sk` 32.
- Aliasing: `c == m` allowed by the underlying secretbox call; keep tag/key
  inputs separate from outputs.
- Return: `0` on success; `0xffffffff` if precomputation fails.
### 11.8 Box detached open after precomputation
```c
uint32_t
Hacl_NaCl_crypto_box_open_detached_afternm(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);
```
- Semantics: verify/decrypt using precomputed `k`.
- Lengths: `m` `mlen`; `c` `mlen`; `tag` 16; `n` 24; `k` 32.
- Aliasing: `m == c` allowed.
- Return: `0` on success; `0xffffffff` on authentication failure.
### 11.9 Box detached open
```c
uint32_t
Hacl_NaCl_crypto_box_open_detached(
  uint8_t *m,
  uint8_t *c,
  uint8_t *tag,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);
```
- Semantics: compute shared key from sender public key `pk` and recipient secret
  key `sk`, then verify/decrypt detached.
- Lengths: `m` `mlen`; `c` `mlen`; `tag` 16; `n` 24; `pk` 32; `sk` 32.
- Aliasing: `m == c` allowed.
- Return: `0` success; `0xffffffff` for precomputation or authentication
  failure.
### 11.10 Box easy after precomputation
```c
uint32_t
Hacl_NaCl_crypto_box_easy_afternm(
  uint8_t *c,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *k
);
```
- Semantics: write combined `tag || ciphertext` using precomputed key.
- Lengths: `c` `16 + mlen`; `m` `mlen`; `n` 24; `k` 32.
- Aliasing: use non-overlapping `c` and `m` for the combined easy API unless
  duplicating the C layout exactly.
- Return: `0` success.
### 11.11 Box easy encrypt
```c
uint32_t
Hacl_NaCl_crypto_box_easy(
  uint8_t *c,
  uint8_t *m,
  uint32_t mlen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);
```
- Semantics: compute shared key from recipient public key `pk` and sender secret
  key `sk`, then write `tag || ciphertext`.
- Lengths: `c` `16 + mlen`; `m` `mlen`; `n` 24; `pk` 32; `sk` 32.
- Return: `0` success; `0xffffffff` if precomputation fails.
### 11.12 Box easy open after precomputation
```c
uint32_t
Hacl_NaCl_crypto_box_open_easy_afternm(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *k
);
```
- Semantics: verify/decrypt combined `tag || ciphertext` using precomputed key.
- Lengths: `c` `clen`; `m` `clen - 16`; `n` 24; `k` 32.
- Preconditions: `clen >= 16`.
- Return: `0` success; `0xffffffff` failure.
### 11.13 Box easy open
```c
uint32_t
Hacl_NaCl_crypto_box_open_easy(
  uint8_t *m,
  uint8_t *c,
  uint32_t clen,
  uint8_t *n,
  uint8_t *pk,
  uint8_t *sk
);
```
- Semantics: compute shared key from sender public key `pk` and recipient secret
  key `sk`, then verify/decrypt combined `tag || ciphertext`.
- Lengths: `c` `clen`; `m` `clen - 16`; `n` 24; `pk` 32; `sk` 32.
- Preconditions: `clen >= 16`.
- Return: `0` success; `0xffffffff` for precomputation/authentication failure.
## 12. Notes for reimplementers
1. **Stateful EverCrypt AEAD requires state.** Encrypt/decrypt take an expanded-key `EverCrypt_AEAD_state_s *`, not a raw key.
2. **`_expand` is the one-shot raw-key family.** It expands internally for one operation and does not allocate persistent public state.
3. **`_no_check` skips CPU detection only.** AES-GCM authentication remains; unsupported hardware may exit or fault instead of returning an error.
4. **EverCrypt has a distinct authentication error.** Decrypt returns `EverCrypt_Error_AuthenticationFailure` (3).
5. **NaCl and HACL fixed AEAD use different return conventions.** NaCl returns `0`/`0xffffffff`; HACL ChaCha20-Poly1305 decrypt returns `0`/`1`.
6. **In-place means exact alias.** The proofs say `eq_or_disjoint`; partial overlaps are outside the contract.
7. **AAD/tag/key/nonce disjointness is real.** C signatures hide many required non-overlap preconditions.
8. **EverCrypt AEAD decrypt failure may modify `dst`.** HACL ChaCha20-Poly1305 comments promise preservation on failure; EverCrypt AEAD does not.
9. **ChaCha20-Poly1305 exists under three HACL module names.** Portable, SIMD128, and SIMD256 are separate symbols with the same API shape.
10. **ChaCha20 stream cipher exists under several names.** Scalar, Vec32, Vec128, Vec256, plus `EverCrypt_Cipher_chacha20`.
11. **AES-GCM is assembly-only in this scope.** Do not infer a portable C GCM backend from `Hacl_AES128.h`.
12. **`Hacl_AES128.h` is not a complete shipped C AES library.** This dist has declarations but no matching `Hacl_AES128.c`.
13. **AES-GCM has IV reduction.** The observed C rejects `iv_len == 0`; 12-byte IVs are standard, but not the only accepted length here.
14. **The AEAD enum includes unsupported CCM values.** EverCrypt AEAD returns `UnsupportedAlgorithm` for them.
15. **Feature initialization matters.** Runtime-checked AES-GCM depends on EverCrypt target configuration/CPU feature flags.
16. **Nonce uniqueness is external.** No API tracks or prevents nonce reuse.
17. **NaCl easy buffers are tag-first.** They contain `tag || ciphertext`.
18. **`beforenm` output is secret key material.** Store and zeroize it as a 32-byte symmetric key.
