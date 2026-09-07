# API surface: FrodoKEM, HPKE, randomness/DRBG, CPU dispatch, and support headers

This note documents the generated public C surface used by post-quantum KEM, HPKE, randomness, CPU feature detection, and low-level support code in `dist/gcc-compatible/`.
It is for teams reimplementing the library in a language similar to, but not identical to, F*.

Primary source of truth: generated public headers and nearby generated C files in `dist/gcc-compatible/`.
Secondary source of truth: the F*/Low* sources under `code/frodo/`, `code/hpke/`, `code/drbg/`, `code/meta/`, `providers/evercrypt/`, `lib/`, and the `doc/*.rst` files named in the task.

Cross-references for common conventions and broader architecture:

- `design/README.md` (requested sibling cross-reference; absent in this checkout at writing time)
- `design/conventions.md`
- `design/api-hashes.md`
- `design/api-curves.md` (requested sibling cross-reference; absent in this checkout at writing time)
- `design/implementation.md`
- `design/surprises.md`

Rules used below:

- Prototypes are copied verbatim from generated headers.
- Byte sizes are copied from generated headers or generated C definitions.
- A value is marked `unconfirmed` if it could not be confirmed from the requested sources.
- This file deliberately avoids loop-level implementation detail and proof machinery.

---

## 1. FrodoKEM

### 1.1 Public headers and modules

- `dist/gcc-compatible/Hacl_Frodo64.h`
- `dist/gcc-compatible/Hacl_Frodo640.h`
- `dist/gcc-compatible/Hacl_Frodo976.h`
- `dist/gcc-compatible/Hacl_Frodo1344.h`
- `dist/gcc-compatible/internal/Hacl_Frodo_KEM.h` for internal helper declarations such as `randombytes_`.
- Generated C definitions in `dist/gcc-compatible/Hacl_Frodo64.c`, `Hacl_Frodo640.c`, `Hacl_Frodo976.c`, and `Hacl_Frodo1344.c` confirm exact sizes and return values.

The four exported modules are fixed-parameter FrodoKEM instantiations.
There is no runtime parameter object; callers choose the C module name at compile time.

### 1.2 Parameter sets and exact byte sizes

The generated headers expose byte-size variables, and the generated C files define them with these values:

| Parameter set | Header | Shared-secret bytes (`crypto_bytes`) | Public-key bytes | Secret-key bytes | Ciphertext bytes | Status |
|---|---:|---:|---:|---:|---:|---|
| Frodo64 | `Hacl_Frodo64.h` | 16 | 976 | 2032 | 1080 | **Toy/test-only**; not a production security level. |
| Frodo640 | `Hacl_Frodo640.h` | 16 | 9616 | 19888 | 9720 | Production-size FrodoKEM parameter set. |
| Frodo976 | `Hacl_Frodo976.h` | 24 | 15632 | 31296 | 15744 | Production-size FrodoKEM parameter set. |
| Frodo1344 | `Hacl_Frodo1344.h` | 32 | 21520 | 43088 | 21632 | Production-size FrodoKEM parameter set. |

Warning for reimplementers: `Frodo64` is present in the public generated distribution, but it is a small testing/toy parameter set.
Do not present it as production post-quantum security.

### 1.3 Size variables

Each Frodo header exports four mutable-looking C variables, not preprocessor constants.
Treat them as read-only constants in a reimplementation.

```c
extern uint32_t Hacl_Frodo64_crypto_bytes;
extern uint32_t Hacl_Frodo64_crypto_publickeybytes;
extern uint32_t Hacl_Frodo64_crypto_secretkeybytes;
extern uint32_t Hacl_Frodo64_crypto_ciphertextbytes;

extern uint32_t Hacl_Frodo640_crypto_bytes;
extern uint32_t Hacl_Frodo640_crypto_publickeybytes;
extern uint32_t Hacl_Frodo640_crypto_secretkeybytes;
extern uint32_t Hacl_Frodo640_crypto_ciphertextbytes;

extern uint32_t Hacl_Frodo976_crypto_bytes;
extern uint32_t Hacl_Frodo976_crypto_publickeybytes;
extern uint32_t Hacl_Frodo976_crypto_secretkeybytes;
extern uint32_t Hacl_Frodo976_crypto_ciphertextbytes;

extern uint32_t Hacl_Frodo1344_crypto_bytes;
extern uint32_t Hacl_Frodo1344_crypto_publickeybytes;
extern uint32_t Hacl_Frodo1344_crypto_secretkeybytes;
extern uint32_t Hacl_Frodo1344_crypto_ciphertextbytes;
```

### 1.4 Key generation, encapsulation, and decapsulation prototypes

#### Frodo64

```c
uint32_t Hacl_Frodo64_crypto_kem_keypair(uint8_t *pk, uint8_t *sk);

uint32_t Hacl_Frodo64_crypto_kem_enc(uint8_t *ct, uint8_t *ss, uint8_t *pk);

uint32_t Hacl_Frodo64_crypto_kem_dec(uint8_t *ss, uint8_t *ct, uint8_t *sk);
```

#### Frodo640

```c
uint32_t Hacl_Frodo640_crypto_kem_keypair(uint8_t *pk, uint8_t *sk);

uint32_t Hacl_Frodo640_crypto_kem_enc(uint8_t *ct, uint8_t *ss, uint8_t *pk);

uint32_t Hacl_Frodo640_crypto_kem_dec(uint8_t *ss, uint8_t *ct, uint8_t *sk);
```

#### Frodo976

```c
uint32_t Hacl_Frodo976_crypto_kem_keypair(uint8_t *pk, uint8_t *sk);

uint32_t Hacl_Frodo976_crypto_kem_enc(uint8_t *ct, uint8_t *ss, uint8_t *pk);

uint32_t Hacl_Frodo976_crypto_kem_dec(uint8_t *ss, uint8_t *ct, uint8_t *sk);
```

#### Frodo1344

```c
uint32_t Hacl_Frodo1344_crypto_kem_keypair(uint8_t *pk, uint8_t *sk);

uint32_t Hacl_Frodo1344_crypto_kem_enc(uint8_t *ct, uint8_t *ss, uint8_t *pk);

uint32_t Hacl_Frodo1344_crypto_kem_dec(uint8_t *ss, uint8_t *ct, uint8_t *sk);
```

### 1.5 Buffer contracts

The public C prototypes do not carry lengths.
The caller must allocate exactly the parameter-set sizes above:

- `pk`: public-key bytes for the selected parameter set.
- `sk`: secret-key bytes for the selected parameter set.
- `ct`: ciphertext bytes for the selected parameter set.
- `ss`: `crypto_bytes`, i.e. shared-secret bytes for the selected parameter set.

Aliasing restrictions are not documented in the C headers.
The F*/Low* sources prove/use stronger live/disjointness facts internally, but the generated public Frodo signatures expose only raw pointers.

### 1.6 Return convention

All three exported Frodo KEM functions return `uint32_t`.
The generated C definitions for all four parameter sets end each `keypair`, `enc`, and `dec` function with `return 0U;`.
No public failure code is surfaced by these generated Frodo APIs.

Important consequence: entropy failure is not propagated.
The internal `randombytes_` shim calls `Lib_RandomBuffer_System_randombytes`, stores the returned `bool`, then discards it via `KRML_MAYBE_UNUSED_VAR(b)`.
A reimplementation should decide whether to preserve this API-compatible behavior or expose entropy failure explicitly in a safer higher-level API.

### 1.7 Randomness used by Frodo

The internal helper is declared in `internal/Hacl_Frodo_KEM.h`:

```c
void randombytes_(uint32_t len, uint8_t *res);
```

The generated implementation in `Hacl_Frodo_KEM.c` is:

```c
void randombytes_(uint32_t len, uint8_t *res)
{
  bool b = Lib_RandomBuffer_System_randombytes(res, len);
  KRML_MAYBE_UNUSED_VAR(b);
}
```

Per generated Frodo C files, random byte counts are:

| Parameter set | Keygen random bytes | Encapsulation random bytes |
|---|---:|---:|
| Frodo64 | 48 | 16 |
| Frodo640 | 48 | 16 |
| Frodo976 | 64 | 24 |
| Frodo1344 | 80 | 32 |

The keygen count is `2 * crypto_bytes + 16` for the observed parameter sets.
The encapsulation count is `crypto_bytes`.

---

## 2. HPKE (RFC 9180)

### 2.1 Public headers and naming scheme

The generated HPKE headers in this distribution are fully monomorphized modules.
Each header name fixes:

1. KEM/DH implementation: `Curve51`, `Curve64`, or `P256`.
2. AEAD implementation family: `CP32`, `CP128`, or `CP256`.
3. HPKE KDF hash: `SHA256` or `SHA512` as shipped for X25519; only `SHA256` as shipped for P-256.

Observed module-name form:

```text
Hacl_HPKE_<Curve51|Curve64|P256>_<CP32|CP128|CP256>_<SHA256|SHA512>
```

Important nuance: `CP32`, `CP128`, and `CP256` do **not** select different RFC 9180 AEAD algorithm identifiers in the observed sources.
The `code/hpke/Hacl.HPKE.Interface.AEAD.*` files show all three are instantiations of `CHACHA20_POLY1305`, using the `Hacl.Chacha20Poly1305_32`, `_128`, and `_256` implementations respectively.
The RFC HPKE AEAD id written into the suite id is therefore `0x0003` for all shipped HPKE headers listed here.

`Curve51` and `Curve64` both implement X25519 (`DH_Curve25519`).
`Curve51` uses the portable 51-bit-limb Curve25519 implementation.
`Curve64` uses the 64-bit/Vale-oriented Curve25519 implementation and its F* interface requires `adx_enabled` and `bmi2_enabled`.
`P256` uses the P-256 DH implementation.

The shared context struct is in `Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE.h`:

```c
typedef struct Hacl_Impl_HPKE_context_s_s
{
  uint8_t *ctx_key;
  uint8_t *ctx_nonce;
  uint64_t *ctx_seq;
  uint8_t *ctx_exporter;
}
Hacl_Impl_HPKE_context_s;
```

The struct stores pointers to caller-allocated buffers; it does not own storage.

### 2.2 Implemented modes

Only HPKE Base mode is exported in the generated public HPKE variant headers.
Each shipped variant exposes exactly these four functions:

- `setupBaseS`
- `setupBaseR`
- `sealBase`
- `openBase`

The HPKE specs contain mode names `Base`, `PSK`, `Auth`, and `AuthPSK`, but no public generated `setupPSK`, `setupAuth`, `sealAuth`, `openAuth`, or AuthPSK API was observed in the shipped headers.
For this API surface:

| HPKE mode | Public support in these headers |
|---|---|
| Base | Implemented. |
| PSK | Not implemented as a public generated HPKE API here. |
| Auth | Not implemented as a public generated HPKE API here. |
| AuthPSK | Not implemented as a public generated HPKE API here. |

### 2.3 Representative prototypes copied verbatim

From `dist/gcc-compatible/Hacl_HPKE_Curve51_CP32_SHA256.h`:

```c
uint32_t
Hacl_HPKE_Curve51_CP32_SHA256_setupBaseS(
  uint8_t *o_pkE,
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info
);

uint32_t
Hacl_HPKE_Curve51_CP32_SHA256_setupBaseR(
  Hacl_Impl_HPKE_context_s o_ctx,
  uint8_t *enc,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info
);

uint32_t
Hacl_HPKE_Curve51_CP32_SHA256_sealBase(
  uint8_t *skE,
  uint8_t *pkR,
  uint32_t infolen,
  uint8_t *info,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t plainlen,
  uint8_t *plain,
  uint8_t *o_enc,
  uint8_t *o_ct
);

uint32_t
Hacl_HPKE_Curve51_CP32_SHA256_openBase(
  uint8_t *pkE,
  uint8_t *skR,
  uint32_t infolen,
  uint8_t *info,
  uint32_t aadlen,
  uint8_t *aad,
  uint32_t ctlen,
  uint8_t *ct,
  uint8_t *o_pt
);
```

The other generated variant headers have the same signatures after substituting the module prefix.

### 2.4 Exact HPKE buffer sizes

The generated public HPKE headers do not expose named size constants.
The exact sizes below are confirmed from `Spec.Agile.HPKE.*`, `Hacl.HPKE.Interface.DH.*`, `Hacl.HPKE.Interface.AEAD.*`, and `Hacl.Impl.HPKE.*`.

| Quantity | X25519 / Curve51 / Curve64 | P-256 / P256 | Source/notes |
|---|---:|---:|---|
| DH secret key `skE`, `skR` | 32 | 32 | `DH.size_key`. |
| Recipient public key input `pkR` to `setupBaseS`/`sealBase` | 32 | 64 | `serialized_point_dh`; P-256 serialized point is 64 bytes. |
| Encapsulated public key output `o_pkE` / `o_enc` | 32 | 65 | `size_dh_public`; P-256 adds one representation byte. |
| Encapsulated public key input `enc` / `pkE` to receiver/open | 32 | 65 | `setupBaseR` uses `key_dh_public`. |
| AEAD key `ctx_key` | 32 | 32 | All shipped variants are ChaCha20-Poly1305. |
| AEAD nonce/base nonce `ctx_nonce` | 12 | 12 | `size_aead_nonce`. |
| AEAD tag appended to ciphertext | 16 | 16 | `AEAD.tag_length CHACHA20_POLY1305`. |
| Ciphertext buffer `o_ct` for `sealBase` | `plainlen + 16` | `plainlen + 16` | Output contains ciphertext followed by tag. |
| Plaintext output `o_pt` for `openBase` | `ctlen - 16` | `ctlen - 16` | Requires `ctlen > 16` in F* type. |
| Context sequence `ctx_seq` | one `uint64_t` | one `uint64_t` | Generated context struct stores `uint64_t *ctx_seq`. |
| Exporter secret `ctx_exporter` with SHA-256 KDF | 32 | 32 | `size_kdf = Hash.hash_length SHA2_256`. |
| Exporter secret `ctx_exporter` with SHA-512 KDF | 64 | not shipped | `size_kdf = Hash.hash_length SHA2_512`. |
| Key-schedule context with SHA-256 KDF | 65 | 65 | `size_ks_ctx = 1 + 2 * size_kdf`. |
| Key-schedule context with SHA-512 KDF | 129 | not shipped | `size_ks_ctx = 1 + 2 * size_kdf`. |
| KEM hash/KEM key length | 32 | 32 | All observed KEMs use SHA-256 as KEM hash. |

For one-shot `sealBase`, callers allocate `o_enc` as the encapsulated public key size and `o_ct` as `plainlen + 16`.
For one-shot `openBase`, callers pass `ctlen` including the 16-byte tag and allocate `o_pt` as `ctlen - 16`.

For `setupBaseS` and `setupBaseR`, callers allocate and populate `Hacl_Impl_HPKE_context_s` manually:

```c
Hacl_Impl_HPKE_context_s ctx;
ctx.ctx_key = /* 32 bytes for all shipped variants */;
ctx.ctx_nonce = /* 12 bytes */;
ctx.ctx_seq = /* pointer to one uint64_t */;
ctx.ctx_exporter = /* 32 bytes for SHA256 variants, 64 bytes for SHA512 variants */;
```

The generated code treats `ctx_seq` as a 64-bit sequence counter.
The F* comment notes that RFC HPKE counter overflow is at `2**96`, but this implementation represents the counter as `uint64_t`, so overflow occurs earlier.

### 2.5 HPKE return convention

All HPKE functions return `uint32_t`.
The F* specifications for the extracted API use:

- `0ul`: success.
- `1ul`: failure.
- Other values: impossible/unreachable by the specification.

Typical failure causes are invalid DH input, AEAD authentication failure on `openBase`, or the implementation-specific sequence counter overflow path.
The public C headers do not expose richer error codes.

### 2.6 Shipped HPKE variants

All shipped variants have KEM hash SHA-256 and AEAD ChaCha20-Poly1305 (`0x0003`).
`CP32`, `CP128`, and `CP256` are implementation choices for ChaCha20-Poly1305, not distinct HPKE AEAD algorithms.

| Header | KEM/DH | KEM public enc bytes | Recipient public key input bytes | AEAD implementation | HPKE KDF hash | Exporter secret bytes | Notes |
|---|---|---:|---:|---|---|---:|---|
| `Hacl_HPKE_Curve51_CP32_SHA256.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP32` | SHA-256 | 32 | portable 51-bit X25519. |
| `Hacl_HPKE_Curve51_CP32_SHA512.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP32` | SHA-512 | 64 | portable 51-bit X25519. |
| `Hacl_HPKE_Curve51_CP128_SHA256.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP128` | SHA-256 | 32 | portable 51-bit X25519. |
| `Hacl_HPKE_Curve51_CP128_SHA512.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP128` | SHA-512 | 64 | portable 51-bit X25519. |
| `Hacl_HPKE_Curve51_CP256_SHA256.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP256` | SHA-256 | 32 | portable 51-bit X25519. |
| `Hacl_HPKE_Curve51_CP256_SHA512.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP256` | SHA-512 | 64 | portable 51-bit X25519. |
| `Hacl_HPKE_Curve64_CP32_SHA256.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP32` | SHA-256 | 32 | 64-bit X25519; requires ADX/BMI2 in F* interface. |
| `Hacl_HPKE_Curve64_CP32_SHA512.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP32` | SHA-512 | 64 | 64-bit X25519; requires ADX/BMI2 in F* interface. |
| `Hacl_HPKE_Curve64_CP128_SHA256.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP128` | SHA-256 | 32 | 64-bit X25519; requires ADX/BMI2 in F* interface. |
| `Hacl_HPKE_Curve64_CP128_SHA512.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP128` | SHA-512 | 64 | 64-bit X25519; requires ADX/BMI2 in F* interface. |
| `Hacl_HPKE_Curve64_CP256_SHA256.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP256` | SHA-256 | 32 | 64-bit X25519; requires ADX/BMI2 in F* interface. |
| `Hacl_HPKE_Curve64_CP256_SHA512.h` | X25519 | 32 | 32 | ChaCha20-Poly1305 `CP256` | SHA-512 | 64 | 64-bit X25519; requires ADX/BMI2 in F* interface. |
| `Hacl_HPKE_P256_CP32_SHA256.h` | P-256 DH | 65 | 64 | ChaCha20-Poly1305 `CP32` | SHA-256 | 32 | P-256 encapsulated key includes one extra representation byte. |
| `Hacl_HPKE_P256_CP128_SHA256.h` | P-256 DH | 65 | 64 | ChaCha20-Poly1305 `CP128` | SHA-256 | 32 | P-256 encapsulated key includes one extra representation byte. |
| `Hacl_HPKE_P256_CP256_SHA256.h` | P-256 DH | 65 | 64 | ChaCha20-Poly1305 `CP256` | SHA-256 | 32 | P-256 encapsulated key includes one extra representation byte. |

### 2.7 Meta-programming and monomorphization

The `code/hpke/Hacl.Meta.HPKE.fst` layer specializes four generic implementation functions:

```text
Hacl.Impl.HPKE.setupBaseS
Hacl.Impl.HPKE.setupBaseR
Hacl.Impl.HPKE.sealBase
Hacl.Impl.HPKE.openBase
```

The result is 15 separate generated modules rather than one runtime-agile HPKE API.
This is a major design point for reimplementers: dispatch is performed by choosing the module/function name, not by passing RFC HPKE suite identifiers to a single function.

---

## 3. Randomness and DRBG

### 3.1 Platform entropy: `Lib_RandomBuffer_System`

Public header `dist/gcc-compatible/Lib_RandomBuffer_System.h`:

```c
extern bool Lib_RandomBuffer_System_randombytes(uint8_t *buf, uint32_t len);

extern void *Lib_RandomBuffer_System_entropy_p;

extern void Lib_RandomBuffer_System_crypto_random(uint8_t *buf, uint32_t len);
```

Observed generated/handwritten C behavior in `Lib_RandomBuffer_System.c`:

- Windows (`_WIN32` or `_WIN64`): uses `CryptAcquireContext` and `CryptGenRandom`, then `CryptReleaseContext`.
- POSIX with `SYS_getrandom`: uses `syscall(SYS_getrandom, buf, len, 0)`.
- POSIX without `SYS_getrandom`: opens `/dev/urandom`, reads, and closes the file descriptor.
- `Lib_RandomBuffer_System_randombytes(buf, len)` returns `true` iff exactly `len` bytes were read.
- `Lib_RandomBuffer_System_crypto_random(buf, len)` loops until `read_random_bytes` succeeds; it has no failure return.
- The documentation marks this file as handwritten and part of the trusted computing base.
- The generated C comments mark `Lib_RandomBuffer_System_randombytes` as deprecated; newer code should prefer the infallible-looping `crypto_random` style only where that blocking behavior is acceptable.

The `Lib_RandomBuffer_System_entropy_p` symbol is declared in the header, but its semantics are unconfirmed from the inspected source.
Treat it as an exposed compatibility artifact unless your build uses a provider that defines it.

### 3.2 HMAC-DRBG public API

Public header: `dist/gcc-compatible/Hacl_HMAC_DRBG.h`.
This is the lower-level HMAC-DRBG API: caller supplies entropy and nonce to instantiate/reseed.

Supported algorithm type:

```c
typedef Spec_Hash_Definitions_hash_alg Hacl_HMAC_DRBG_supported_alg;
```

Supported values documented in the header:

- `Spec_Hash_Definitions_SHA2_256`
- `Spec_Hash_Definitions_SHA2_384`
- `Spec_Hash_Definitions_SHA2_512`
- `Spec_Hash_Definitions_SHA1`

Global limit variables, defined in generated C:

```c
extern uint32_t Hacl_HMAC_DRBG_reseed_interval;
extern uint32_t Hacl_HMAC_DRBG_max_output_length;
extern uint32_t Hacl_HMAC_DRBG_max_length;
extern uint32_t Hacl_HMAC_DRBG_max_personalization_string_length;
extern uint32_t Hacl_HMAC_DRBG_max_additional_input_length;
```

Observed values:

| Variable | Value | Meaning |
|---|---:|---|
| `Hacl_HMAC_DRBG_reseed_interval` | 1024 | Generate calls after which reseed is required by this implementation. |
| `Hacl_HMAC_DRBG_max_output_length` | 65536 | Maximum bytes per generate request. |
| `Hacl_HMAC_DRBG_max_length` | 65536 | Generic maximum length bound. |
| `Hacl_HMAC_DRBG_max_personalization_string_length` | 65536 | Maximum personalization string bytes. |
| `Hacl_HMAC_DRBG_max_additional_input_length` | 65536 | Maximum additional-input bytes. |

These names correspond to NIST SP 800-90A concepts, but the generated code uses the values shown above.

Minimum entropy input length:

```c
uint32_t Hacl_HMAC_DRBG_min_length(Spec_Hash_Definitions_hash_alg a);
```

| Algorithm | `Hacl_HMAC_DRBG_min_length(a)` |
|---|---:|
| SHA1 | 16 |
| SHA2-256 | 32 |
| SHA2-384 | 32 |
| SHA2-512 | 32 |

State type:

```c
typedef struct Hacl_HMAC_DRBG_state_s
{
  uint8_t *k;
  uint8_t *v;
  uint32_t *reseed_counter;
}
Hacl_HMAC_DRBG_state;
```

The low-level state contains heap-allocated buffers for `K`, `V`, and the reseed counter.
Hash-output-sized `k` and `v` buffers are allocated by `Hacl_HMAC_DRBG_create_in`.

Lifecycle prototypes copied from the header:

```c
Hacl_HMAC_DRBG_state Hacl_HMAC_DRBG_create_in(Spec_Hash_Definitions_hash_alg a);

void
Hacl_HMAC_DRBG_instantiate(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state st,
  uint32_t entropy_input_len,
  uint8_t *entropy_input,
  uint32_t nonce_len,
  uint8_t *nonce,
  uint32_t personalization_string_len,
  uint8_t *personalization_string
);

void
Hacl_HMAC_DRBG_reseed(
  Spec_Hash_Definitions_hash_alg a,
  Hacl_HMAC_DRBG_state st,
  uint32_t entropy_input_len,
  uint8_t *entropy_input,
  uint32_t additional_input_input_len,
  uint8_t *additional_input_input
);

bool
Hacl_HMAC_DRBG_generate(
  Spec_Hash_Definitions_hash_alg a,
  uint8_t *output,
  Hacl_HMAC_DRBG_state st,
  uint32_t n,
  uint32_t additional_input_len,
  uint8_t *additional_input
);

void Hacl_HMAC_DRBG_free(Spec_Hash_Definitions_hash_alg uu___, Hacl_HMAC_DRBG_state s);
```

Return conventions:

- `create_in` returns a struct containing allocated pointers; allocation failure handling is not expressed as a `bool`.
- `instantiate` returns `void`; the caller is responsible for respecting length preconditions.
- `reseed` returns `void`; the caller supplies entropy and additional input.
- `generate` returns `true` on success and `false` if generation is refused, notably when `reseed_counter > reseed_interval`.
- `free` releases state allocations.

Personalization and additional input:

- Personalization string is supplied only to `instantiate`.
- Additional input is supplied to `reseed` and `generate`.
- The public HACL API takes explicit byte lengths for all these optional byte strings.

### 3.3 EverCrypt_DRBG public API

Public header: `dist/gcc-compatible/EverCrypt_DRBG.h`.
Internal type details are visible in `dist/gcc-compatible/internal/EverCrypt_DRBG.h`.
EverCrypt_DRBG wraps HMAC-DRBG and fetches entropy from `Lib_RandomBuffer_System_randombytes` during instantiate/reseed and, when needed, generate.

Supported algorithm type:

```c
typedef Spec_Hash_Definitions_hash_alg EverCrypt_DRBG_supported_alg;
```

Global limit variables mirror HACL HMAC-DRBG:

```c
extern uint32_t EverCrypt_DRBG_reseed_interval;
extern uint32_t EverCrypt_DRBG_max_output_length;
extern uint32_t EverCrypt_DRBG_max_length;
extern uint32_t EverCrypt_DRBG_max_personalization_string_length;
extern uint32_t EverCrypt_DRBG_max_additional_input_length;
```

Observed values:

| Variable | Value |
|---|---:|
| `EverCrypt_DRBG_reseed_interval` | 1024 |
| `EverCrypt_DRBG_max_output_length` | 65536 |
| `EverCrypt_DRBG_max_length` | 65536 |
| `EverCrypt_DRBG_max_personalization_string_length` | 65536 |
| `EverCrypt_DRBG_max_additional_input_length` | 65536 |

Minimum entropy input length:

```c
uint32_t EverCrypt_DRBG_min_length(Spec_Hash_Definitions_hash_alg a);
```

| Algorithm | `EverCrypt_DRBG_min_length(a)` |
|---|---:|
| SHA1 | 16 |
| SHA2-256 | 32 |
| SHA2-384 | 32 |
| SHA2-512 | 32 |

Opaque public state:

```c
typedef struct EverCrypt_DRBG_state_s_s EverCrypt_DRBG_state_s;
```

Internal tag layout from `internal/EverCrypt_DRBG.h`:

```c
#define EverCrypt_DRBG_SHA1_s 0
#define EverCrypt_DRBG_SHA2_256_s 1
#define EverCrypt_DRBG_SHA2_384_s 2
#define EverCrypt_DRBG_SHA2_512_s 3

typedef uint8_t EverCrypt_DRBG_state_s_tags;

typedef struct EverCrypt_DRBG_state_s_s
{
  EverCrypt_DRBG_state_s_tags tag;
  union {
    Hacl_HMAC_DRBG_state case_SHA1_s;
    Hacl_HMAC_DRBG_state case_SHA2_256_s;
    Hacl_HMAC_DRBG_state case_SHA2_384_s;
    Hacl_HMAC_DRBG_state case_SHA2_512_s;
  }
  ;
}
EverCrypt_DRBG_state_s;
```

Lifecycle prototypes copied from the public header:

```c
EverCrypt_DRBG_state_s *EverCrypt_DRBG_create_in(Spec_Hash_Definitions_hash_alg a);

EverCrypt_DRBG_state_s *EverCrypt_DRBG_create(Spec_Hash_Definitions_hash_alg a);

bool
EverCrypt_DRBG_instantiate(
  EverCrypt_DRBG_state_s *st,
  uint8_t *personalization_string,
  uint32_t personalization_string_len
);

bool
EverCrypt_DRBG_reseed(
  EverCrypt_DRBG_state_s *st,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

bool
EverCrypt_DRBG_generate(
  uint8_t *output,
  EverCrypt_DRBG_state_s *st,
  uint32_t n,
  uint8_t *additional_input,
  uint32_t additional_input_len
);

void EverCrypt_DRBG_uninstantiate(EverCrypt_DRBG_state_s *st);
```

Return conventions:

- `create_in` / `create` return a heap pointer to an algorithm-tagged DRBG state.
- `instantiate` returns `true` iff personalization length is allowed and system entropy acquisition succeeds.
- `reseed` returns `true` iff additional-input length is allowed and system entropy acquisition succeeds.
- `generate` returns `true` iff `additional_input_len <= 65536`, `n <= 65536`, entropy acquisition succeeds when an automatic reseed is needed, and HMAC-DRBG generation succeeds.
- `uninstantiate` frees the algorithm-specific HMAC-DRBG state and the outer state pointer.

Entropy and nonce behavior:

- `instantiate` obtains `min_length(a)` bytes of entropy and uses `min_length(a) / 2` bytes of nonce internally.
- `reseed` obtains `min_length(a)` bytes of entropy.
- `generate` may reseed automatically when the underlying reseed counter has exceeded the interval.
- Entropy source failures from `Lib_RandomBuffer_System_randombytes` are propagated as `false` by EverCrypt_DRBG.

### 3.4 Extraction-artifact discriminators (not intended API)

Both DRBG headers additionally export automatically generated *discriminator*
functions for the tagged union underlying the state. They are an artifact of
F\* inductive-type extraction, not a designed API, and should not be relied on:

```c
bool EverCrypt_DRBG_uu___is_SHA1_s(Spec_Hash_Definitions_hash_alg a, EverCrypt_DRBG_state_s projectee);
bool EverCrypt_DRBG_uu___is_SHA2_256_s(Spec_Hash_Definitions_hash_alg a, EverCrypt_DRBG_state_s projectee);
bool EverCrypt_DRBG_uu___is_SHA2_384_s(Spec_Hash_Definitions_hash_alg a, EverCrypt_DRBG_state_s projectee);
bool EverCrypt_DRBG_uu___is_SHA2_512_s(Spec_Hash_Definitions_hash_alg a, EverCrypt_DRBG_state_s projectee);
bool Hacl_HMAC_DRBG_uu___is_State(Spec_Hash_Definitions_hash_alg a, Hacl_HMAC_DRBG_state projectee);
```

Note that each takes the state **by value**, even though the state is otherwise
manipulated exclusively through pointers. `EverCrypt_AEAD_uu___is_Ek` in
`EverCrypt_AEAD.h` is the same kind of artifact. A reimplementation should
simply omit these.

---

## 4. CPU feature detection and runtime dispatch

### 4.1 Public AutoConfig2 API

Public header: `dist/gcc-compatible/EverCrypt_AutoConfig2.h`.

Feature-query functions:

```c
bool EverCrypt_AutoConfig2_has_shaext(void);
bool EverCrypt_AutoConfig2_has_aesni(void);
bool EverCrypt_AutoConfig2_has_pclmulqdq(void);
bool EverCrypt_AutoConfig2_has_avx2(void);
bool EverCrypt_AutoConfig2_has_avx(void);
bool EverCrypt_AutoConfig2_has_bmi2(void);
bool EverCrypt_AutoConfig2_has_adx(void);
bool EverCrypt_AutoConfig2_has_sse(void);
bool EverCrypt_AutoConfig2_has_movbe(void);
bool EverCrypt_AutoConfig2_has_rdrand(void);
bool EverCrypt_AutoConfig2_has_avx512(void);
bool EverCrypt_AutoConfig2_has_vec128(void);
bool EverCrypt_AutoConfig2_has_vec256(void);
```

Initialization and recall:

```c
void EverCrypt_AutoConfig2_recall(void);

void EverCrypt_AutoConfig2_init(void);
```

Disable override type and functions:

```c
typedef void (*EverCrypt_AutoConfig2_disabler)(void);

void EverCrypt_AutoConfig2_disable_avx2(void);
void EverCrypt_AutoConfig2_disable_avx(void);
void EverCrypt_AutoConfig2_disable_bmi2(void);
void EverCrypt_AutoConfig2_disable_adx(void);
void EverCrypt_AutoConfig2_disable_shaext(void);
void EverCrypt_AutoConfig2_disable_aesni(void);
void EverCrypt_AutoConfig2_disable_pclmulqdq(void);
void EverCrypt_AutoConfig2_disable_sse(void);
void EverCrypt_AutoConfig2_disable_movbe(void);
void EverCrypt_AutoConfig2_disable_rdrand(void);
void EverCrypt_AutoConfig2_disable_avx512(void);
```

### 4.2 Observed implementation model

`EverCrypt_AutoConfig2.c` stores one `static bool cpu_has_*[1]` flag per feature.
Before `init`, all flags are initialized to `false`.
`EverCrypt_AutoConfig2_init()` calls Vale CPUID helper functions only when `HACL_CAN_COMPILE_VALE` is true:

- `check_aesni()` sets both `aesni` and `pclmulqdq` true.
- `check_sha()` sets `shaext` true.
- `check_adx_bmi2()` sets both `bmi2` and `adx` true.
- `check_avx()` is accepted only if OSXSAVE and XCR0 checks pass.
- `check_avx2()` is accepted only if OSXSAVE and XCR0 checks pass.
- `check_sse()` sets `sse` true.
- `check_movbe()` sets `movbe` true.
- `check_rdrand()` sets `rdrand` true.
- `check_avx512()` is accepted only if OSXSAVE, AVX XCR0, and AVX512 XCR0 checks pass.

`has_vec128()` returns `has_avx() || has_vec128_not_avx()`.
`has_vec256()` returns `has_avx2() || has_vec256_not_avx2()`.
The `*_not_avx*` helpers are compile-time/architecture predicates from `evercrypt_targetconfig.h`, primarily for non-x64 platforms where vector support is treated as available if the code was compiled for it.

The `disable_*` functions simply set the corresponding stored feature flag to `false`.
They are useful to force fallback paths or avoid a feature after detection.
Calling `init()` after a `disable_*` call may re-enable a feature if CPUID still reports it, because `init()` writes true flags and does not remember disables as permanent policy.

### 4.3 Requirement to call `init()`

The official documentation states that clients should call `EverCrypt_AutoConfig2_init()` to detect the target CPU before using EverCrypt multiplexed APIs.
If clients fail to do this, EverCrypt APIs always see false feature flags and choose slow/fallback implementations.

For a reimplementation:

- Separate compile-time availability from runtime CPU/OS availability.
- Runtime dispatch should only select optimized code if both the code was compiled in and runtime detection says it is safe to execute.
- Expose explicit disable hooks if API compatibility matters.
- Make initialization idempotent.

### 4.4 Thread-safety and idempotence

The generated implementation uses unsynchronized writes to static booleans.
Repeated `init()` calls are idempotent in effect when no `disable_*` calls are interleaved: detected features are set to `true`, already-false unavailable features remain false.
Concurrent `init()` calls write the same booleans, but there is no explicit locking or C11 atomic synchronization in the inspected source.
Concurrent `disable_*` racing with `init()` is policy-ambiguous and should be avoided by clients.

A safer reimplementation should prefer one-time initialization primitives or atomics, while preserving the visible behavior that feature queries are cheap and return cached booleans.

### 4.5 `evercrypt_targetconfig.h` compile-time flags

`dist/gcc-compatible/evercrypt_targetconfig.h` defines architecture ids:

```c
#define TARGET_ARCHITECTURE_ID_UNKNOWN 0
#define TARGET_ARCHITECTURE_ID_X86 1
#define TARGET_ARCHITECTURE_ID_X64 2
#define TARGET_ARCHITECTURE_ID_ARM7 3
#define TARGET_ARCHITECTURE_ID_ARM8 4
#define TARGET_ARCHITECTURE_ID_SYSTEMZ 5
#define TARGET_ARCHITECTURE_ID_POWERPC64 6
```

If a `config.h` is available, it is included.
Otherwise `TARGET_ARCHITECTURE` defaults to `TARGET_ARCHITECTURE_ID_UNKNOWN`.

Vector compile-time predicates used here:

```c
static inline bool has_vec128_not_avx () {
#if (TARGET_ARCHITECTURE != TARGET_ARCHITECTURE_ID_X64) && HACL_CAN_COMPILE_VEC128
  return true;
#else
  return false;
#endif
}

static inline bool has_vec256_not_avx2 () {
#if (TARGET_ARCHITECTURE != TARGET_ARCHITECTURE_ID_X64) && HACL_CAN_COMPILE_VEC256
  return true;
#else
  return false;
#endif
}
```

`HACL_CAN_COMPILE_VALE` controls whether the Vale CPUID checks and Vale assembly-backed feature detection code are compiled in at all.
If it is false or undefined in the effective build configuration, `EverCrypt_AutoConfig2_init()` does not set any x86 feature flags from CPUID in the inspected generated C.
`HACL_CAN_COMPILE_VEC128` and `HACL_CAN_COMPILE_VEC256` control whether vector intrinsic types and operations are available in the public support headers.

---

## 5. Support headers and public-surface leakage

These headers are mostly implementation support.
They are nevertheless in `dist/gcc-compatible/` and can leak into consumers because generated public headers include runtime support types, endian helpers, target macros, and shared enums.

### 5.1 `Hacl_Krmllib.h`: KaRaMeL runtime helpers

Public declarations observed:

```c
static KRML_NOINLINE uint64_t FStar_UInt64_eq_mask(uint64_t a, uint64_t b);

static KRML_NOINLINE uint64_t FStar_UInt64_gte_mask(uint64_t a, uint64_t b);

static inline FStar_UInt128_uint128
FStar_UInt128_add_mod(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

static inline FStar_UInt128_uint128
FStar_UInt128_sub_mod(FStar_UInt128_uint128 a, FStar_UInt128_uint128 b);

static inline FStar_UInt128_uint128
FStar_UInt128_shift_right(FStar_UInt128_uint128 a, uint32_t s);

static inline FStar_UInt128_uint128 FStar_UInt128_uint64_to_uint128(uint64_t a);

static inline uint64_t FStar_UInt128_uint128_to_uint64(FStar_UInt128_uint128 a);
```

Purpose: support extracted KaRaMeL code, especially constant-time masks and portable/extracted 128-bit arithmetic wrappers.
These functions are implementation-support API, not cryptographic primitives intended for direct application use.
A reimplementation should hide this layer if the target language can express masks and wide arithmetic directly.

### 5.2 `lib_memzero0.h`: secret erasure

Header content:

```c
#include <inttypes.h>

void Lib_Memzero0_memzero0(void *dst, uint64_t len);

#define Lib_Memzero0_memzero(dst, len, t, _ret_t) Lib_Memzero0_memzero0(dst, len * sizeof(t))
```

Purpose: explicit erasure of secret buffers.
Generated code uses it for Frodo intermediate matrices, keys, and random coins.
This is implementation support, but the behavior is security-critical.
A reimplementation should map it to a guaranteed-not-optimized-away memory clearing primitive in the target runtime.

### 5.3 `libintvector.h` and `libintvector-shim.h`: SIMD abstraction

`libintvector.h` is a plain C preprocessor and intrinsic abstraction layer.
It is selected by architecture and compile-time macros, not by generated code at runtime.

Observed architecture branches:

- x86/x86_64: `__x86_64__`, `_M_X64`, `__i386__`, or `_M_IX86`.
- ARM/AArch64: `__aarch64__`, `_M_ARM64`, `__arm__`, or `_M_ARM`, excluding `__ARM_32BIT_STATE`.
- IBM Z: `__s390x__`.
- PowerPC64: `__powerpc64__`.

Observed compile-time gates:

- `HACL_CAN_COMPILE_VEC128` enables 128-bit vector types and operations.
- `HACL_CAN_COMPILE_VEC256` enables 256-bit vector types and operations where supported.
- On x86 with vec128, the type is `typedef __m128i Lib_IntVector_Intrinsics_vec128;`.
- On x86 with vec256, the type is `typedef __m256i Lib_IntVector_Intrinsics_vec256;`.
- The header maps operations to SSE/SSSE3/SSE4.1/AES-NI/PCLMUL and AVX/AVX2 intrinsics on x86, and to corresponding vector intrinsics on ARM, s390x, and PowerPC64 branches.

Examples of operations exposed as macros:

- Loads/stores in little-endian and big-endian forms.
- XOR, OR, AND, NOT.
- Equality and greater-than comparisons for 32-bit and 64-bit lanes.
- Shifts and rotations.
- Lane shuffles and interleaves.
- 32-bit and 64-bit vector addition, subtraction, and multiplication.
- AES-NI encryption/keygen assist and carry-less multiply macros where available.

`libintvector-shim.h` intentionally defines incomplete struct types:

```c
typedef struct __vec128 Lib_IntVector_Intrinsics_vec128;
typedef struct __vec256 Lib_IntVector_Intrinsics_vec256;
```

The shim exists because some modules need vector types in state definitions without compiling the including translation unit with vector flags such as `-mavx`.
The incomplete types prevent construction and enforce that actual vector operations remain in optimized modules that include the real `libintvector.h`.

For reimplementers: this SIMD layer is plain C headers with intrinsics, not generated Low* code.
Port it as a target-language backend abstraction, not as part of the cryptographic algorithm spec.

### 5.4 `lib_intrinsics.h`: scalar arithmetic intrinsics

`lib_intrinsics.h` selects between portable HACL integer helpers and compiler intrinsics.
It includes `config.h` when present and then uses `HACL_CAN_COMPILE_INTRINSICS` and `HACL_CAN_COMPILE_UINT128`.

Public macro names exposed:

```c
Lib_IntTypes_Intrinsics_add_carry_u32(cin, x, y, r)
Lib_IntTypes_Intrinsics_add_carry_u64(cin, x, y, r)
Lib_IntTypes_Intrinsics_sub_borrow_u32(cin, x, y, r)
Lib_IntTypes_Intrinsics_sub_borrow_u64(cin, x, y, r)
```

When compiler intrinsics are enabled on x86, these map to `_addcarry_u32`, `_addcarry_u64`, `_subborrow_u32`, and `_subborrow_u64` from `<x86intrin.h>` or `<immintrin.h>`.
The header contains workarounds for known old GCC/Clang intrinsic bugs.
When intrinsics are not available, it maps to generated helper headers such as `Hacl_IntTypes_Intrinsics.h` and, if available, `Hacl_IntTypes_Intrinsics_128.h`.

The requested `mul64x64` concept is not exposed by that exact macro name in `lib_intrinsics.h`; multiplication support appears in related vector macros and bignum/curve code.
For this header, the confirmed public scalar operations are add-with-carry and subtract-with-borrow.

### 5.5 `Hacl_Spec.h`: shared enums

Public enum-like macros in `Hacl_Spec.h`:

```c
#define Spec_FFDHE_FFDHE2048 0
#define Spec_FFDHE_FFDHE3072 1
#define Spec_FFDHE_FFDHE4096 2
#define Spec_FFDHE_FFDHE6144 3
#define Spec_FFDHE_FFDHE8192 4

typedef uint8_t Spec_FFDHE_ffdhe_alg;

#define Spec_Agile_AEAD_AES128_GCM 0
#define Spec_Agile_AEAD_AES256_GCM 1
#define Spec_Agile_AEAD_CHACHA20_POLY1305 2
#define Spec_Agile_AEAD_AES128_CCM 3
#define Spec_Agile_AEAD_AES256_CCM 4
#define Spec_Agile_AEAD_AES128_CCM8 5
#define Spec_Agile_AEAD_AES256_CCM8 6

typedef uint8_t Spec_Agile_AEAD_alg;
```

DRBG hash algorithm identifiers are in `Hacl_Streaming_Types.h`, which is included by the DRBG headers:

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

These are shared generated ABI constants.
They are public in C, but most application users should see higher-level algorithm choices rather than these raw tags.

### 5.6 `Lib_PrintBuffer.h` and `TestLib.h`: test-only/support

`Lib_PrintBuffer.h` exposes debugging/test output helpers:

```c
extern void Lib_PrintBuffer_print_bytes(uint32_t len, uint8_t *buf);

extern void Lib_PrintBuffer_print_compare(uint32_t len, uint8_t *buf0, uint8_t *buf1);

extern void
Lib_PrintBuffer_print_compare_display(uint32_t len, const uint8_t *buf0, const uint8_t *buf1);

extern bool
Lib_PrintBuffer_result_compare_display(uint32_t len, const uint8_t *buf0, const uint8_t *buf1);
```

`TestLib.h` exposes test assertions, unsafe allocation, null-pointer compatibility globals, CPU cycle helpers, and comparison/printing functions.
Examples include:

```c
extern void TestLib_check(bool uu___);
extern void TestLib_checku32(uint32_t uu___, uint32_t uu___1);
extern void TestLib_compare_and_print(Prims_string uu___, uint8_t *b1, uint8_t *b2, uint32_t l);
extern uint8_t *TestLib_unsafe_malloc(uint32_t l);
extern TestLib_cycles TestLib_cpucycles(void);
```

Treat both headers as test/support-only, not stable cryptographic API.
Do not model them as part of a clean reimplementation surface unless test compatibility is required.

---

## 6. Notes for reimplementers

### 6.1 Non-obvious API choices

- FrodoKEM parameter selection is by C module name, not by runtime enum.
- `Frodo64` is present but is toy/test-only.
- Frodo functions return `0` unconditionally in the observed generated C; entropy failure from `randombytes_` is discarded.
- HPKE is monomorphized into 15 generated modules instead of exposing one runtime-agile API.
- HPKE `CP32`, `CP128`, and `CP256` name implementation backends for ChaCha20-Poly1305, not different RFC AEAD ids.
- HPKE Base mode is the only public HPKE mode exported here; PSK/Auth/AuthPSK are spec concepts but not shipped public APIs in these headers.
- HPKE context state is caller-allocated through a struct of pointers, not an opaque allocation returned by the library.
- HPKE P-256 uses 64-byte serialized recipient public keys but 65-byte encapsulated public keys in this generated API.
- HPKE sequence state is a `uint64_t`, even though RFC HPKE defines nonce/counter space over 96 bits.
- HMAC-DRBG state is heap-backed but returned as a small struct of pointers; EverCrypt_DRBG wraps it in a heap-allocated, algorithm-tagged union.
- EverCrypt_DRBG obtains entropy itself through `Lib_RandomBuffer_System_randombytes`; Hacl_HMAC_DRBG expects caller-supplied entropy.
- `Lib_RandomBuffer_System` is a handwritten trusted shim over OS randomness APIs.
- AutoConfig2 is cached CPU detection plus runtime dispatch, guarded by compile-time macros such as `HACL_CAN_COMPILE_VALE`, `HACL_CAN_COMPILE_VEC128`, and `HACL_CAN_COMPILE_VEC256`.
- AutoConfig2 feature flags are plain static booleans, not atomics; initialize before concurrent use.
- The SIMD layer is ordinary C headers and intrinsics selected by preprocessor macros, not generated F*/Low* code.
- KaRaMeL runtime helpers leak into the public include surface because generated C uses shared runtime definitions for masks, uint128, allocation, target checks, and endian operations.

### 6.2 Suggested clean target-language shape

For a non-C reimplementation, consider preserving wire/API compatibility while using more idiomatic internals:

- Represent Frodo parameter sets with a sealed enum or type-level parameter, but keep exact byte-size constants and module aliases for compatibility.
- Return explicit entropy/system errors in new APIs, while offering C-compatible wrappers that mimic `0`/`1` or boolean behavior.
- Model HPKE variants as a generated or type-specialized family, because the original is monomorphized and optimized per suite.
- Keep Base-mode HPKE separate from future PSK/Auth additions so consumers do not assume unsupported modes exist.
- Make DRBG states opaque and ensure uninstantiate/free zeroizes key material before releasing memory.
- Centralize OS randomness in a small reviewed trusted module.
- Use a clear two-stage CPU policy: compile-time capability determines what code exists; runtime detection determines what code may run.
- Replace C macro-heavy SIMD with target-language traits/interfaces or backend modules, but preserve constant-time behavior and feature gating.

### 6.3 Compatibility checklist

- [ ] Frodo sizes match the table in section 1.2 exactly.
- [ ] Frodo public return behavior is intentionally chosen: exact C-compatible always-`0`, or safer documented deviation.
- [ ] Frodo randomness uses cryptographically secure OS entropy or a reviewed DRBG source.
- [ ] HPKE variant list matches all 15 shipped headers.
- [ ] HPKE `o_enc`/`enc` sizes distinguish X25519 32 bytes from P-256 65 bytes.
- [ ] HPKE P-256 recipient public key input remains 64 bytes where the C API expects serialized input.
- [ ] HPKE ciphertext length includes the 16-byte tag.
- [ ] HPKE Base-only support is documented.
- [ ] HMAC-DRBG and EverCrypt_DRBG limits are 1024 reseed interval and 65536-byte maximum lengths where API compatibility is required.
- [ ] DRBG SHA1/SHA2-256/SHA2-384/SHA2-512 tags match public hash identifiers.
- [ ] AutoConfig2 `init()` or equivalent is called before multiplexed optimized code dispatch.
- [ ] Disable hooks cannot race with dispatch in a way that violates memory safety or CPU-feature safety.
- [ ] Secret erasure is guaranteed by the target compiler/runtime.
- [ ] Test-only headers are not exposed as production cryptographic APIs.

---

## 7. Source index

- `dist/gcc-compatible/Hacl_Frodo64.h`
- `dist/gcc-compatible/Hacl_Frodo640.h`
- `dist/gcc-compatible/Hacl_Frodo976.h`
- `dist/gcc-compatible/Hacl_Frodo1344.h`
- `dist/gcc-compatible/internal/Hacl_Frodo_KEM.h`
- `dist/gcc-compatible/Hacl_Frodo_KEM.c`
- `dist/gcc-compatible/Hacl_HPKE_Curve51_CP32_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve51_CP32_SHA512.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve51_CP128_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve51_CP128_SHA512.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve51_CP256_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve51_CP256_SHA512.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve64_CP32_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve64_CP32_SHA512.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve64_CP128_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve64_CP128_SHA512.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve64_CP256_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_Curve64_CP256_SHA512.h`
- `dist/gcc-compatible/Hacl_HPKE_P256_CP32_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_P256_CP128_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_P256_CP256_SHA256.h`
- `dist/gcc-compatible/Hacl_HPKE_Interface_Hacl_Impl_HPKE_Hacl_Meta_HPKE.h`
- `dist/gcc-compatible/Hacl_HMAC_DRBG.h`
- `dist/gcc-compatible/EverCrypt_DRBG.h`
- `dist/gcc-compatible/internal/EverCrypt_DRBG.h`
- `dist/gcc-compatible/Lib_RandomBuffer_System.h`
- `dist/gcc-compatible/Lib_RandomBuffer_System.c`
- `dist/gcc-compatible/EverCrypt_AutoConfig2.h`
- `dist/gcc-compatible/EverCrypt_AutoConfig2.c`
- `dist/gcc-compatible/evercrypt_targetconfig.h`
- `dist/gcc-compatible/Hacl_Krmllib.h`
- `dist/gcc-compatible/lib_memzero0.h`
- `dist/gcc-compatible/libintvector.h`
- `dist/gcc-compatible/libintvector-shim.h`
- `dist/gcc-compatible/lib_intrinsics.h`
- `dist/gcc-compatible/Hacl_Spec.h`
- `dist/gcc-compatible/Hacl_Streaming_Types.h`
- `dist/gcc-compatible/Lib_PrintBuffer.h`
- `dist/gcc-compatible/TestLib.h`
- `code/frodo/`
- `code/hpke/`
- `code/drbg/`
- `code/hpke/Hacl.Meta.HPKE.fst`
- `providers/evercrypt/EverCrypt.DRBG.fsti`
- `providers/evercrypt/EverCrypt.AutoConfig2.fsti`
- `providers/evercrypt/EverCrypt.TargetConfig.fsti`
- `lib/c/Lib_RandomBuffer_System.c`
- `doc/Randomness.rst`
- `doc/EverCryptDRBG.rst`
- `doc/EverCryptAutoConfig.rst`
