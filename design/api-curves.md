# Elliptic-curve APIs: Curve25519, Ed25519, P-256, K-256
This document inventories the generated public C APIs for elliptic-curve
operations in `dist/gcc-compatible/` and records the behavioral contract a
reimplementation should preserve. Read it with [README.md](README.md),
[conventions.md](conventions.md), [api-bignum.md](api-bignum.md),
[implementation.md](implementation.md), and [surprises.md](surprises.md).
Primary headers covered:
- `Hacl_Curve25519_51.h`
- `Hacl_Curve25519_64.h`
- `EverCrypt_Curve25519.h`
- `Hacl_Ed25519.h`
- `EverCrypt_Ed25519.h`
- `Hacl_EC_Ed25519.h`
- `Hacl_P256.h`
- `Hacl_K256_ECDSA.h`
- `Hacl_EC_K256.h`
Internal headers read only for context: `internal/Hacl_P256.h`,
`internal/Hacl_K256_ECDSA.h`, `internal/Hacl_Ed25519.h`,
`internal/Hacl_Bignum25519_51.h`, and the generated `*_PrecompTable.h` files.
They expose implementation details and are not treated as the public inventory.
## 1. Supported curves and implementation families
| Curve | Main use in this API set | Public headers | Encoding convention | Implementation status |
| --- | --- | --- | --- | --- |
| Curve25519 / X25519 Montgomery curve | ECDH (`secret_to_public`, `scalarmult`, `ecdh`) | `Hacl_Curve25519_51.h`, `Hacl_Curve25519_64.h`, `EverCrypt_Curve25519.h` | 32-byte little-endian u-coordinate/scalar strings, RFC 7748-style scalar clamping semantics | Two named implementations: `_51` portable C radix-2^51, and `_64` radix-2^64 using 128-bit arithmetic / Vale or GCC inline assembly. `EverCrypt_Curve25519` multiplexes at runtime to `_64` when Vale is compiled and BMI2+ADX are present, otherwise `_51`. |
| Edwards25519 / Ed25519 | EdDSA signatures and low-level Edwards arithmetic | `Hacl_Ed25519.h`, `EverCrypt_Ed25519.h`, `Hacl_EC_Ed25519.h` | 32-byte little-endian compressed points and scalars; 64-byte signatures `R || S` with both halves little-endian Ed25519 encodings | Portable C in `Hacl_Ed25519`; `EverCrypt_Ed25519` is only a thin forwarding layer in the current sources, despite its name saying “EverCrypt”. Low-level `Hacl_EC_Ed25519` exposes radix-2^51 limbs. |
| NIST P-256 / secp256r1 | ECDSA, ECDH, key validation, point encoding conversion | `Hacl_P256.h` | Big-endian 32-byte integers; raw public key is `x || y` (64 bytes); uncompressed `0x04 || x || y` (65 bytes); compressed `0x02/0x03 || x` (33 bytes) | Portable generated C public API. No EverCrypt multiplexed P-256 front-end in the covered headers. |
| secp256k1 / K-256 | ECDSA, low-S variants, ECDH, key validation, point conversion, low-level EC arithmetic | `Hacl_K256_ECDSA.h`, `Hacl_EC_K256.h` | Big-endian 32-byte integers; raw public key is `x || y` (64 bytes); uncompressed/compressed SEC1 encodings as above | Portable generated C public API. No EverCrypt multiplexed K-256 front-end in the covered headers. Low-level `Hacl_EC_K256` exposes radix-2^52 limbs. |
Important cross-family convention: all 25519 byte encodings in these APIs are
little-endian; P-256 and K-256 byte encodings are big-endian. This was confirmed
in the F* sources by uses of `nat_from_bytes_le`/`nat_to_bytes_le` for
Curve25519 and Ed25519, and `nat_from_bytes_be`/`nat_to_bytes_be` for P-256 and
K-256.
## 2. Global buffer and return-value conventions
- Buffer sizes in the headers are implicit C contracts; callers must provide at
  least the stated byte/limb lengths.
- Null pointers are not accepted by the verified Low* model. Treat every pointer
  parameter as non-null and live for the full access range.
- When comments say buffers must be disjoint or either disjoint/equal, preserve
  those aliasing preconditions. Functions not explicitly documenting an overlap
  allowance should be treated as requiring the generated F* preconditions.
- Public keys in raw Weierstrass APIs are `x || y`, with each coordinate encoded
  as a fixed 32-byte big-endian integer.
- ECDSA signatures are fixed 64 bytes `R || S`, each 32-byte big-endian for
  P-256/K-256. P-256 verification takes `R` and `S` as separate 32-byte buffers;
  K-256 verification takes the combined 64-byte signature.
- `bool` return values never report allocation failure. They report validation or
  cryptographic success/failure as described for each function.
- If a `bool`-returning function returns `false`, do not rely on any newly
  written output except where specifically stated by the source. Some
  implementations compute into buffers before returning the validation flag.
## 3. Curve25519 / X25519 APIs
### 3.1 Common Curve25519 semantics
- All inputs and outputs are exactly 32 bytes.
- Scalars and u-coordinates are little-endian byte strings.
- The scalar multiplication semantics match RFC 7748: the effective scalar has
  the low three bits cleared, bit 255 cleared, and bit 254 set. In the HACL*
  spec this is implemented by fixed ladder bit handling rather than by requiring
  a caller-supplied already-clamped scalar.
- `scalarmult` writes the raw X25519 result and does not return a validation
  flag. It accepts any 32-byte scalar and any 32-byte encoded u-coordinate;
  the input point is decoded as `nat_from_bytes_le(pub) mod 2^255 mod p`.
- `secret_to_public` is scalar multiplication by the base point `09 00 ... 00`.
- `ecdh` performs the same scalar multiplication as `scalarmult`, then compares
  the 32-byte shared secret with all zeroes. It returns `false` exactly when the
  shared secret is all zero; otherwise it returns `true`. This is the API's
  low-order-point handling: low-order peer inputs that lead to an all-zero
  shared secret are rejected by `ecdh`, but not by `scalarmult`.
### 3.2 `Hacl_Curve25519_51.h`
Portable C implementation using five 64-bit limbs in radix 2^51 internally.
The public API does not expose these limbs.
#### `Hacl_Curve25519_51_scalarmult`
```c
void Hacl_Curve25519_51_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub);
```
- Semantics: compute X25519 scalar multiplication `[priv]pub`.
- Buffers: `out[32]`, `priv[32]`, `pub[32]`.
- Encoding: little-endian scalar and u-coordinate; output little-endian
  u-coordinate.
- Validation: no public-key validation flag; all 32-byte inputs are accepted at
  the API level.
- Return: none.
- Preconditions: pointers valid for their ranges. Treat `out` as distinct from
  input buffers unless a reimplementation deliberately supports overlap.
#### `Hacl_Curve25519_51_secret_to_public`
```c
void Hacl_Curve25519_51_secret_to_public(uint8_t *pub, uint8_t *priv);
```
- Semantics: compute `[priv]G`, where `G` is the X25519 base point.
- Buffers: `pub[32]`, `priv[32]`.
- Encoding: little-endian input scalar; little-endian public u-coordinate.
- Validation: no private-key validation; any 32-byte secret is accepted and
  clamped by the X25519 scalar semantics.
- Return: none.
- Preconditions: `pub` and `priv` valid; source F* requires disjoint output and
  input for equivalent EverCrypt functions.
#### `Hacl_Curve25519_51_ecdh`
```c
bool Hacl_Curve25519_51_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub);
```
- Semantics: compute X25519 shared secret `[priv]pub`.
- Buffers: `out[32]`, `priv[32]`, `pub[32]`.
- Encoding: little-endian scalar/u-coordinate; output little-endian u-coordinate.
- Validation: detects only the all-zero result. It does not otherwise validate
  that `pub` is a canonical field element or prime-order point.
- Return: `true` iff `out` is not 32 zero bytes; `false` iff the computed shared
  secret is all zero.
- Preconditions: pointers valid; output not overlapping inputs in the F* API
  shape.
### 3.3 `Hacl_Curve25519_64.h`
Radix-2^64 Curve25519 implementation. The distribution notes and sibling docs
identify this as requiring 128-bit arithmetic or, in the GCC-compatible build,
Vale/GCC inline assembly in `curve25519-inline.h`, gated by CPU support
(BMI2+ADX) when selected through EverCrypt.
#### `Hacl_Curve25519_64_scalarmult`
```c
void Hacl_Curve25519_64_scalarmult(uint8_t *out, uint8_t *priv, uint8_t *pub);
```
- Semantics, buffers, encoding, validation, return, and preconditions are the
  same as `Hacl_Curve25519_51_scalarmult`.
- Additional implementation precondition: callers that bypass EverCrypt must not
  call an assembly-specialized build on a CPU lacking the required instruction
  set. Use EverCrypt if runtime dispatch is desired.
#### `Hacl_Curve25519_64_secret_to_public`
```c
void Hacl_Curve25519_64_secret_to_public(uint8_t *pub, uint8_t *priv);
```
- Semantics: compute `[priv]G`.
- Buffers: `pub[32]`, `priv[32]`.
- Encoding: little-endian.
- Validation: no private-key validation beyond X25519 scalar clamping semantics.
- Return: none.
- Preconditions: valid buffers; observe CPU/assembly requirements if not using
  EverCrypt.
#### `Hacl_Curve25519_64_ecdh`
```c
bool Hacl_Curve25519_64_ecdh(uint8_t *out, uint8_t *priv, uint8_t *pub);
```
- Semantics: compute X25519 shared secret.
- Buffers: `out[32]`, `priv[32]`, `pub[32]`.
- Encoding: little-endian.
- Validation: rejects exactly the all-zero shared secret.
- Return: `true` iff `out` is nonzero; `false` iff all zero.
- Preconditions: valid buffers; observe CPU/assembly requirements if not using
  EverCrypt.
### 3.4 `EverCrypt_Curve25519.h`
Multiplexed front-end. The F* implementation checks `hacl_can_compile_vale`,
then `EverCrypt_AutoConfig2.has_bmi2()` and `.has_adx()`. If both CPU features
are available, it calls `Hacl_Curve25519_64`; otherwise it calls
`Hacl_Curve25519_51`. If Vale is not compiled, it always calls `_51`.
#### `EverCrypt_Curve25519_secret_to_public`
```c
void EverCrypt_Curve25519_secret_to_public(uint8_t *pub, uint8_t *priv);
```
- Semantics: multiplexed X25519 base-point multiplication.
- Buffers: `pub[32]`, `priv[32]`.
- Encoding: little-endian.
- Validation: no private-key validation beyond X25519 scalar semantics.
- Return: none.
- Preconditions: valid, disjoint `pub` and `priv` in the F* signature; callers
  should initialize EverCrypt CPU configuration as described in
  [conventions.md](conventions.md) if relying on runtime feature detection.
#### `EverCrypt_Curve25519_scalarmult`
```c
void EverCrypt_Curve25519_scalarmult(uint8_t *shared, uint8_t *my_priv, uint8_t *their_pub);
```
- Semantics: multiplexed X25519 scalar multiplication.
- Buffers: `shared[32]`, `my_priv[32]`, `their_pub[32]`.
- Encoding: little-endian.
- Validation: no boolean validation; all inputs accepted at API level.
- Return: none.
- Preconditions: `shared` valid and disjoint from both inputs in the F* signature.
#### `EverCrypt_Curve25519_ecdh`
```c
bool EverCrypt_Curve25519_ecdh(uint8_t *shared, uint8_t *my_priv, uint8_t *their_pub);
```
- Semantics: multiplexed X25519 ECDH.
- Buffers: `shared[32]`, `my_priv[32]`, `their_pub[32]`.
- Encoding: little-endian.
- Validation: rejects exactly the all-zero shared secret.
- Return: `true` iff `shared` is not all zero; `false` iff all zero.
- Preconditions: `shared` valid and disjoint from both inputs in the F* signature.
## 4. Ed25519 signature APIs
### 4.1 Common Ed25519 semantics
- Private keys are 32-byte seeds. Any 32-byte seed is accepted.
- Public keys are 32-byte compressed Edwards25519 points.
- Signatures are 64 bytes `R || S`: `R` is a 32-byte compressed point and `S` is
  a 32-byte little-endian scalar modulo the Ed25519 group order.
- Expanded keys are 96 bytes laid out as `public_key[32] || s[32] || prefix[32]`,
  as specified in `EverCrypt.Ed25519.fsti` and `Spec.Ed25519.expand_keys`.
- `secret_to_public` and signing internally SHA-512-hash the seed and clamp the
  lower half (`h_low[0] &= 0xf8`, `h_low[31] &= 127`, `h_low[31] |= 64`).
- Verification validates by decompression of the public key and `R`, rejects
  `S >= q`, and checks the Ed25519 equation. It returns only a boolean.
- The source does not expose Ed25519ph/ctx variants in these headers.
### 4.2 `Hacl_Ed25519.h`
#### `Hacl_Ed25519_secret_to_public`
```c
void Hacl_Ed25519_secret_to_public(uint8_t *public_key, uint8_t *private_key);
```
- Semantics: derive Ed25519 public key from a 32-byte private seed.
- Buffers: `public_key[32]`, `private_key[32]`.
- Encoding: output is little-endian Edwards compressed point.
- Validation: no private-key validation; every 32-byte seed is accepted.
- Return: none.
- Preconditions: header says `public_key` must not overlap `private_key`.
#### `Hacl_Ed25519_expand_keys`
```c
void Hacl_Ed25519_expand_keys(uint8_t *expanded_keys, uint8_t *private_key);
```
- Semantics: precompute expanded signing material for repeated signing.
- Buffers: `expanded_keys[96]`, `private_key[32]`.
- Encoding/layout: `expanded_keys[0..31]` public key, `expanded_keys[32..63]`
  clamped scalar `s`, `expanded_keys[64..95]` SHA-512 prefix; all Ed25519
  32-byte scalar/point strings are little-endian/compressed as appropriate.
- Validation: no private-key validation.
- Return: none.
- Preconditions: header says output must not overlap `private_key`.
#### `Hacl_Ed25519_sign_expanded`
```c
void
Hacl_Ed25519_sign_expanded(
  uint8_t *signature,
  uint8_t *expanded_keys,
  uint32_t msg_len,
  uint8_t *msg
);
```
- Semantics: sign `msg` using expanded key material obtained from
  `Hacl_Ed25519_expand_keys`.
- Buffers: `signature[64]`, `expanded_keys[96]`, `msg[msg_len]`.
- Encoding: signature is `R[32] || S[32]`, little-endian Ed25519 encodings.
- Validation: does not validate that `expanded_keys` was produced by the expand
  function; caller must supply a well-formed expanded key buffer.
- Return: none.
- Preconditions: header says `signature` must not overlap `expanded_keys` or
  `msg`.
#### `Hacl_Ed25519_sign`
```c
void
Hacl_Ed25519_sign(uint8_t *signature, uint8_t *private_key, uint32_t msg_len, uint8_t *msg);
```
- Semantics: expand the private seed and sign `msg`.
- Buffers: `signature[64]`, `private_key[32]`, `msg[msg_len]`.
- Encoding: signature is `R || S`, 64 bytes.
- Validation: no private-key validation.
- Return: none.
- Preconditions: header says `signature` must not overlap `private_key` or `msg`.
#### `Hacl_Ed25519_verify`
```c
bool
Hacl_Ed25519_verify(uint8_t *public_key, uint32_t msg_len, uint8_t *msg, uint8_t *signature);
```
- Semantics: verify an Ed25519 signature on `msg` under `public_key`.
- Buffers: `public_key[32]`, `msg[msg_len]`, `signature[64]`.
- Encoding: public key and `R` are 32-byte compressed Edwards points; `S` is a
  32-byte little-endian scalar.
- Validation: decompresses `public_key`; decompresses `signature[0..31]`; rejects
  if `S >= q`; then checks the verification equation. This is the only
  validation exposed by the high-level Ed25519 API.
- Return: `true` iff the signature verifies; `false` for invalid public key,
  invalid `R`, non-canonical/high `S`, or equation failure.
- Preconditions: valid input buffers.
### 4.3 `EverCrypt_Ed25519.h`
The F* implementation says: “For now, only one implementation... to be improved
in the future.” Every function forwards directly to the corresponding
`Hacl_Ed25519` function. There is no runtime assembly/C selection in the current
sources.
#### `EverCrypt_Ed25519_secret_to_public`
```c
void EverCrypt_Ed25519_secret_to_public(uint8_t *public_key, uint8_t *private_key);
```
- Same semantics, buffer sizes, encodings, validation, and preconditions as
  `Hacl_Ed25519_secret_to_public`.
#### `EverCrypt_Ed25519_expand_keys`
```c
void EverCrypt_Ed25519_expand_keys(uint8_t *expanded_keys, uint8_t *private_key);
```
- Same semantics as `Hacl_Ed25519_expand_keys`.
- Buffer sizes: `expanded_keys[96]`, `private_key[32]`.
#### `EverCrypt_Ed25519_sign_expanded`
```c
void
EverCrypt_Ed25519_sign_expanded(
  uint8_t *signature,
  uint8_t *expanded_keys,
  uint32_t msg_len,
  uint8_t *msg
);
```
- Same semantics as `Hacl_Ed25519_sign_expanded`.
- Buffers: `signature[64]`, `expanded_keys[96]`, `msg[msg_len]`.
#### `EverCrypt_Ed25519_sign`
```c
void
EverCrypt_Ed25519_sign(
  uint8_t *signature,
  uint8_t *private_key,
  uint32_t msg_len,
  uint8_t *msg
);
```
- Same semantics as `Hacl_Ed25519_sign`.
- Buffers: `signature[64]`, `private_key[32]`, `msg[msg_len]`.
#### `EverCrypt_Ed25519_verify`
```c
bool
EverCrypt_Ed25519_verify(
  uint8_t *public_key,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *signature
);
```
- Same semantics as `Hacl_Ed25519_verify`.
- Return: `true` iff signature verification succeeds; `false` otherwise.
## 5. P-256 public API: `Hacl_P256.h`
### 5.1 Common P-256 semantics
- All P-256 integer byte strings are 32-byte big-endian values. This is
  explicit in the F* sources (`nat_from_bytes_be`, `bn_from_bytes_be4`,
  `bn_to_bytes_be4`).
- Raw public keys and ECDH shared secrets are 64 bytes `x || y`, each coordinate
  a 32-byte big-endian field element. Note: this ECDH API returns the full raw
  point, not only an x-coordinate KDF input.
- SEC1 encodings: uncompressed public key is 65 bytes `0x04 || x || y`;
  compressed public key is 33 bytes `(0x02 if y even, 0x03 if y odd) || x`.
- Private key validity: `0 < private_key < order`.
- Signature scalar validity: `0 < r,s < order`.
- Hashing variants: SHA2-256, SHA2-384, SHA2-512, and `without_hash`.
  `without_hash` requires `msg_len >= 32` and uses the first 32 bytes as the
  ECDSA integer modulo the group order; it does not left-pad shorter inputs.
- The caller supplies the ECDSA nonce `k` as a 32-byte `nonce` buffer. HACL* does
  not generate deterministic RFC6979 nonces in this API.
- P-256 has no low-S normalization helpers in this header.
### 5.2 P-256 ECDSA signing
#### `Hacl_P256_ecdsa_sign_p256_sha2`
```c
bool
Hacl_P256_ecdsa_sign_p256_sha2(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);
```
- Semantics: SHA2-256-hash `msg`, then ECDSA-sign the hash.
- Buffers: `signature[64]`, `msg[msg_len]`, `private_key[32]`, `nonce[32]`.
- Encoding: `signature = R || S`, both 32-byte big-endian.
- Validation: checks private key and nonce are each in `1..order-1`; also fails
  if generated `r` or `s` is zero.
- Return: `true` iff a signature was created and written; `false` for invalid
  private key/nonce or zero `r`/`s`.
- Preconditions: valid, live buffers; `signature` disjoint from inputs in F*.
#### `Hacl_P256_ecdsa_sign_p256_sha384`
```c
bool
Hacl_P256_ecdsa_sign_p256_sha384(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);
```
- Same as the SHA2-256 signing function except the message is hashed with
  SHA2-384 and then truncated/converted by the P-256 ECDSA spec path to the
  first 32 hash bytes modulo the order.
#### `Hacl_P256_ecdsa_sign_p256_sha512`
```c
bool
Hacl_P256_ecdsa_sign_p256_sha512(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);
```
- Same as the SHA2-256 signing function except the message is hashed with
  SHA2-512 and then the first 32 hash bytes are used modulo the order.
#### `Hacl_P256_ecdsa_sign_p256_without_hash`
```c
bool
Hacl_P256_ecdsa_sign_p256_without_hash(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);
```
- Semantics: ECDSA-sign a caller-supplied prehashed/input byte string without
  hashing inside HACL*.
- Buffers: `signature[64]`, `msg[msg_len]`, `private_key[32]`, `nonce[32]`.
- Encoding: big-endian `R || S`.
- Special precondition: `msg_len >= 32`. The header explicitly says HACL* does
  not emulate OpenSSL/Fiat-Crypto left-padding for shorter inputs.
- Validation/return: same as other P-256 signing functions.
### 5.3 P-256 ECDSA verification
#### `Hacl_P256_ecdsa_verif_p256_sha2`
```c
bool
Hacl_P256_ecdsa_verif_p256_sha2(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
);
```
- Semantics: SHA2-256-hash `msg`, then verify ECDSA.
- Buffers: `msg[msg_len]`, `public_key[64]`, `signature_r[32]`,
  `signature_s[32]`.
- Encoding: public key `x || y`, all big-endian; signature halves big-endian.
- Validation: validates public key; validates `0 < r,s < order`; rejects point at
  infinity during verification.
- Return: `true` iff signature is valid; `false` for invalid public key, invalid
  signature scalars, or equation mismatch.
- Preconditions: valid buffers.
#### `Hacl_P256_ecdsa_verif_p256_sha384`
```c
bool
Hacl_P256_ecdsa_verif_p256_sha384(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
);
```
- Same as SHA2-256 verification except the message is hashed with SHA2-384.
#### `Hacl_P256_ecdsa_verif_p256_sha512`
```c
bool
Hacl_P256_ecdsa_verif_p256_sha512(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
);
```
- Same as SHA2-256 verification except the message is hashed with SHA2-512.
#### `Hacl_P256_ecdsa_verif_without_hash`
```c
bool
Hacl_P256_ecdsa_verif_without_hash(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature_r,
  uint8_t *signature_s
);
```
- Semantics: verify ECDSA over a caller-supplied prehashed/input byte string.
- Special precondition: `msg_len >= 32`.
- Buffers and validation: same as other verification functions.
- Return: `true` iff verification succeeds.
### 5.4 P-256 key validation
#### `Hacl_P256_validate_public_key`
```c
bool Hacl_P256_validate_public_key(uint8_t *public_key);
```
- Semantics: validate raw P-256 public key.
- Buffer: `public_key[64] = x[32] || y[32]`, big-endian.
- Validation: not point at infinity; `x` and `y` in `[0,p-1]`; curve equation
  `y^2 = x^3 + ax + b`.
- Return: `true` iff valid; `false` otherwise.
#### `Hacl_P256_validate_private_key`
```c
bool Hacl_P256_validate_private_key(uint8_t *private_key);
```
- Semantics: validate scalar private key.
- Buffer: `private_key[32]`, big-endian.
- Return: `true` iff `0 < private_key < order`; `false` otherwise.
### 5.5 P-256 public-key conversion
#### `Hacl_P256_uncompressed_to_raw`
```c
bool Hacl_P256_uncompressed_to_raw(uint8_t *pk, uint8_t *pk_raw);
```
- Semantics: convert 65-byte uncompressed SEC1 public key to raw form.
- Buffers: input `pk[65]`, output `pk_raw[64]`.
- Encoding: `pk = 0x04 || x || y`, output `x || y`, big-endian coordinates.
- Validation: checks only that conversion succeeds, i.e. header byte is `0x04`;
  it does **not** check that `(x,y)` is a valid point.
- Return: `true` iff header/format accepted; `false` otherwise.
- Preconditions: valid, disjoint input and output buffers.
#### `Hacl_P256_compressed_to_raw`
```c
bool Hacl_P256_compressed_to_raw(uint8_t *pk, uint8_t *pk_raw);
```
- Semantics: decompress a 33-byte compressed SEC1 public key to raw form.
- Buffers: input `pk[33]`, output `pk_raw[64]`.
- Encoding: `pk = 0x02/0x03 || x`, output `x || y`, big-endian.
- Validation: checks prefix, checks `x < p`, recovers `y`, and checks the point
  is on the curve.
- Return: `true` iff decompression and validation succeed; `false` otherwise.
#### `Hacl_P256_raw_to_uncompressed`
```c
void Hacl_P256_raw_to_uncompressed(uint8_t *pk_raw, uint8_t *pk);
```
- Semantics: prepend `0x04` to a raw key.
- Buffers: input `pk_raw[64]`, output `pk[65]`.
- Encoding: big-endian coordinates.
- Validation: none; does not check that `(x,y)` is a valid point.
- Return: none.
#### `Hacl_P256_raw_to_compressed`
```c
void Hacl_P256_raw_to_compressed(uint8_t *pk_raw, uint8_t *pk);
```
- Semantics: create compressed SEC1 encoding from raw `x || y` by using the parity
  of `y`.
- Buffers: input `pk_raw[64]`, output `pk[33]`.
- Encoding: output prefix `0x02` for even `y`, `0x03` for odd `y`; integers
  big-endian.
- Validation: none; does not check that `(x,y)` is a valid point.
- Return: none.
### 5.6 P-256 ECDH
#### `Hacl_P256_dh_initiator`
```c
bool Hacl_P256_dh_initiator(uint8_t *public_key, uint8_t *private_key);
```
- Semantics: derive P-256 public key `[private_key]G`.
- Buffers: `public_key[64]`, `private_key[32]`.
- Encoding: output raw `x || y`, big-endian.
- Validation: validates private key `0 < sk < order`.
- Return: `true` iff private key is valid; `false` otherwise.
- Preconditions: output and input disjoint in F*.
#### `Hacl_P256_dh_responder`
```c
bool
Hacl_P256_dh_responder(uint8_t *shared_secret, uint8_t *their_pubkey, uint8_t *private_key);
```
- Semantics: compute `[private_key]their_pubkey`.
- Buffers: `shared_secret[64]`, `their_pubkey[64]`, `private_key[32]`.
- Encoding: raw input/output points `x || y`, big-endian.
- Validation: validates private key and peer public key.
- Return: `true` iff both private key and peer public key are valid and the
  shared point was written; `false` otherwise.
- Low-order handling: P-256 has cofactor 1; invalid/infinity public keys are
  rejected by public-key validation rather than all-zero checking.
## 6. K-256 ECDSA and ECDH API: `Hacl_K256_ECDSA.h`
### 6.1 Common K-256 semantics
- All secp256k1 integers in public byte APIs are 32-byte big-endian values.
- Raw public keys and ECDH shared secrets are 64 bytes `x || y`, big-endian.
  As with P-256, ECDH returns the full raw point, not only the x-coordinate.
- ECDSA `msgHash` inputs are exactly 32 bytes and interpreted big-endian modulo
  the group order `q`.
- The caller supplies the ECDSA nonce `k`; this API does not generate it.
- Two ECDSA families are exposed:
  - `ecdsa_*`: accepts and may produce non-low-S signatures.
  - `secp256k1_ecdsa_*`: Bitcoin/secp256k1-style low-S canonical behavior.
- No Ethereum-style public-key recovery, recovery id, or recoverable-signature
  entry point is present in the covered public header or K-256 sources searched.
### 6.2 K-256 ECDSA without low-S enforcement
#### `Hacl_K256_ECDSA_ecdsa_sign_hashed_msg`
```c
bool
Hacl_K256_ECDSA_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
);
```
- Semantics: ECDSA-sign a 32-byte prehashed message.
- Buffers: `signature[64]`, `msgHash[32]`, `private_key[32]`, `nonce[32]`.
- Encoding: signature `R || S`, big-endian halves.
- Validation: checks private key and nonce are in `1..q-1`; fails if generated
  `r` or `s` is zero.
- Low-S: does **not** normalize `S`.
- Return: `true` iff signature creation succeeds; `false` otherwise.
#### `Hacl_K256_ECDSA_ecdsa_sign_sha256`
```c
bool
Hacl_K256_ECDSA_ecdsa_sign_sha256(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);
```
- Semantics: SHA2-256-hash `msg`, then call the hashed-message signer.
- Buffers: `signature[64]`, `msg[msg_len]`, `private_key[32]`, `nonce[32]`.
- Validation/return: same as hashed-message signer.
- Low-S: does **not** normalize `S`.
#### `Hacl_K256_ECDSA_ecdsa_verify_hashed_msg`
```c
bool
Hacl_K256_ECDSA_ecdsa_verify_hashed_msg(uint8_t *m, uint8_t *public_key, uint8_t *signature);
```
- Semantics: verify ECDSA over 32-byte message hash `m`.
- Buffers: `m[32]`, `public_key[64]`, `signature[64]`.
- Encoding: big-endian.
- Validation: validates public key; validates `0 < R,S < q`; accepts high-S
  signatures if mathematically valid.
- Return: `true` iff valid; `false` otherwise.
#### `Hacl_K256_ECDSA_ecdsa_verify_sha256`
```c
bool
Hacl_K256_ECDSA_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
);
```
- Semantics: SHA2-256-hash `msg`, then verify with the non-low-S-enforcing
  verifier.
- Buffers: `msg[msg_len]`, `public_key[64]`, `signature[64]`.
- Return: `true` iff the signature verifies; high-S signatures are accepted.
### 6.3 K-256 low-S helpers and secp256k1-style ECDSA
#### `Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize`
```c
bool Hacl_K256_ECDSA_secp256k1_ecdsa_signature_normalize(uint8_t *signature);
```
- Semantics: replace `S` by the canonical lowest value: if `S > q/2`, write
  `q - S`; otherwise leave it unchanged.
- Buffer: in-place `signature[64]`, big-endian `R || S`.
- Validation: checks `0 < S < q`. It does not validate `R` or a public key.
- Return: `true` iff `S` was a valid scalar and output was normalized; `false`
  otherwise.
#### `Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized`
```c
bool Hacl_K256_ECDSA_secp256k1_ecdsa_is_signature_normalized(uint8_t *signature);
```
- Semantics: test low-S canonical form.
- Buffer: `signature[64]`.
- Validation: reads only `S`; returns `true` iff `0 < S <= q/2`.
- Return: `true` iff low-S normalized; `false` for zero, high, or out-of-range
  `S`.
#### `Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg`
```c
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_sign_hashed_msg(
  uint8_t *signature,
  uint8_t *msgHash,
  uint8_t *private_key,
  uint8_t *nonce
);
```
- Semantics: ECDSA-sign a 32-byte prehash, then normalize `S` to low-S form.
- Buffers: `signature[64]`, `msgHash[32]`, `private_key[32]`, `nonce[32]`.
- Validation: validates private key and nonce; fails on zero `r`/`s`; normalization
  also requires valid `S`.
- Return: `true` iff signature creation and normalization succeed.
#### `Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256`
```c
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_sign_sha256(
  uint8_t *signature,
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *private_key,
  uint8_t *nonce
);
```
- Semantics: SHA2-256-hash `msg`, then low-S secp256k1-style sign.
- Buffers: `signature[64]`, `msg[msg_len]`, `private_key[32]`, `nonce[32]`.
- Return: `true` iff successful.
#### `Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg`
```c
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_verify_hashed_msg(
  uint8_t *msgHash,
  uint8_t *public_key,
  uint8_t *signature
);
```
- Semantics: verify ECDSA over a 32-byte prehash, but first require low-S.
- Buffers: `msgHash[32]`, `public_key[64]`, `signature[64]`.
- Validation: rejects unless `0 < S <= q/2`; then performs the same public-key
  and `R,S` validation/equation checks as the generic verifier.
- Return: `true` iff signature is low-S and verifies.
#### `Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256`
```c
bool
Hacl_K256_ECDSA_secp256k1_ecdsa_verify_sha256(
  uint32_t msg_len,
  uint8_t *msg,
  uint8_t *public_key,
  uint8_t *signature
);
```
- Semantics: SHA2-256-hash `msg`, then low-S-enforcing verification.
- Buffers: `msg[msg_len]`, `public_key[64]`, `signature[64]`.
- Return: `true` iff low-S and mathematically valid.
### 6.4 K-256 public-key conversion
#### `Hacl_K256_ECDSA_public_key_uncompressed_to_raw`
```c
bool Hacl_K256_ECDSA_public_key_uncompressed_to_raw(uint8_t *pk_raw, uint8_t *pk);
```
- Semantics: convert uncompressed SEC1 key to raw key.
- Buffers: output `pk_raw[64]`, input `pk[65]`.
- Encoding: input `0x04 || x || y`, output `x || y`, big-endian.
- Validation: checks format prefix; does **not** check that `(x,y)` is a valid
  secp256k1 point.
- Return: `true` iff conversion succeeds; `false` otherwise.
#### `Hacl_K256_ECDSA_public_key_uncompressed_from_raw`
```c
void Hacl_K256_ECDSA_public_key_uncompressed_from_raw(uint8_t *pk, uint8_t *pk_raw);
```
- Semantics: prepend `0x04` to raw public key.
- Buffers: output `pk[65]`, input `pk_raw[64]`.
- Validation: none.
- Return: none.
#### `Hacl_K256_ECDSA_public_key_compressed_to_raw`
```c
bool Hacl_K256_ECDSA_public_key_compressed_to_raw(uint8_t *pk_raw, uint8_t *pk);
```
- Semantics: decompress compressed SEC1 key.
- Buffers: output `pk_raw[64]`, input `pk[33]`.
- Encoding: input `0x02/0x03 || x`; output `x || y`, big-endian.
- Validation: checks prefix, `x`, and curve equation during decompression.
- Return: `true` iff valid compressed point; `false` otherwise.
#### `Hacl_K256_ECDSA_public_key_compressed_from_raw`
```c
void Hacl_K256_ECDSA_public_key_compressed_from_raw(uint8_t *pk, uint8_t *pk_raw);
```
- Semantics: produce compressed SEC1 key from raw `x || y`.
- Buffers: output `pk[33]`, input `pk_raw[64]`.
- Encoding: prefix `0x02` if big-endian `y` is even, `0x03` if odd.
- Validation: none; does not check raw point validity.
- Return: none.
### 6.5 K-256 key validation and ECDH
#### `Hacl_K256_ECDSA_is_public_key_valid`
```c
bool Hacl_K256_ECDSA_is_public_key_valid(uint8_t *public_key);
```
- Semantics: validate raw secp256k1 public key.
- Buffer: `public_key[64] = x || y`, big-endian.
- Validation: `x < p`, `y < p`, and `y^2 = x^3 + 7`; point at infinity is not a
  raw affine encoding.
- Return: `true` iff valid; `false` otherwise.
#### `Hacl_K256_ECDSA_is_private_key_valid`
```c
bool Hacl_K256_ECDSA_is_private_key_valid(uint8_t *private_key);
```
- Semantics: validate scalar private key.
- Buffer: `private_key[32]`, big-endian.
- Return: `true` iff `0 < private_key < q`; `false` otherwise.
#### `Hacl_K256_ECDSA_secret_to_public`
```c
bool Hacl_K256_ECDSA_secret_to_public(uint8_t *public_key, uint8_t *private_key);
```
- Semantics: derive secp256k1 public key `[private_key]G`.
- Buffers: `public_key[64]`, `private_key[32]`.
- Encoding: output raw `x || y`, big-endian.
- Validation: validates private key.
- Return: `true` iff private key is valid; `false` otherwise.
#### `Hacl_K256_ECDSA_ecdh`
```c
bool Hacl_K256_ECDSA_ecdh(uint8_t *shared_secret, uint8_t *their_pubkey, uint8_t *private_key);
```
- Semantics: compute secp256k1 scalar multiplication
  `[private_key]their_pubkey`.
- Buffers: `shared_secret[64]`, `their_pubkey[64]`, `private_key[32]`.
- Encoding: raw input/output `x || y`, big-endian.
- Validation: validates private key and peer public key.
- Return: `true` iff both validations succeed and shared point is written;
  `false` otherwise.
- Low-order handling: secp256k1 has cofactor 1; invalid raw public keys are
  rejected rather than mapped to all-zero shared secrets.
## 7. Low-level Edwards25519 arithmetic API: `Hacl_EC_Ed25519.h`
### 7.1 Representation warning
This header exposes expert-only building blocks. It is not a safe high-level
Ed25519 API. It exposes non-canonical internal representations with invariants
normally maintained by generated code:
- Field modulus: `p = 2^255 - 19`.
- Field element representation: `uint64_t[5]`, radix 2^51.
- Point representation: `uint64_t[20]`, extended homogeneous Edwards
  coordinates `(X,Y,Z,T)`, each coordinate a 5-limb field element.
- Byte field/scalar encodings are little-endian.
- Functions do not generally validate that caller-supplied limb arrays satisfy
  all internal bounds or point-representation invariants. Reimplement these only
  if you also reproduce the representation discipline.
### 7.2 Field operations
#### `Hacl_EC_Ed25519_mk_felem_zero`
```c
void Hacl_EC_Ed25519_mk_felem_zero(uint64_t *b);
```
- Writes field zero to `b[5]`.
- Return: none.
#### `Hacl_EC_Ed25519_mk_felem_one`
```c
void Hacl_EC_Ed25519_mk_felem_one(uint64_t *b);
```
- Writes field one to `b[5]`.
- Return: none.
#### `Hacl_EC_Ed25519_felem_add`
```c
void Hacl_EC_Ed25519_felem_add(uint64_t *a, uint64_t *b, uint64_t *out);
```
- Computes `out = a + b mod p` over `uint64_t[5]` limbs.
- Aliasing: `a`, `b`, and `out` either pairwise disjoint or equal.
#### `Hacl_EC_Ed25519_felem_sub`
```c
void Hacl_EC_Ed25519_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out);
```
- Computes `out = a - b mod p` over `uint64_t[5]` limbs.
- Aliasing: `a`, `b`, and `out` either pairwise disjoint or equal.
#### `Hacl_EC_Ed25519_felem_mul`
```c
void Hacl_EC_Ed25519_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out);
```
- Computes `out = a * b mod p` over `uint64_t[5]` limbs.
- Aliasing: `a`, `b`, and `out` either pairwise disjoint or equal.
#### `Hacl_EC_Ed25519_felem_sqr`
```c
void Hacl_EC_Ed25519_felem_sqr(uint64_t *a, uint64_t *out);
```
- Computes `out = a^2 mod p`.
- Aliasing: `a` and `out` either disjoint or equal.
#### `Hacl_EC_Ed25519_felem_inv`
```c
void Hacl_EC_Ed25519_felem_inv(uint64_t *a, uint64_t *out);
```
- Computes `out = a^(p-2) mod p`, the multiplicative inverse when `a != 0`.
- Aliasing: `a` and `out` must be disjoint.
- Validation: no zero-input error flag.
#### `Hacl_EC_Ed25519_felem_load`
```c
void Hacl_EC_Ed25519_felem_load(uint8_t *b, uint64_t *out);
```
- Loads `b[32]` little-endian into a field element `out[5]`.
- The header notes reduction modulo `2^255`; source postcondition is
  `nat_from_bytes_le(b) % 2^255`.
- Aliasing: `b` and `out` disjoint.
#### `Hacl_EC_Ed25519_felem_store`
```c
void Hacl_EC_Ed25519_felem_store(uint64_t *a, uint8_t *out);
```
- Serializes field element `a[5]` as `out[32]` little-endian.
- Aliasing: `a` and `out` disjoint.
### 7.3 Point operations
#### `Hacl_EC_Ed25519_mk_point_at_inf`
```c
void Hacl_EC_Ed25519_mk_point_at_inf(uint64_t *p);
```
- Writes the additive identity to `p[20]`.
#### `Hacl_EC_Ed25519_mk_base_point`
```c
void Hacl_EC_Ed25519_mk_base_point(uint64_t *p);
```
- Writes the Edwards25519 base point to `p[20]`.
#### `Hacl_EC_Ed25519_point_negate`
```c
void Hacl_EC_Ed25519_point_negate(uint64_t *p, uint64_t *out);
```
- Computes `out = -p` over internal extended coordinates.
- Buffers: `p[20]`, `out[20]`.
- Aliasing: `p` and `out` disjoint.
#### `Hacl_EC_Ed25519_point_add`
```c
void Hacl_EC_Ed25519_point_add(uint64_t *p, uint64_t *q, uint64_t *out);
```
- Computes `out = p + q`.
- Buffers: all `uint64_t[20]`.
- Aliasing: `p`, `q`, and `out` either pairwise disjoint or equal.
#### `Hacl_EC_Ed25519_point_double`
```c
void Hacl_EC_Ed25519_point_double(uint64_t *p, uint64_t *out);
```
- Computes `out = p + p`.
- Buffers: `p[20]`, `out[20]`.
- Aliasing: `p` and `out` either disjoint or equal.
#### `Hacl_EC_Ed25519_point_mul`
```c
void Hacl_EC_Ed25519_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out);
```
- Computes `out = [scalar]p`.
- Buffers: `scalar[32]`, `p[20]`, `out[20]`.
- Encoding: scalar loaded little-endian.
- Validation: no scalar range check and no point validity check; caller must
  provide valid internal point representation.
- Aliasing: all three pairwise disjoint.
#### `Hacl_EC_Ed25519_point_eq`
```c
bool Hacl_EC_Ed25519_point_eq(uint64_t *p, uint64_t *q);
```
- Compares two internal points for group equality.
- Buffers: `p[20]`, `q[20]`.
- Return: `true` iff equal; `false` otherwise.
- Aliasing: `p` and `q` either disjoint or equal.
#### `Hacl_EC_Ed25519_point_compress`
```c
void Hacl_EC_Ed25519_point_compress(uint64_t *p, uint8_t *out);
```
- Converts internal extended point to affine and writes compressed Ed25519 form.
- Buffers: `p[20]`, `out[32]`.
- Encoding: little-endian `y` with top bit equal to `x mod 2`, i.e.
  `2^255 * (x % 2) + y`.
- Validation: no public error flag.
- Aliasing: `p` and `out` disjoint.
#### `Hacl_EC_Ed25519_point_decompress`
```c
bool Hacl_EC_Ed25519_point_decompress(uint8_t *s, uint64_t *out);
```
- Decompresses 32-byte compressed Ed25519 point into internal coordinates.
- Buffers: `s[32]`, `out[20]`.
- Encoding: little-endian compressed point.
- Validation: returns `true` iff decompression succeeds; `false` otherwise.
- Aliasing: `s` and `out` disjoint.
## 8. Low-level K-256 arithmetic API: `Hacl_EC_K256.h`
### 8.1 Representation warning
This header is unsafe/expert-only, like `Hacl_EC_Ed25519.h`.
- Field modulus: `p = 2^256 - 0x1000003D1`.
- Field element representation: `uint64_t[5]`, radix 2^52.
- Point representation: `uint64_t[15]`, projective coordinates, three 5-limb
  field elements.
- Byte encodings are big-endian. The generated comments contain a typo
  “bid-endian” in two places; the F* sources use `nat_from_bytes_be` and
  `nat_to_bytes_be`.
- Callers must maintain limb bounds and point invariants. Most operations assume
  valid internal representations and are not standalone validators.
### 8.2 Field operations
#### `Hacl_EC_K256_mk_felem_zero`
```c
void Hacl_EC_K256_mk_felem_zero(uint64_t *f);
```
- Writes field zero to `f[5]`.
#### `Hacl_EC_K256_mk_felem_one`
```c
void Hacl_EC_K256_mk_felem_one(uint64_t *f);
```
- Writes field one to `f[5]`.
#### `Hacl_EC_K256_felem_add`
```c
void Hacl_EC_K256_felem_add(uint64_t *a, uint64_t *b, uint64_t *out);
```
- Computes `out = a + b mod p` over `uint64_t[5]`.
- Aliasing: `a`, `b`, `out` either pairwise disjoint or equal.
#### `Hacl_EC_K256_felem_sub`
```c
void Hacl_EC_K256_felem_sub(uint64_t *a, uint64_t *b, uint64_t *out);
```
- Computes `out = a - b mod p` over `uint64_t[5]`.
- Aliasing: `a`, `b`, `out` either pairwise disjoint or equal.
#### `Hacl_EC_K256_felem_mul`
```c
void Hacl_EC_K256_felem_mul(uint64_t *a, uint64_t *b, uint64_t *out);
```
- Computes `out = a * b mod p` over `uint64_t[5]`.
- Aliasing: `a`, `b`, `out` either pairwise disjoint or equal.
#### `Hacl_EC_K256_felem_sqr`
```c
void Hacl_EC_K256_felem_sqr(uint64_t *a, uint64_t *out);
```
- Computes `out = a^2 mod p`.
- Aliasing: `a` and `out` either disjoint or equal.
#### `Hacl_EC_K256_felem_inv`
```c
void Hacl_EC_K256_felem_inv(uint64_t *a, uint64_t *out);
```
- Computes `out = a^(p-2) mod p`, the inverse for nonzero `a`.
- Aliasing: `a` and `out` disjoint.
- Validation: no zero-input failure flag.
#### `Hacl_EC_K256_felem_load`
```c
void Hacl_EC_K256_felem_load(uint8_t *b, uint64_t *out);
```
- Loads `b[32]` big-endian into `out[5]`.
- Source postcondition: `out` represents `nat_from_bytes_be(b) mod p`.
- Aliasing: `b` and `out` disjoint.
#### `Hacl_EC_K256_felem_store`
```c
void Hacl_EC_K256_felem_store(uint64_t *a, uint8_t *out);
```
- Stores `a[5]` as a 32-byte big-endian field element.
- Aliasing: `a` and `out` disjoint.
### 8.3 Point operations
#### `Hacl_EC_K256_mk_point_at_inf`
```c
void Hacl_EC_K256_mk_point_at_inf(uint64_t *p);
```
- Writes point at infinity to `p[15]`.
#### `Hacl_EC_K256_mk_base_point`
```c
void Hacl_EC_K256_mk_base_point(uint64_t *p);
```
- Writes secp256k1 generator to `p[15]`.
#### `Hacl_EC_K256_point_negate`
```c
void Hacl_EC_K256_point_negate(uint64_t *p, uint64_t *out);
```
- Computes `out = -p`.
- Buffers: `p[15]`, `out[15]`.
- Aliasing: `p` and `out` either disjoint or equal.
#### `Hacl_EC_K256_point_add`
```c
void Hacl_EC_K256_point_add(uint64_t *p, uint64_t *q, uint64_t *out);
```
- Computes `out = p + q`.
- Buffers: all `uint64_t[15]`.
- Aliasing: `p`, `q`, `out` either pairwise disjoint or equal.
#### `Hacl_EC_K256_point_double`
```c
void Hacl_EC_K256_point_double(uint64_t *p, uint64_t *out);
```
- Computes `out = p + p`.
- Buffers: `p[15]`, `out[15]`.
- Aliasing: `p` and `out` either disjoint or equal.
#### `Hacl_EC_K256_point_mul`
```c
void Hacl_EC_K256_point_mul(uint8_t *scalar, uint64_t *p, uint64_t *out);
```
- Computes `out = [scalar]p`.
- Buffers: `scalar[32]`, `p[15]`, `out[15]`.
- Encoding: scalar loaded big-endian. The source notes it is safe to invoke with
  `scalar >= q`; the mathematical point multiplication uses the loaded integer.
- Validation: no boolean validation of scalar range or internal point validity.
- Aliasing: all three pairwise disjoint.
#### `Hacl_EC_K256_point_store`
```c
void Hacl_EC_K256_point_store(uint64_t *p, uint8_t *out);
```
- Converts projective point to affine raw form and stores `out[64] = x || y`.
- Encoding: each coordinate 32-byte big-endian.
- Buffers: `p[15]`, `out[64]`.
- Aliasing: `p` and `out` disjoint.
#### `Hacl_EC_K256_point_load`
```c
void Hacl_EC_K256_point_load(uint8_t *b, uint64_t *out);
```
- Loads raw affine point `b[64] = x || y` into projective `out[15]`.
- Encoding: big-endian coordinates.
- Preconditions: header requires `b` is a valid point: `x < p`, `y < p`, and on
  the curve; `b` and `out` disjoint.
- Validation: no return value. Use `Hacl_EC_K256_is_point_valid` before loading
  untrusted bytes.
#### `Hacl_EC_K256_is_point_valid`
```c
bool Hacl_EC_K256_is_point_valid(uint8_t *b);
```
- Validates raw affine secp256k1 point `b[64] = x || y`.
- Encoding: big-endian.
- Checks: `x < p`, `y < p`, and point on `y^2 = x^3 + 7`.
- Return: `true` iff valid; `false` otherwise.
- Constant-time: header explicitly says this function is **not constant-time**.
## 9. Internal headers and precomputed tables
The internal headers confirm representation and build-shape facts but should not
be considered stable high-level API:
- `internal/Hacl_Bignum25519_51.h` contains inline radix-2^51 field routines for
  Curve25519/Ed25519-style arithmetic. It operates on 5-limb arrays and uses
  wide multiplication support from KaRaMeL/FStar UInt128 helpers.
- `internal/Hacl_Ed25519.h` exposes lower-level bignum and point routines such as
  `Hacl_Bignum25519_load_51`, `Hacl_Bignum25519_store_51`, point add/double,
  point decompression/compression, equality, negation, and ladder multiplication.
  These explain how the public `Hacl_EC_Ed25519` layer is connected to internals.
- `internal/Hacl_P256.h` exposes internal DH wrappers
  `Hacl_Impl_P256_DH_ecp256dh_i` and `_r`, mirroring public initiator/responder.
- `internal/Hacl_K256_ECDSA.h` exposes internal projective point operations and
  scalar multiplication used by public K-256 APIs.
- Generated precomputation table headers exist for Ed25519, P-256, and K-256:
  - `Hacl_Ed25519_PrecompTable_precomp_basepoint_table_w4[320]`
  - `Hacl_Ed25519_PrecompTable_precomp_g_pow2_64_table_w4[320]`
  - `Hacl_Ed25519_PrecompTable_precomp_g_pow2_128_table_w4[320]`
  - `Hacl_Ed25519_PrecompTable_precomp_g_pow2_192_table_w4[320]`
  - `Hacl_Ed25519_PrecompTable_precomp_basepoint_table_w5[640]`
  - `Hacl_P256_PrecompTable_precomp_basepoint_table_w4[192]`
  - `Hacl_P256_PrecompTable_precomp_g_pow2_64_table_w4[192]`
  - `Hacl_P256_PrecompTable_precomp_g_pow2_128_table_w4[192]`
  - `Hacl_P256_PrecompTable_precomp_g_pow2_192_table_w4[192]`
  - `Hacl_P256_PrecompTable_precomp_basepoint_table_w5[384]`
  - `Hacl_K256_PrecompTable_precomp_basepoint_table_w4[240]`
  - `Hacl_K256_PrecompTable_precomp_g_pow2_64_table_w4[240]`
  - `Hacl_K256_PrecompTable_precomp_g_pow2_128_table_w4[240]`
  - `Hacl_K256_PrecompTable_precomp_g_pow2_192_table_w4[240]`
  - `Hacl_K256_PrecompTable_precomp_basepoint_table_w5[480]`
- As noted in [surprises.md](surprises.md), these precomputed tables are
  generated as `static const` arrays in headers, so including them can duplicate
  constants into translation units.
## 10. Validation matrix
| Function family | Validates private scalar? | Validates public point? | Validates signature scalars? | Special boolean meaning |
| --- | --- | --- | --- | --- |
| X25519 `scalarmult`, `secret_to_public` | No; accepts any 32-byte scalar and applies X25519 scalar semantics | No separate public-point validation | N/A | No boolean return |
| X25519 `ecdh` | No separate private-key validity | Only detects low-order/all-zero result indirectly | N/A | `true` iff shared secret is not all zero |
| Ed25519 `secret_to_public`, `sign`, `expand_keys`, `sign_expanded` | No; accepts any 32-byte seed/expanded buffer | N/A for signing | N/A | No boolean return |
| Ed25519 `verify` | N/A | Decompresses public key and `R`; invalid encodings fail | Rejects `S >= q` | `true` iff signature verifies |
| P-256 signing | Yes, `0 < sk < order` | N/A | Fails if computed `r` or `s` is zero | `true` iff signature created |
| P-256 verification | N/A | Yes, raw public key must be valid | Yes, `0 < r,s < order` | `true` iff signature verifies |
| P-256 conversion uncompressed→raw | N/A | No curve validation; prefix/format only | N/A | `true` iff conversion succeeds |
| P-256 conversion compressed→raw | N/A | Yes, decompression validates point | N/A | `true` iff decompression succeeds |
| P-256 ECDH | Yes | Responder validates peer raw point | N/A | `true` iff required keys valid |
| K-256 generic ECDSA | Signing validates sk/nonce; verification validates no private scalar | Verification validates public key | Verification validates `0 < R,S < q`; accepts high-S | `true` iff operation succeeds/verifies |
| K-256 secp256k1 ECDSA | Same as generic | Same as generic | Requires low-S for secp256k1 verification; signing normalizes | `true` iff low-S policy and ECDSA pass |
| K-256 conversion uncompressed→raw | N/A | No curve validation; prefix/format only | N/A | `true` iff conversion succeeds |
| K-256 conversion compressed→raw | N/A | Yes, decompression validates point | N/A | `true` iff decompression succeeds |
| `Hacl_EC_Ed25519` low-level | Mostly no | Only `point_decompress` returns decompression success | N/A | Expert representation-level booleans |
| `Hacl_EC_K256` low-level | Mostly no | `is_point_valid` validates raw point; `point_load` assumes validity | N/A | Expert representation-level booleans |
## 11. Notes for reimplementers
1. **Do not unify endianness accidentally.** Curve25519 and Ed25519 are
   little-endian; P-256 and K-256 are big-endian. This affects public keys,
   scalars, signature halves, compressed-point parity, and prehash conversion.
2. **X25519 failure is all-zero only.** `ecdh` returns `false` when the computed
   shared secret is 32 zero bytes. `scalarmult` exposes the raw result and has no
   failure channel.
3. **Curve25519 has two modules with representation in the name.** `_51` is the
   portable radix-2^51 C path. `_64` is a separate radix-2^64 path that needs
   wide arithmetic and/or assembly. EverCrypt, not the Hacl module names, is the
   dispatch layer.
4. **EverCrypt_Ed25519 is not currently multiplexed.** It forwards directly to
   `Hacl_Ed25519`; unlike `EverCrypt_Curve25519`, it does not inspect CPU
   features in the current implementation.
5. **ECDSA nonces are caller-supplied.** P-256 and K-256 signing APIs take a
   32-byte `nonce`; callers must generate a fresh uniform nonce or a correct
   deterministic nonce outside these APIs.
6. **P-256 prehashed signing is asymmetric with OpenSSL-style behavior.** The
   `without_hash` functions require `msg_len >= 32` and do not left-pad shorter
   inputs.
7. **P-256 and K-256 ECDH return raw points.** The `shared_secret` buffer is 64
   bytes `x || y`, not the more common 32-byte x-coordinate output.
8. **P-256 signatures are split for verification; K-256 signatures are combined.**
   P-256 verify takes separate `signature_r` and `signature_s`; K-256 verify
   takes a single 64-byte `R || S` buffer.
9. **Low-S policy exists only in the K-256 API.** Generic K-256 ECDSA accepts
   high-S signatures; `secp256k1_ecdsa_*` enforces/produces low-S. P-256 has no
   corresponding public normalizer in this header.
10. **No recoverable K-256 API is present.** There are no Ethereum-style recovery
    id or public-key-recovery functions in `Hacl_K256_ECDSA.h`.
11. **Raw exposed field/point arithmetic is intentionally sharp.**
    `Hacl_EC_Ed25519` and `Hacl_EC_K256` are useful for building higher-level
    code but expose limb arrays whose invariants are not obvious from C types.
12. **Precomputed tables are public-looking generated constants.** They are used
    for base-point/windowed scalar multiplication and are emitted as static
    arrays in internal headers. Decide whether your reimplementation wants these
    as code constants, generated assets, or runtime tables.
13. **Conversion functions differ in validation.** Uncompressed-to-raw and
    raw-to-encoded conversions do not validate curve membership; compressed-to-
    raw validates because decompression necessarily solves/checks the curve
    equation.
14. **Some validation is variable-time.** Public-key parsing/decompression and
    low-level K-256 `is_point_valid` are documented or implemented as variable-
    time routines. Avoid using them on secrets.
15. **Header comments can contain typos.** `Hacl_EC_K256.h` says “bid-endian” in
    comments for load/scalar loading; source confirms big-endian.
