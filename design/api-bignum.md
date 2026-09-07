# HACL*/EverCrypt bignum, generic-field, RSA-PSS, and FFDHE public API

This document is for reimplementers. It describes the public C API generated in `dist/gcc-compatible/` for arbitrary-precision arithmetic and primitives that build on it. Cross-reference the sibling design notes: [README](README.md), [conventions](conventions.md), [curves API](api-curves.md), [implementation](implementation.md), and [surprises](surprises.md).

Primary headers covered: `Hacl_Bignum32.h`, `Hacl_Bignum64.h`, `Hacl_Bignum256.h`, `Hacl_Bignum256_32.h`, `Hacl_Bignum4096.h`, `Hacl_Bignum4096_32.h`, `Hacl_GenericField32.h`, `Hacl_GenericField64.h`, `Hacl_RSAPSS.h`, `Hacl_FFDHE.h`, and `Hacl_Bignum.h`. Internal headers consulted for type shape: `internal/Hacl_Bignum.h`, `internal/Hacl_Bignum_Base.h`, and `internal/Hacl_Impl_FFDHE_Constants.h`.

## 1. Families and representation

The bignum code appears as several public families, but the shape is generated from the same generic F*/Low* bignum and Montgomery code, instantiated at two limb widths: 32-bit (`uint32_t`) and 64-bit (`uint64_t`).

| Family | Headers | Size model | Limb width | Main use |
|---|---|---:|---:|---|
| Runtime-length bignums | `Hacl_Bignum32.h`, `Hacl_Bignum64.h` | caller supplies `len` in limbs | 32 or 64 | arbitrary precision chosen at runtime |
| Fixed-size bignums | `Hacl_Bignum256.h`, `Hacl_Bignum256_32.h`, `Hacl_Bignum4096.h`, `Hacl_Bignum4096_32.h` | 256 or 4096 bits | 32 or 64 | specialized fixed instantiations of the same operations |
| Montgomery generic fields | `Hacl_GenericField32.h`, `Hacl_GenericField64.h` | context stores `len` and modulus | 32 or 64 | finite-field arithmetic over a caller-selected odd modulus |
| Primitives on bignums | `Hacl_RSAPSS.h`, `Hacl_FFDHE.h` | RSA runtime bits; FFDHE named groups | mostly 64 | RSA-PSS and finite-field Diffie-Hellman |

### Limb and byte conventions

- **Limb order:** fixed-size headers explicitly state little-endian limb order: limb index 0 is the least-significant limb. The generic runtime modules are generated from the same bignum representation and conversion code; internal bignum values (`bn_v`) and `bn_from_bytes_*`/`bn_to_bytes_*` confirm the same least-significant-limb-first convention.
- **Native limb storage:** each `uint32_t`/`uint64_t` limb is stored in native C object representation. Do not serialize by dumping limb memory; use byte conversion functions.
- **Byte conversion:** `*_new_bn_from_bytes_be` reads a big-endian byte string; `*_new_bn_from_bytes_le` reads a little-endian byte string. `*_bn_to_bytes_be` and `*_bn_to_bytes_le` write exactly the requested byte count in that byte order.
- **`len` is overloaded:** in arithmetic functions, `len` is a limb count. In byte conversion functions, `len` is a byte count. In RSA, `modBits`/`eBits`/`dBits` are bit counts. In FFDHE, `Hacl_FFDHE_ffdhe_len` returns byte length.
- **Allocation:** functions named `new_*` allocate with the HACL/KreML host allocator (`malloc`/`calloc` equivalent) and return `NULL` on allocation or validation failure. The caller owns successful results and frees them with `free`/`KRML_HOST_FREE` as appropriate for the embedding.
- **Aliasing:** when headers or F* preconditions say “may have exactly equal memory location”, in-place use is allowed only for the exact same buffer, not partial overlap. When they say “disjoint”, no overlap is allowed. If not documented in a generated header, use the F* precondition summarized below.

Allocation/freeing inventory:

| Allocating API | Successful return | Failure return | Required free |
|---|---|---|---|
| `Hacl_Bignum{32,64,256,256_32,4096,4096_32}_new_bn_from_bytes_{be,le}` | heap limb array of `ceil(byte_len/wordbytes)` limbs | `NULL` for `byte_len == 0`, allocation failure, or allocation too large | caller `free`/host free |
| `Hacl_Bignum{32,64,256,256_32,4096,4096_32}_mont_ctx_init` | heap Montgomery context with owned `n` and `r2` arrays | `NULL` on allocation failure; modulus validity is a caller precondition | matching `*_mont_ctx_free` |
| `Hacl_GenericField{32,64}_field_init` | heap Montgomery context with owned `n` and `r2` arrays | `NULL` on allocation failure; modulus validity is a caller precondition | matching `*_field_free` |
| `Hacl_RSAPSS_new_rsapss_load_{pkey,skey}` | heap `uint64_t` flat key array | `NULL` on invalid lengths/key parts or allocation failure | caller `free`/host free |
| `Hacl_FFDHE_new_ffdhe_precomp_p` | heap `uint64_t[2*nLen]` precomputation `[p;r2]` | `NULL` on allocation failure | caller `free`/host free |

### Constant-time contract (security-critical)

The API intentionally exposes both constant-time and variable-time exponentiation paths.

| Category | Functions | Timing note |
|---|---|---|
| Explicit variable-time | names containing `_vartime`: `mod_exp_vartime`, `mod_exp_vartime_precomp`, `mod_inv_prime_vartime`, `mod_inv_prime_vartime_precomp`, `exp_vartime`; also generic-field `inverse` internally uses a variable-time exponentiation path | **Do not use with secret exponent/control data.** Header comments say these are not constant-time on exponent `b`; inverse leaks through `n-2`/algorithm choices only if that is sensitive. |
| Explicit constant-time over exponent | `mod_exp_consttime`, `mod_exp_consttime_precomp`, `Hacl_GenericField*_exp_consttime`; FFDHE exponentiation uses the constant-time precomputed exponentiation helper | Constant-time with respect to exponent bits according to the header/F* contract; loop length still depends on public `bBits`/group size. |
| Arithmetic/comparison masks | add/sub/modular add/sub, multiplication/square, mask comparisons, Montgomery field add/sub/mul/sqr/one/to/from | No `_vartime` suffix and fixed loops over public lengths. Treat public lengths/moduli as public and still obey memory/precondition requirements. |
| RSA-PSS verify/public exponent | RSA public exponentiation uses the variable-time path internally; the public exponent is normally public. RSA private exponentiation in signing uses the constant-time path. | Keep exponents classified correctly in a reimplementation. |

## 2. Montgomery context type (`Hacl_Bignum.h`)

`Hacl_Bignum.h` exposes the structure, but the lifecycle functions own the allocation of the structure and of the two limb arrays inside it. Treat contexts as immutable after initialization unless you reimplement the whole ownership protocol.

```c
typedef struct Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32_s
{
  uint32_t len;
  uint32_t *n;
  uint32_t mu;
  uint32_t *r2;
}
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32;

typedef struct Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64_s
{
  uint32_t len;
  uint64_t *n;
  uint64_t mu;
  uint64_t *r2;
}
Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64;
```

Field meanings:

| Field | Meaning |
|---|---|
| `len` | modulus length in limbs |
| `n` | heap-allocated modulus, `len` limbs |
| `mu` | Montgomery single-limb inverse parameter satisfying `(1 + n * mu) mod 2^wordbits == 0` for the least-significant limb |
| `r2` | heap-allocated `R^2 mod n`, `len` limbs, where `R = 2^(wordbits*len)` |

Precondition for valid contexts: `1 < n` and `n` odd. The context invariant also requires `n < 2^(wordbits*len)`, `n` and `r2` live/disjoint, and `r2 = 2^(2*wordbits*len) mod n`. There is no public copy/free-deep-copy API; shallow copying the struct duplicates internal pointers and can cause double-free or aliasing surprises. Share a context read-only among calls only if your language/runtime guarantees the pointed-to arrays are not mutated or freed concurrently.

## 3. Bignum module dimensions

| Module | Header | Limb type | Normal element limbs | Product/reduction input limbs | Normal byte size | Notes |
|---|---|---|---:|---:|---:|---|
| `Hacl_Bignum32` | `Hacl_Bignum32.h` | `uint32_t` | `len` | `2*len` | `4*len` | context len from call; conversion allocation length is `ceil(byte_len/4)` limbs for the input byte count |
| `Hacl_Bignum64` | `Hacl_Bignum64.h` | `uint64_t` | `len` | `2*len` | `8*len` | context len from call; conversion allocation length is `ceil(byte_len/8)` limbs for the input byte count |
| `Hacl_Bignum256` | `Hacl_Bignum256.h` | `uint64_t` | `4` | `8` | `32` | context len=4; conversion allocation length is `ceil(byte_len/8)` limbs for the input byte count |
| `Hacl_Bignum256_32` | `Hacl_Bignum256_32.h` | `uint32_t` | `8` | `16` | `32` | context len=8; conversion allocation length is `ceil(byte_len/4)` limbs for the input byte count |
| `Hacl_Bignum4096` | `Hacl_Bignum4096.h` | `uint64_t` | `64` | `128` | `512` | context len=64; conversion allocation length is `ceil(byte_len/8)` limbs for the input byte count |
| `Hacl_Bignum4096_32` | `Hacl_Bignum4096_32.h` | `uint32_t` | `128` | `256` | `512` | context len=128; conversion allocation length is `ceil(byte_len/4)` limbs for the input byte count |

For runtime modules, `normal byte size` is `wordbytes * len`, but byte conversion functions independently take a byte count and round it up to limbs.

## 4. Bignum operation shape (applies to all six modules)

The six bignum modules export the same operation set. Runtime modules include `len`; fixed modules bake `len` into the function name/header. Exact prototypes are in §5.

| Operation suffix | Semantics | Input/output sizes | Return value | Preconditions and aliasing | Timing |
|---|---|---|---|---|---|
| `add` | `res = (a + b) mod 2^(wordbits*L)` | `a`, `b`, `res`: `L` limbs | carry limb (`0` or `1`) | Runtime 32-bit header explicitly allows exact aliasing among `a`, `b`, `res`, but no partial overlap. Generic F* addition preconditions are `eq_or_disjoint` for same-size buffers. | fixed loop over public `L` |
| `sub` | `res = (a - b) mod 2^(wordbits*L)` | `a`, `b`, `res`: `L` limbs | borrow/carry limb | Same alias rule as `add`. | fixed loop over public `L` |
| `add_mod` | `res = (a + b) mod n` | `n`, `a`, `b`, `res`: `L` limbs | none | `a < n`, `b < n`; `n` disjoint from `a`, `b`, `res`; `a`, `b`, `res` may be exactly equal pairwise but not partially overlap. | fixed loop over public `L` |
| `sub_mod` | `res = (a - b) mod n` | `n`, `a`, `b`, `res`: `L` limbs | none | `a < n`, `b < n`; same aliasing as `add_mod`. | fixed loop over public `L` |
| `mul` | full product `res = a*b` | `a`, `b`: `L` limbs; `res`: `2L` limbs | none | `res` disjoint from `a` and `b`; `a` and `b` may be the same or disjoint according to F* `eq_or_disjoint`. The 32-bit runtime header says `a`, `b`, and `res` disjoint except exact input equality is allowed by generic multiplication. | fixed loop/algorithm over public `L` |
| `sqr` | full square `res = a*a` | `a`: `L` limbs; `res`: `2L` limbs | none | `res` disjoint from `a`. | fixed loop/algorithm over public `L` |
| `mod` | `res = a mod n` | `a`: `2L` limbs; `n`, `res`: `L` limbs | `true` iff checked preconditions hold; on failure implementation writes zero to `res` | checked: `1 < n`, `n` odd; buffers disjoint (`res` from `a` and `n`, `n` from `a`). | no `_vartime`; modulus/length public |
| `mod_exp_vartime` | `res = a^b mod n` | `n`, `a`, `res`: `L` limbs; `b`: `ceil(bBits/wordbits)` limbs (or zero limbs if `bBits==0` in F* `blocks0`) | `true` iff checked preconditions hold; on failure implementation writes zero to `res` | checked: `n` odd, `1 < n`, `b < 2^bBits`, `a < n`; `res` disjoint from `a`, `b`, `n`; `n` disjoint from `a`. | **variable-time on `b`** |
| `mod_exp_consttime` | `res = a^b mod n` | same as `mod_exp_vartime` | `true` iff checked preconditions hold; on failure zeroes `res` | same as `mod_exp_vartime` | **constant-time over exponent `b`; runtime proportional to public `bBits`** |
| `mod_inv_prime_vartime` | `res = a^(-1) mod n` using prime-modulus exponentiation | `n`, `a`, `res`: `L` limbs | `true` iff runtime-checked preconditions except primality hold; on failure zeroes `res` | verifier-only: `n` prime. Runtime checked: `n` odd, `1 < n`, `0 < a`, `a < n`; disjoint `res`/`n`/`a`. | **variable-time** |
| `mont_ctx_init` | allocate context containing `n`, `mu`, and `r2` | `n`: `L` limbs | pointer or `NULL` on allocation failure (preconditions not fully guarded in all wrappers) | caller must ensure `n` odd and `1 < n`; returned context must be freed with matching `mont_ctx_free`. | setup over public modulus |
| `mont_ctx_free` | free context and internal arrays | context pointer | none | pointer must come from matching init and not already be freed. | n/a |
| `mod_precomp` | `res = a mod context.n` | `a`: `2L`; `res`: `L`; context length `L` | none | context valid; `a` and `res` disjoint; context footprint disjoint from `a`/`res`. | no `_vartime` |
| `mod_exp_vartime_precomp` | `res = a^b mod context.n` | `a`, `res`: `L`; `b`: `ceil(bBits/wordbits)` limbs | none | context valid; `a < n`, `b < 2^bBits`; `res` disjoint from `a`, `b`; context disjoint from `a`, `res`. | **variable-time on `b`** |
| `mod_exp_consttime_precomp` | `res = a^b mod context.n` | same | none | same as precomputed vartime. | **constant-time over exponent `b`** |
| `mod_inv_prime_vartime_precomp` | `res = a^(-1) mod context.n` | `a`, `res`: `L` | none | verifier-only: `n` prime; runtime caller obligation: `0 < a < n`; context valid; `res` disjoint from `a`; context disjoint from both. | **variable-time** |
| `new_bn_from_bytes_be` | allocate limbs for integer encoded big-endian | `b`: `byte_len` bytes; return has `ceil(byte_len/wordbytes)` limbs | pointer or `NULL`; returns `NULL` if `byte_len==0`, allocation fails, or allocation would exceed 4GB | caller frees non-null result. | length public |
| `new_bn_from_bytes_le` | allocate limbs for integer encoded little-endian | same | same | same | length public |
| `bn_to_bytes_be` | serialize low `byte_len` bytes big-endian | `b`: `ceil(byte_len/wordbytes)` limbs; `res`: `byte_len` bytes | none | `b` and `res` disjoint; `byte_len > 0` by F* precondition. | length public |
| `bn_to_bytes_le` | serialize low `byte_len` bytes little-endian | same | none | same. | length public |
| `lt_mask` | all-ones limb if `a < b`, else zero | `a`, `b`: `L` limbs | `2^wordbits-1` or `0` | inputs live; no output buffer. | mask-style comparison |
| `eq_mask` | all-ones limb if `a == b`, else zero | `a`, `b`: `L` limbs | `2^wordbits-1` or `0` | inputs live. | mask-style comparison |

`L` means the module limb count: runtime `len`, fixed 256-bit `4` or `8`, fixed 4096-bit `64` or `128`.

## 5. Complete bignum public prototypes by module

### `Hacl_Bignum32` (`Hacl_Bignum32.h`)

- Limb type: `uint32_t`; word bits: 32.
- Arithmetic `len` argument counts `uint32_t` limbs. `a`, `b`, `n`, and `res` expectations are from §4 with `L=len`.
- Byte loaders allocate `ceil(byte_len/4)` limbs for the requested byte count; normal fixed-size use should pass 4*len bytes.

Function names: `Hacl_Bignum32_add`, `Hacl_Bignum32_sub`, `Hacl_Bignum32_add_mod`, `Hacl_Bignum32_sub_mod`, `Hacl_Bignum32_mul`, `Hacl_Bignum32_sqr`, `Hacl_Bignum32_mod`, `Hacl_Bignum32_mod_exp_vartime`, `Hacl_Bignum32_mod_exp_consttime`, `Hacl_Bignum32_mod_inv_prime_vartime`, `Hacl_Bignum32_mont_ctx_init`, `Hacl_Bignum32_mont_ctx_free`, `Hacl_Bignum32_mod_precomp`, `Hacl_Bignum32_mod_exp_vartime_precomp`, `Hacl_Bignum32_mod_exp_consttime_precomp`, `Hacl_Bignum32_mod_inv_prime_vartime_precomp`, `Hacl_Bignum32_new_bn_from_bytes_be`, `Hacl_Bignum32_new_bn_from_bytes_le`, `Hacl_Bignum32_bn_to_bytes_be`, `Hacl_Bignum32_bn_to_bytes_le`, `Hacl_Bignum32_lt_mask`, `Hacl_Bignum32_eq_mask`.

```c
uint32_t Hacl_Bignum32_add(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

uint32_t Hacl_Bignum32_sub(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum32_add_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum32_sub_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum32_mul(uint32_t len, uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum32_sqr(uint32_t len, uint32_t *a, uint32_t *res);

bool Hacl_Bignum32_mod(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res);

bool
Hacl_Bignum32_mod_exp_vartime(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

bool
Hacl_Bignum32_mod_exp_consttime(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

bool
Hacl_Bignum32_mod_inv_prime_vartime(uint32_t len, uint32_t *n, uint32_t *a, uint32_t *res);

Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
*Hacl_Bignum32_mont_ctx_init(uint32_t len, uint32_t *n);

void Hacl_Bignum32_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

void
Hacl_Bignum32_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
);

void
Hacl_Bignum32_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum32_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum32_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
);

uint32_t *Hacl_Bignum32_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

uint32_t *Hacl_Bignum32_new_bn_from_bytes_le(uint32_t len, uint8_t *b);

void Hacl_Bignum32_bn_to_bytes_be(uint32_t len, uint32_t *b, uint8_t *res);

void Hacl_Bignum32_bn_to_bytes_le(uint32_t len, uint32_t *b, uint8_t *res);

uint32_t Hacl_Bignum32_lt_mask(uint32_t len, uint32_t *a, uint32_t *b);

uint32_t Hacl_Bignum32_eq_mask(uint32_t len, uint32_t *a, uint32_t *b);
```

### `Hacl_Bignum64` (`Hacl_Bignum64.h`)

- Limb type: `uint64_t`; word bits: 64.
- Arithmetic `len` argument counts `uint64_t` limbs. `a`, `b`, `n`, and `res` expectations are from §4 with `L=len`.
- Byte loaders allocate `ceil(byte_len/8)` limbs for the requested byte count; normal fixed-size use should pass 8*len bytes.

Function names: `Hacl_Bignum64_add`, `Hacl_Bignum64_sub`, `Hacl_Bignum64_add_mod`, `Hacl_Bignum64_sub_mod`, `Hacl_Bignum64_mul`, `Hacl_Bignum64_sqr`, `Hacl_Bignum64_mod`, `Hacl_Bignum64_mod_exp_vartime`, `Hacl_Bignum64_mod_exp_consttime`, `Hacl_Bignum64_mod_inv_prime_vartime`, `Hacl_Bignum64_mont_ctx_init`, `Hacl_Bignum64_mont_ctx_free`, `Hacl_Bignum64_mod_precomp`, `Hacl_Bignum64_mod_exp_vartime_precomp`, `Hacl_Bignum64_mod_exp_consttime_precomp`, `Hacl_Bignum64_mod_inv_prime_vartime_precomp`, `Hacl_Bignum64_new_bn_from_bytes_be`, `Hacl_Bignum64_new_bn_from_bytes_le`, `Hacl_Bignum64_bn_to_bytes_be`, `Hacl_Bignum64_bn_to_bytes_le`, `Hacl_Bignum64_lt_mask`, `Hacl_Bignum64_eq_mask`.

```c
uint64_t Hacl_Bignum64_add(uint32_t len, uint64_t *a, uint64_t *b, uint64_t *res);

uint64_t Hacl_Bignum64_sub(uint32_t len, uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum64_add_mod(uint32_t len, uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum64_sub_mod(uint32_t len, uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum64_mul(uint32_t len, uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum64_sqr(uint32_t len, uint64_t *a, uint64_t *res);

bool Hacl_Bignum64_mod(uint32_t len, uint64_t *n, uint64_t *a, uint64_t *res);

bool
Hacl_Bignum64_mod_exp_vartime(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

bool
Hacl_Bignum64_mod_exp_consttime(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

bool
Hacl_Bignum64_mod_inv_prime_vartime(uint32_t len, uint64_t *n, uint64_t *a, uint64_t *res);

Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
*Hacl_Bignum64_mont_ctx_init(uint32_t len, uint64_t *n);

void Hacl_Bignum64_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k);

void
Hacl_Bignum64_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
);

void
Hacl_Bignum64_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum64_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum64_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
);

uint64_t *Hacl_Bignum64_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

uint64_t *Hacl_Bignum64_new_bn_from_bytes_le(uint32_t len, uint8_t *b);

void Hacl_Bignum64_bn_to_bytes_be(uint32_t len, uint64_t *b, uint8_t *res);

void Hacl_Bignum64_bn_to_bytes_le(uint32_t len, uint64_t *b, uint8_t *res);

uint64_t Hacl_Bignum64_lt_mask(uint32_t len, uint64_t *a, uint64_t *b);

uint64_t Hacl_Bignum64_eq_mask(uint32_t len, uint64_t *a, uint64_t *b);
```

### `Hacl_Bignum256` (`Hacl_Bignum256.h`)

- Limb type: `uint64_t`; word bits: 64.
- Fixed bignum is 32 bytes: normal values are `uint64_t[4]`; full products/reduction inputs are `uint64_t[8]`.
- Byte loaders allocate `ceil(byte_len/8)` limbs for the requested byte count; normal fixed-size use should pass 32 bytes.

Function names: `Hacl_Bignum256_add`, `Hacl_Bignum256_sub`, `Hacl_Bignum256_add_mod`, `Hacl_Bignum256_sub_mod`, `Hacl_Bignum256_mul`, `Hacl_Bignum256_sqr`, `Hacl_Bignum256_mod`, `Hacl_Bignum256_mod_exp_vartime`, `Hacl_Bignum256_mod_exp_consttime`, `Hacl_Bignum256_mod_inv_prime_vartime`, `Hacl_Bignum256_mont_ctx_init`, `Hacl_Bignum256_mont_ctx_free`, `Hacl_Bignum256_mod_precomp`, `Hacl_Bignum256_mod_exp_vartime_precomp`, `Hacl_Bignum256_mod_exp_consttime_precomp`, `Hacl_Bignum256_mod_inv_prime_vartime_precomp`, `Hacl_Bignum256_new_bn_from_bytes_be`, `Hacl_Bignum256_new_bn_from_bytes_le`, `Hacl_Bignum256_bn_to_bytes_be`, `Hacl_Bignum256_bn_to_bytes_le`, `Hacl_Bignum256_lt_mask`, `Hacl_Bignum256_eq_mask`.

```c
uint64_t Hacl_Bignum256_add(uint64_t *a, uint64_t *b, uint64_t *res);

uint64_t Hacl_Bignum256_sub(uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum256_add_mod(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum256_sub_mod(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum256_mul(uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum256_sqr(uint64_t *a, uint64_t *res);

bool Hacl_Bignum256_mod(uint64_t *n, uint64_t *a, uint64_t *res);

bool
Hacl_Bignum256_mod_exp_vartime(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

bool
Hacl_Bignum256_mod_exp_consttime(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

bool Hacl_Bignum256_mod_inv_prime_vartime(uint64_t *n, uint64_t *a, uint64_t *res);

Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *Hacl_Bignum256_mont_ctx_init(uint64_t *n);

void Hacl_Bignum256_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k);

void
Hacl_Bignum256_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
);

void
Hacl_Bignum256_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum256_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum256_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
);

uint64_t *Hacl_Bignum256_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

uint64_t *Hacl_Bignum256_new_bn_from_bytes_le(uint32_t len, uint8_t *b);

void Hacl_Bignum256_bn_to_bytes_be(uint64_t *b, uint8_t *res);

void Hacl_Bignum256_bn_to_bytes_le(uint64_t *b, uint8_t *res);

uint64_t Hacl_Bignum256_lt_mask(uint64_t *a, uint64_t *b);

uint64_t Hacl_Bignum256_eq_mask(uint64_t *a, uint64_t *b);
```

### `Hacl_Bignum256_32` (`Hacl_Bignum256_32.h`)

- Limb type: `uint32_t`; word bits: 32.
- Fixed bignum is 32 bytes: normal values are `uint32_t[8]`; full products/reduction inputs are `uint32_t[16]`.
- Byte loaders allocate `ceil(byte_len/4)` limbs for the requested byte count; normal fixed-size use should pass 32 bytes.

Function names: `Hacl_Bignum256_32_add`, `Hacl_Bignum256_32_sub`, `Hacl_Bignum256_32_add_mod`, `Hacl_Bignum256_32_sub_mod`, `Hacl_Bignum256_32_mul`, `Hacl_Bignum256_32_sqr`, `Hacl_Bignum256_32_mod`, `Hacl_Bignum256_32_mod_exp_vartime`, `Hacl_Bignum256_32_mod_exp_consttime`, `Hacl_Bignum256_32_mod_inv_prime_vartime`, `Hacl_Bignum256_32_mont_ctx_init`, `Hacl_Bignum256_32_mont_ctx_free`, `Hacl_Bignum256_32_mod_precomp`, `Hacl_Bignum256_32_mod_exp_vartime_precomp`, `Hacl_Bignum256_32_mod_exp_consttime_precomp`, `Hacl_Bignum256_32_mod_inv_prime_vartime_precomp`, `Hacl_Bignum256_32_new_bn_from_bytes_be`, `Hacl_Bignum256_32_new_bn_from_bytes_le`, `Hacl_Bignum256_32_bn_to_bytes_be`, `Hacl_Bignum256_32_bn_to_bytes_le`, `Hacl_Bignum256_32_lt_mask`, `Hacl_Bignum256_32_eq_mask`.

```c
uint32_t Hacl_Bignum256_32_add(uint32_t *a, uint32_t *b, uint32_t *res);

uint32_t Hacl_Bignum256_32_sub(uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum256_32_add_mod(uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum256_32_sub_mod(uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum256_32_mul(uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum256_32_sqr(uint32_t *a, uint32_t *res);

bool Hacl_Bignum256_32_mod(uint32_t *n, uint32_t *a, uint32_t *res);

bool
Hacl_Bignum256_32_mod_exp_vartime(
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

bool
Hacl_Bignum256_32_mod_exp_consttime(
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

bool Hacl_Bignum256_32_mod_inv_prime_vartime(uint32_t *n, uint32_t *a, uint32_t *res);

Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *Hacl_Bignum256_32_mont_ctx_init(uint32_t *n);

void Hacl_Bignum256_32_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

void
Hacl_Bignum256_32_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
);

void
Hacl_Bignum256_32_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum256_32_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum256_32_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
);

uint32_t *Hacl_Bignum256_32_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

uint32_t *Hacl_Bignum256_32_new_bn_from_bytes_le(uint32_t len, uint8_t *b);

void Hacl_Bignum256_32_bn_to_bytes_be(uint32_t *b, uint8_t *res);

void Hacl_Bignum256_32_bn_to_bytes_le(uint32_t *b, uint8_t *res);

uint32_t Hacl_Bignum256_32_lt_mask(uint32_t *a, uint32_t *b);

uint32_t Hacl_Bignum256_32_eq_mask(uint32_t *a, uint32_t *b);
```

### `Hacl_Bignum4096` (`Hacl_Bignum4096.h`)

- Limb type: `uint64_t`; word bits: 64.
- Fixed bignum is 512 bytes: normal values are `uint64_t[64]`; full products/reduction inputs are `uint64_t[128]`.
- Byte loaders allocate `ceil(byte_len/8)` limbs for the requested byte count; normal fixed-size use should pass 512 bytes.

Function names: `Hacl_Bignum4096_add`, `Hacl_Bignum4096_sub`, `Hacl_Bignum4096_add_mod`, `Hacl_Bignum4096_sub_mod`, `Hacl_Bignum4096_mul`, `Hacl_Bignum4096_sqr`, `Hacl_Bignum4096_mod`, `Hacl_Bignum4096_mod_exp_vartime`, `Hacl_Bignum4096_mod_exp_consttime`, `Hacl_Bignum4096_mod_inv_prime_vartime`, `Hacl_Bignum4096_mont_ctx_init`, `Hacl_Bignum4096_mont_ctx_free`, `Hacl_Bignum4096_mod_precomp`, `Hacl_Bignum4096_mod_exp_vartime_precomp`, `Hacl_Bignum4096_mod_exp_consttime_precomp`, `Hacl_Bignum4096_mod_inv_prime_vartime_precomp`, `Hacl_Bignum4096_new_bn_from_bytes_be`, `Hacl_Bignum4096_new_bn_from_bytes_le`, `Hacl_Bignum4096_bn_to_bytes_be`, `Hacl_Bignum4096_bn_to_bytes_le`, `Hacl_Bignum4096_lt_mask`, `Hacl_Bignum4096_eq_mask`.

```c
uint64_t Hacl_Bignum4096_add(uint64_t *a, uint64_t *b, uint64_t *res);

uint64_t Hacl_Bignum4096_sub(uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum4096_add_mod(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum4096_sub_mod(uint64_t *n, uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum4096_mul(uint64_t *a, uint64_t *b, uint64_t *res);

void Hacl_Bignum4096_sqr(uint64_t *a, uint64_t *res);

bool Hacl_Bignum4096_mod(uint64_t *n, uint64_t *a, uint64_t *res);

bool
Hacl_Bignum4096_mod_exp_vartime(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

bool
Hacl_Bignum4096_mod_exp_consttime(
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

bool Hacl_Bignum4096_mod_inv_prime_vartime(uint64_t *n, uint64_t *a, uint64_t *res);

Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *Hacl_Bignum4096_mont_ctx_init(uint64_t *n);

void Hacl_Bignum4096_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k);

void
Hacl_Bignum4096_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
);

void
Hacl_Bignum4096_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum4096_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum4096_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *res
);

uint64_t *Hacl_Bignum4096_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

uint64_t *Hacl_Bignum4096_new_bn_from_bytes_le(uint32_t len, uint8_t *b);

void Hacl_Bignum4096_bn_to_bytes_be(uint64_t *b, uint8_t *res);

void Hacl_Bignum4096_bn_to_bytes_le(uint64_t *b, uint8_t *res);

uint64_t Hacl_Bignum4096_lt_mask(uint64_t *a, uint64_t *b);

uint64_t Hacl_Bignum4096_eq_mask(uint64_t *a, uint64_t *b);
```

### `Hacl_Bignum4096_32` (`Hacl_Bignum4096_32.h`)

- Limb type: `uint32_t`; word bits: 32.
- Fixed bignum is 512 bytes: normal values are `uint32_t[128]`; full products/reduction inputs are `uint32_t[256]`.
- Byte loaders allocate `ceil(byte_len/4)` limbs for the requested byte count; normal fixed-size use should pass 512 bytes.

Function names: `Hacl_Bignum4096_32_add`, `Hacl_Bignum4096_32_sub`, `Hacl_Bignum4096_32_add_mod`, `Hacl_Bignum4096_32_sub_mod`, `Hacl_Bignum4096_32_mul`, `Hacl_Bignum4096_32_sqr`, `Hacl_Bignum4096_32_mod`, `Hacl_Bignum4096_32_mod_exp_vartime`, `Hacl_Bignum4096_32_mod_exp_consttime`, `Hacl_Bignum4096_32_mod_inv_prime_vartime`, `Hacl_Bignum4096_32_mont_ctx_init`, `Hacl_Bignum4096_32_mont_ctx_free`, `Hacl_Bignum4096_32_mod_precomp`, `Hacl_Bignum4096_32_mod_exp_vartime_precomp`, `Hacl_Bignum4096_32_mod_exp_consttime_precomp`, `Hacl_Bignum4096_32_mod_inv_prime_vartime_precomp`, `Hacl_Bignum4096_32_new_bn_from_bytes_be`, `Hacl_Bignum4096_32_new_bn_from_bytes_le`, `Hacl_Bignum4096_32_bn_to_bytes_be`, `Hacl_Bignum4096_32_bn_to_bytes_le`, `Hacl_Bignum4096_32_lt_mask`, `Hacl_Bignum4096_32_eq_mask`.

```c
uint32_t Hacl_Bignum4096_32_add(uint32_t *a, uint32_t *b, uint32_t *res);

uint32_t Hacl_Bignum4096_32_sub(uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum4096_32_add_mod(uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum4096_32_sub_mod(uint32_t *n, uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum4096_32_mul(uint32_t *a, uint32_t *b, uint32_t *res);

void Hacl_Bignum4096_32_sqr(uint32_t *a, uint32_t *res);

bool Hacl_Bignum4096_32_mod(uint32_t *n, uint32_t *a, uint32_t *res);

bool
Hacl_Bignum4096_32_mod_exp_vartime(
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

bool
Hacl_Bignum4096_32_mod_exp_consttime(
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

bool Hacl_Bignum4096_32_mod_inv_prime_vartime(uint32_t *n, uint32_t *a, uint32_t *res);

Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *Hacl_Bignum4096_32_mont_ctx_init(uint32_t *n);

void Hacl_Bignum4096_32_mont_ctx_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

void
Hacl_Bignum4096_32_mod_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
);

void
Hacl_Bignum4096_32_mod_exp_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum4096_32_mod_exp_consttime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum4096_32_mod_inv_prime_vartime_precomp(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *res
);

uint32_t *Hacl_Bignum4096_32_new_bn_from_bytes_be(uint32_t len, uint8_t *b);

uint32_t *Hacl_Bignum4096_32_new_bn_from_bytes_le(uint32_t len, uint8_t *b);

void Hacl_Bignum4096_32_bn_to_bytes_be(uint32_t *b, uint8_t *res);

void Hacl_Bignum4096_32_bn_to_bytes_le(uint32_t *b, uint8_t *res);

uint32_t Hacl_Bignum4096_32_lt_mask(uint32_t *a, uint32_t *b);

uint32_t Hacl_Bignum4096_32_eq_mask(uint32_t *a, uint32_t *b);
```

## 6. Generic Montgomery field API

The generic-field modules are a higher-level Montgomery-domain workflow around the same `Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32/u64` context. All field elements are `len` limbs, where `len = Hacl_GenericField*_field_get_len(k)` after initialization. The modulus `n` is part of the context. All arithmetic inputs named `aM`, `bM`, `cM`, `resM`, `oneM`, or `aInvM` are in Montgomery representation and maintain the invariant `< n`.

Workflow:

1. Call `field_modulus_check(len, n)` if you want a runtime validation that `1 < n` and `n` is odd.
2. Call `field_init(len, n)` to allocate a context. Caller must still ensure the modulus preconditions; returns a context pointer (or `NULL` on allocation failure in generated C paths).
3. Convert regular values with `to_field(k, a, aM)`, compute using field operations, and convert back with `from_field(k, aM, a)`.
4. Free with the matching `field_free(k)`.

Context sharing/copying: the context struct is public but not abstract in C. It owns heap arrays `n` and `r2`; do not shallow-copy it if both copies may be freed. Treat it as immutable and share by pointer only with external synchronization/lifetime discipline.

| Field operation | Semantics and sizes | Preconditions and aliasing | Timing |
|---|---|---|---|
| `field_modulus_check` | returns `true` iff `n` (`len` limbs) is usable: odd and `1 < n` | live `n`; no allocation | fixed check over public `len` |
| `field_init` | allocates context for `n` (`len` limbs), copying modulus and precomputing `mu`, `r2` | caller must ensure odd `n`, `1 < n`; caller frees | setup |
| `field_free` | frees context and internal arrays | valid matching context | n/a |
| `field_get_len` | returns context `len` in limbs | valid context | n/a |
| `to_field` | writes `a * R mod n` to `aM`; `a`, `aM`: `len` limbs | `a` and `aM` disjoint; context footprint disjoint from both. `a` need not be `< n` because result is reduced. | Montgomery conversion |
| `from_field` | writes `aM / R mod n` to `a`; both `len` limbs | `aM < n`; `aM` and `a` disjoint; context disjoint. | Montgomery conversion |
| `add`/`sub` | field addition/subtraction in Montgomery domain; all operands `len` limbs | inputs `< n`; exact aliasing among field operand/result buffers allowed by `eq_or_disjoint`; context disjoint. | fixed loop |
| `mul` | field multiplication in Montgomery domain | inputs `< n`; exact aliasing among `aM`, `bM`, `cM` allowed by F* precondition; context disjoint. | fixed loop over public len |
| `sqr` | field squaring in Montgomery domain | `aM < n`; `aM` and `cM` may be exactly equal or disjoint; context disjoint. | fixed loop |
| `one` | writes Montgomery representation of 1 | output `len` limbs, context disjoint | fixed |
| `exp_consttime` | writes `aM^b mod n` in Montgomery domain | `aM < n`, `b < 2^bBits`; `b` is `ceil(bBits/wordbits)` limbs; `resM` disjoint from `aM` and `b`; `aM` disjoint from `b`; context disjoint from `aM`/`resM`. | **constant-time over `b`** |
| `exp_vartime` | same as exponentiation | same | **variable-time on `b`** |
| `inverse` | writes `aM^(-1) mod n` in Montgomery domain | verifier-only: `n` prime; caller: `0 < aM < n`; `aM` and `aInvM` disjoint; context disjoint. | implemented via variable-time exponentiation; treat as **variable-time** |

### `Hacl_GenericField32` (`Hacl_GenericField32.h`)

- Limb type: `uint32_t`; field element buffers hold `len` limbs; exponent buffer `b` holds `ceil(bBits/32)` limbs for `bBits`.
Function names: `Hacl_GenericField32_field_modulus_check`, `Hacl_GenericField32_field_init`, `Hacl_GenericField32_field_free`, `Hacl_GenericField32_field_get_len`, `Hacl_GenericField32_to_field`, `Hacl_GenericField32_from_field`, `Hacl_GenericField32_add`, `Hacl_GenericField32_sub`, `Hacl_GenericField32_mul`, `Hacl_GenericField32_sqr`, `Hacl_GenericField32_one`, `Hacl_GenericField32_exp_consttime`, `Hacl_GenericField32_exp_vartime`, `Hacl_GenericField32_inverse`.

```c
bool Hacl_GenericField32_field_modulus_check(uint32_t len, uint32_t *n);

Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32
*Hacl_GenericField32_field_init(uint32_t len, uint32_t *n);

void Hacl_GenericField32_field_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

uint32_t Hacl_GenericField32_field_get_len(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k);

void
Hacl_GenericField32_to_field(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *a,
  uint32_t *aM
);

void
Hacl_GenericField32_from_field(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *a
);

void
Hacl_GenericField32_add(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *cM
);

void
Hacl_GenericField32_sub(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *cM
);

void
Hacl_GenericField32_mul(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *cM
);

void
Hacl_GenericField32_sqr(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *cM
);

void Hacl_GenericField32_one(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k, uint32_t *oneM);

void
Hacl_GenericField32_exp_consttime(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *resM
);

void
Hacl_GenericField32_exp_vartime(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *resM
);

void
Hacl_GenericField32_inverse(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u32 *k,
  uint32_t *aM,
  uint32_t *aInvM
);
```

### `Hacl_GenericField64` (`Hacl_GenericField64.h`)

- Limb type: `uint64_t`; field element buffers hold `len` limbs; exponent buffer `b` holds `ceil(bBits/64)` limbs for `bBits`.
Function names: `Hacl_GenericField64_field_modulus_check`, `Hacl_GenericField64_field_init`, `Hacl_GenericField64_field_free`, `Hacl_GenericField64_field_get_len`, `Hacl_GenericField64_to_field`, `Hacl_GenericField64_from_field`, `Hacl_GenericField64_add`, `Hacl_GenericField64_sub`, `Hacl_GenericField64_mul`, `Hacl_GenericField64_sqr`, `Hacl_GenericField64_one`, `Hacl_GenericField64_exp_consttime`, `Hacl_GenericField64_exp_vartime`, `Hacl_GenericField64_inverse`.

```c
bool Hacl_GenericField64_field_modulus_check(uint32_t len, uint64_t *n);

Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64
*Hacl_GenericField64_field_init(uint32_t len, uint64_t *n);

void Hacl_GenericField64_field_free(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k);

uint32_t Hacl_GenericField64_field_get_len(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k);

void
Hacl_GenericField64_to_field(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *a,
  uint64_t *aM
);

void
Hacl_GenericField64_from_field(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *a
);

void
Hacl_GenericField64_add(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
);

void
Hacl_GenericField64_sub(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
);

void
Hacl_GenericField64_mul(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *cM
);

void
Hacl_GenericField64_sqr(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *cM
);

void Hacl_GenericField64_one(Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k, uint64_t *oneM);

void
Hacl_GenericField64_exp_consttime(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *resM
);

void
Hacl_GenericField64_exp_vartime(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *resM
);

void
Hacl_GenericField64_inverse(
  Hacl_Bignum_MontArithmetic_bn_mont_ctx_u64 *k,
  uint64_t *aM,
  uint64_t *aInvM
);
```

## 7. RSA-PSS (`Hacl_RSAPSS.h`)

RSA-PSS is built on 64-bit bignums. Public and secret keys are flat `uint64_t` arrays produced by load functions. They are opaque at the API level even though the packing is observable in generated code.

### RSA-PSS bit/byte sizes and key packing

Let:

- `nLen = ceil(modBits / 64)` limbs, `nBytes = ceil(modBits / 8)` bytes.
- `eLen = ceil(eBits / 64)` limbs, `eBytes = ceil(eBits / 8)` bytes.
- `dLen = ceil(dBits / 64)` limbs, `dBytes = ceil(dBits / 8)` bytes.

Generated header comments for `eb`/`db` say `ceil(modBits/8)` in a few places, but the F* source and generated C actually read `ceil(eBits/8)` bytes for `eb` and `ceil(dBits/8)` bytes for `db`. For reimplementation, use the bit count associated with each integer.

| Key | C type and length | Packing | Validation |
|---|---|---|---|
| Public key | `uint64_t[pkeyLen]`, `pkeyLen = nLen + nLen + eLen` | `[n (nLen); r2 (nLen); e (eLen)]` | `modBits > 1`, `eBits > 0`, allocation bounds; `n` odd; `2^(modBits-1) < n < 2^modBits`; `0 < e < 2^eBits`; `r2 = 2^(2*64*nLen) mod n` with exponent bit bound `modBits-1` |
| Secret key | `uint64_t[skeyLen]`, `skeyLen = nLen + nLen + eLen + dLen` | `[n; r2; e; d]` | public-key validation plus `dBits > 0`, `0 < d < 2^dBits` |

The byte inputs `nb`, `eb`, and `db` are big-endian. Successful `new_rsapss_load_*` results are heap allocated and caller-freed; invalid key parts or allocation failure return `NULL`.

### Hash and salt conventions

- Hash selector type is `Spec_Hash_Definitions_hash_alg` from `Hacl_Streaming_Types.h`. Allowed RSA-PSS values are `Spec_Hash_Definitions_SHA2_256`, `Spec_Hash_Definitions_SHA2_384`, and `Spec_Hash_Definitions_SHA2_512`.
- Salt is caller-supplied: signing reads exactly `saltLen` bytes from `salt`; verification takes the expected `saltLen` and checks the encoded PSS salt length accordingly.
- PSS signing preconditions include `saltLen + hashLen + 2 <= ceil((modBits - 1)/8)` and input-length bounds for the selected hash. Runtime functions return `false` when these checks fail.
- Signature output/input size is `ceil(modBits/8)` bytes. `rsapss_verify` additionally requires `sgntLen == ceil(modBits/8)` or returns `false`.

### RSA-PSS prototypes

Function names: `Hacl_RSAPSS_rsapss_sign`, `Hacl_RSAPSS_rsapss_verify`, `Hacl_RSAPSS_new_rsapss_load_pkey`, `Hacl_RSAPSS_new_rsapss_load_skey`, `Hacl_RSAPSS_rsapss_skey_sign`, `Hacl_RSAPSS_rsapss_pkey_verify`, `Hacl_RSAPSS_mgf_hash`.

```c
bool
Hacl_RSAPSS_rsapss_sign(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint64_t *skey,
  uint32_t saltLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
);

bool
Hacl_RSAPSS_rsapss_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint64_t *pkey,
  uint32_t saltLen,
  uint32_t sgntLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
);

uint64_t
*Hacl_RSAPSS_new_rsapss_load_pkey(uint32_t modBits, uint32_t eBits, uint8_t *nb, uint8_t *eb);

uint64_t
*Hacl_RSAPSS_new_rsapss_load_skey(
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db
);

bool
Hacl_RSAPSS_rsapss_skey_sign(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint32_t dBits,
  uint8_t *nb,
  uint8_t *eb,
  uint8_t *db,
  uint32_t saltLen,
  uint8_t *salt,
  uint32_t msgLen,
  uint8_t *msg,
  uint8_t *sgnt
);

bool
Hacl_RSAPSS_rsapss_pkey_verify(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t modBits,
  uint32_t eBits,
  uint8_t *nb,
  uint8_t *eb,
  uint32_t saltLen,
  uint32_t sgntLen,
  uint8_t *sgnt,
  uint32_t msgLen,
  uint8_t *msg
);

void
Hacl_RSAPSS_mgf_hash(
  Spec_Hash_Definitions_hash_alg a,
  uint32_t len,
  uint8_t *mgfseed,
  uint32_t maskLen,
  uint8_t *res
);
```

### RSA-PSS function inventory

| Function | Semantics | Arguments and lengths | Return/side effects | Timing notes |
|---|---|---|---|---|
| `Hacl_RSAPSS_rsapss_sign` | Sign `msg` using a pre-loaded secret key. Performs PSS encode, private exponentiation, and a public-exponent self-check before releasing signature. | `skey`: `uint64_t[skeyLen]` from `new_rsapss_load_skey`; `salt`: `saltLen`; `msg`: `msgLen`; `sgnt`: `ceil(modBits/8)` bytes. | `true` iff signing succeeds; writes `sgnt` on success. | private exponent uses constant-time exponentiation; public self-check uses variable-time public exponent. |
| `Hacl_RSAPSS_rsapss_verify` | Verify `sgnt` using a pre-loaded public key. | `pkey`: `uint64_t[pkeyLen]`; `sgnt`: `sgntLen` bytes; `msg`: `msgLen`; expected salt length `saltLen`. | `true` iff valid; requires `sgntLen == ceil(modBits/8)`. | public exponent is variable-time and assumed public. |
| `Hacl_RSAPSS_new_rsapss_load_pkey` | Allocate and load public key from big-endian `n` and `e`. | `nb`: `ceil(modBits/8)` bytes; `eb`: `ceil(eBits/8)` bytes. | pointer to `[n;r2;e]`, or `NULL`; caller frees. | key validation over public key material. |
| `Hacl_RSAPSS_new_rsapss_load_skey` | Allocate and load secret key from big-endian `n`, `e`, `d`. | `nb`: `ceil(modBits/8)`; `eb`: `ceil(eBits/8)`; `db`: `ceil(dBits/8)`. | pointer to `[n;r2;e;d]`, or `NULL`; caller frees. | key validation includes secret `d` bit-length/nonzero check. |
| `Hacl_RSAPSS_rsapss_skey_sign` | Convenience sign: load key into a stack array, sign, discard stack key. | byte key parts as above; `salt`, `msg`, `sgnt` as for sign. | `true` iff key load and sign succeed. | same signing timing. |
| `Hacl_RSAPSS_rsapss_pkey_verify` | Convenience verify: load public key into a stack array, verify. | byte public key parts as above; `sgnt`, `msg` as for verify. | `true` iff key load and verify succeed. | same verify timing. |
| `Hacl_RSAPSS_mgf_hash` | MGF1-style mask generation for PKCS #1 PSS. | `mgfseed`: `len` bytes; `res`: `maskLen` bytes. | writes mask to `res`; no boolean validation return. | hash-loop count depends on public `maskLen`. |

## 8. FFDHE (`Hacl_FFDHE.h`)

FFDHE implements RFC-style finite-field Diffie-Hellman over named safe-prime groups. Inputs and outputs are fixed-length big-endian byte strings of the group size. The implementation uses 64-bit bignums and Montgomery precomputation of the group modulus.

### Supported groups

Enum constants come from `Hacl_Spec.h`:

```c
#define Spec_FFDHE_FFDHE2048 0
#define Spec_FFDHE_FFDHE3072 1
#define Spec_FFDHE_FFDHE4096 2
#define Spec_FFDHE_FFDHE6144 3
#define Spec_FFDHE_FFDHE8192 4
typedef uint8_t Spec_FFDHE_ffdhe_alg;
```

| Constant | Prime size | `Hacl_FFDHE_ffdhe_len` bytes | `uint64_t` modulus limbs `nLen` | precomp `p_r2_n` limbs |
|---|---:|---:|---:|---:|
| `Spec_FFDHE_FFDHE2048` | 2048 | 256 | 32 | 64 |
| `Spec_FFDHE_FFDHE3072` | 3072 | 384 | 48 | 96 |
| `Spec_FFDHE_FFDHE4096` | 4096 | 512 | 64 | 128 |
| `Spec_FFDHE_FFDHE6144` | 6144 | 768 | 96 | 192 |
| `Spec_FFDHE_FFDHE8192` | 8192 | 1024 | 128 | 256 |

The generator is `g = 2` (internal constant `ffdhe_g2`). Public keys and shared secrets are big-endian byte strings of exactly the group byte length.

### FFDHE prototypes

Function names: `Hacl_FFDHE_ffdhe_len`, `Hacl_FFDHE_new_ffdhe_precomp_p`, `Hacl_FFDHE_ffdhe_secret_to_public_precomp`, `Hacl_FFDHE_ffdhe_secret_to_public`, `Hacl_FFDHE_ffdhe_shared_secret_precomp`, `Hacl_FFDHE_ffdhe_shared_secret`.

```c
uint32_t Hacl_FFDHE_ffdhe_len(Spec_FFDHE_ffdhe_alg a);

uint64_t *Hacl_FFDHE_new_ffdhe_precomp_p(Spec_FFDHE_ffdhe_alg a);

void
Hacl_FFDHE_ffdhe_secret_to_public_precomp(
  Spec_FFDHE_ffdhe_alg a,
  uint64_t *p_r2_n,
  uint8_t *sk,
  uint8_t *pk
);

void Hacl_FFDHE_ffdhe_secret_to_public(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk);

uint64_t
Hacl_FFDHE_ffdhe_shared_secret_precomp(
  Spec_FFDHE_ffdhe_alg a,
  uint64_t *p_r2_n,
  uint8_t *sk,
  uint8_t *pk,
  uint8_t *ss
);

uint64_t
Hacl_FFDHE_ffdhe_shared_secret(Spec_FFDHE_ffdhe_alg a, uint8_t *sk, uint8_t *pk, uint8_t *ss);
```

### FFDHE function inventory

| Function | Semantics | Arguments and lengths | Return/validation | Timing notes |
|---|---|---|---|---|
| `Hacl_FFDHE_ffdhe_len` | Return byte length for named group. | `a`: one of the `Spec_FFDHE_*` constants. | `256`, `384`, `512`, `768`, or `1024`. Behavior for out-of-range enum is not specified by the public contract. | public. |
| `Hacl_FFDHE_new_ffdhe_precomp_p` | Allocate precomputed modulus buffer. | Returns `uint64_t[2*nLen]` storing `[p (nLen); r2 (nLen)]`. | pointer or `NULL`; caller frees. | setup over public group. |
| `Hacl_FFDHE_ffdhe_secret_to_public_precomp` | Compute public key `pk = 2^sk mod p` using caller-supplied precomp. | `p_r2_n`: `2*nLen` limbs for same group; `sk`: `len` bytes; `pk`: `len` bytes. | no runtime boolean; F* precondition requires big-endian integer `sk > 1`; writes `pk`. | exponentiation uses constant-time precomputed path over fixed group size. |
| `Hacl_FFDHE_ffdhe_secret_to_public` | Same, but computes precomp on stack for the call. | `sk`: group byte length; `pk`: group byte length. | no runtime boolean; caller must ensure `sk > 1`; writes `pk`. | constant-time exponentiation path. |
| `Hacl_FFDHE_ffdhe_shared_secret_precomp` | Validate peer public key then compute `ss = pk^sk mod p`. | `p_r2_n`: `2*nLen`; `sk`, `pk`, `ss`: group byte length. | returns `0xffffffffffffffff` if `1 < pk < p-1`, otherwise `0`; writes `ss` only on valid peer key. F* precondition requires `sk > 1`. | constant-time exponentiation only after validation; validation result is public/error path. |
| `Hacl_FFDHE_ffdhe_shared_secret` | Same, but computes precomp on stack. | `sk`, `pk`, `ss`: group byte length. | same all-ones/zero mask return; writes `ss` only on valid peer key. | same. |

Validation behavior: public-key validation rejects `pk <= 1` and `pk >= p-1`. Secret-key validation is not a returned error; `sk > 1` is a caller obligation from the F* precondition. There is no random key generation function in `Hacl_FFDHE.h`; callers provide a secret byte string of the named-group length and call `secret_to_public` to derive the public key.

## 9. Notes for reimplementers

- **Six near-identical modules are intentional.** `Hacl_Bignum32/64` are runtime-length; `Hacl_Bignum256*` and `Hacl_Bignum4096*` are fixed instantiations. Do not infer semantic differences from names beyond size and limb width.
- **Most sizes are limbs, not bytes.** Arithmetic `len` is a limb count; conversion `len` is bytes; RSA sizes are bits; FFDHE `ffdhe_len` is bytes. Mixing these is the easiest source of buffer bugs.
- **Little-endian limbs, explicit byte endianness.** Internally limb 0 is least significant. External byte functions are explicit big- or little-endian and may handle non-multiple-of-word byte counts by zero-padding/truncating at the high end.
- **Allocation exists in this corner of HACL*.** Many HACL APIs are caller-buffer-only, but bignum conversion, Montgomery context init, RSA key loading, and FFDHE precomp allocate. Preserve `NULL` failure behavior and caller-free ownership.
- **Context structs are public but ownership-sensitive.** A C caller can see `len`, `n`, `mu`, `r2`, but public free functions assume the exact allocation topology. A safer reimplementation should make the context abstract or use reference-counted/owned arrays.
- **Variable-time is part of the API surface.** `_vartime` suffixes are not naming noise. Use consttime variants for secret exponents. RSA verify/public exponent and public-key validation may be variable-time because inputs are public; RSA private signing and FFDHE secret exponentiation use constant-time exponentiation paths.
- **Prime-modulus inverse trusts a proof precondition.** `mod_inv_prime_vartime` returns `false` for oddness/range failures, but it does not perform a primality test. Generic-field `inverse` has no boolean return and also assumes `n` prime and `aM != 0`.
- **Precomputed functions usually stop checking.** The non-precomputed safe bignum functions validate modulus/range and return `bool`; the `_precomp` versions assume their context is valid and have `void` return. Generic-field operations follow the same assumption-heavy style after `field_init`.
- **RSA keys are flat arrays.** The API does not expose a struct with named fields; callers pass `uint64_t *`. Reimplementations can use a structured type internally, but the C-compatible ABI must preserve `[n;r2;e]` and `[n;r2;e;d]` if interoperating with this API.
- **RSA header comments have a length typo.** The public header says `eb`/`db` point to `ceil(modBits/8)` bytes in load/convenience functions. Generated C and F* preconditions read `ceil(eBits/8)` and `ceil(dBits/8)`. Document this if you expose an API compatible with HACL*.
- **FFDHE has no RNG/keygen API.** “Key-pair generation” means caller obtains a valid secret by other means, then computes public key with `ffdhe_secret_to_public*`. Peer public-key validation happens in shared-secret functions; local secret validity is a caller precondition.
- **Failure output buffers are not uniformly specified.** Safe bignum functions zero `res` on failed runtime checks in generated code. RSA/FFDHE boolean failures should not be treated as producing a meaningful output; FFDHE shared secret does not write `ss` when peer validation fails.
- **Out-of-range enum behavior is not a cryptographic contract.** Generated `match`/C switch code is intended for known `Spec_FFDHE_*` and hash constants. Validate enum values at language boundaries.

## 10. Quick checklist for compatible reimplementation

- Preserve least-significant-limb-first bignum arrays.
- Preserve exact byte serialization results for non-word-multiple lengths.
- Preserve all buffer length formulas and boolean/mask return conventions.
- Preserve `NULL` on allocation/validation failure for `new_*` APIs.
- Make constant-time/variable-time choices explicit in types or names.
- Avoid silently accepting invalid Montgomery moduli; require odd `n > 1`.
- For RSA-PSS, treat `saltLen` as exact expected length, not a maximum.
- For FFDHE, reject invalid peer public keys with return mask `0`, and do not generate a shared secret.
