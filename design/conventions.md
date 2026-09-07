# C API conventions

Every function in the public surface obeys the conventions below. The
algorithm chapters (`api-*.md`) rely on this document and do not repeat these
rules. If you are reimplementing HACL\*, this is the contract you must decide
to keep or deliberately break.

---

## 1. Naming

Generated C names are the F\* module path with `.` replaced by `_`, followed by
the declaration name:

```
Hacl.Hash.SHA2.hash_256          →  Hacl_Hash_SHA2_hash_256
EverCrypt.AEAD.create_in         →  EverCrypt_AEAD_create_in
Spec.Hash.Definitions.SHA2_256   →  Spec_Hash_Definitions_SHA2_256   (a #define)
```

The prefix may be rewritten by a `-bundle …[rename=X,rename-prefix]` flag, so
the C name reflects the *bundle* name, not necessarily the source module (see
[architecture.md](architecture.md) §4). For example
`Hacl.Streaming.Poly1305_256.*` is emitted as `Hacl_MAC_Poly1305_Simd256_*`.

Recurring suffixes and infixes carry meaning:

| Marker | Meaning |
|---|---|
| `_32`, `_51`, `_64` | Internal *representation* width (limb radix), not a security parameter. `Hacl_Curve25519_51` = radix-2^51 limbs; `Hacl_Curve25519_64` = radix-2^64 (needs 128-bit ints or assembly). |
| `_Simd128`, `_Simd256`, `_Vec128`, `_Vec256` | Requires 128-/256-bit SIMD. A separate C file, compiled with different flags, guarded by CPU detection at the call site. |
| `_224`, `_256`, `_384`, `_512` | Digest size / algorithm variant baked in at compile time. |
| `_vartime` | **Not constant-time.** Only safe on public data. |
| `_expand` | Takes a raw key and expands it internally, instead of taking a pre-expanded state. |
| `_no_check` | Skips the CPU-feature check; the caller has promised the features are present. Calling it on the wrong CPU is undefined behaviour. |
| `malloc_`, `free_`, `copy_`, `reset_`, `update_`, `digest_`, `hash_` | The standard streaming lifecycle (§5). |

---

## 2. Types

### Integers

| C type | Use |
|---|---|
| `uint8_t *` | All byte buffers: keys, nonces, messages, digests, points, scalars. |
| `uint32_t` | **All lengths and indices, everywhere.** There is no `size_t` in the API. |
| `uint64_t` | Occasionally for lengths that may exceed 4 GB in specific APIs, and as the limb type for 64-bit bignums. |
| `bool` | Validity / success results in the HACL\* (non-EverCrypt) layer. |
| `FStar_UInt128_uint128` | Only in code that needs 128-bit arithmetic; realized by `krml/internal/types.h`. |

The `uint32_t`-for-lengths choice is pervasive and load-bearing: it comes from
Low\*'s `UInt32.t` being the index type of `LowStar.Buffer`. **A single call
can therefore never process more than 4 GiB − 1 of data.** Streaming APIs work
around this by accumulating a 64-bit total internally while still taking
`uint32_t` chunks.

### Enumerations

F\* inductive types with no arguments are extracted as `#define`d integer
constants plus a `typedef uint8_t`. They are *not* C enums.

```c
#define Spec_Hash_Definitions_SHA2_224 0
#define Spec_Hash_Definitions_SHA2_256 1
/* … */
typedef uint8_t Spec_Hash_Definitions_hash_alg;
```

Because the numeric values are part of the ABI and are assigned by declaration
order in the F\* source, **adding a case in the middle of an F\* inductive is a
silent ABI break.** The two enumerations a client sees most are
`Spec_Hash_Definitions_hash_alg` (14 cases, `Hacl_Streaming_Types.h`) and
`Spec_Agile_AEAD_alg`.

### Error codes

There are **two** unrelated error enumerations, plus a third `bool`-based
convention, plus a fourth `0/-1` convention in the NaCl API. This is a genuine
inconsistency in the API, not a documentation artifact.

`Hacl_Streaming_Types.h` — used by streaming/incremental APIs:

```c
#define Hacl_Streaming_Types_Success 0
#define Hacl_Streaming_Types_InvalidAlgorithm 1
#define Hacl_Streaming_Types_InvalidLength 2
#define Hacl_Streaming_Types_MaximumLengthExceeded 3
#define Hacl_Streaming_Types_OutOfMemory 4
typedef uint8_t Hacl_Streaming_Types_error_code;
```

`EverCrypt_Error.h` — used by EverCrypt AEAD/DRBG/etc.:

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

Both use `0` for success, which is the only thing they agree on. See
[surprises.md](surprises.md).

### Abstract state

Stateful objects are exposed as pointers to *incomplete* struct types:

```c
typedef struct EverCrypt_AEAD_state_s_s EverCrypt_AEAD_state_s;
typedef struct Hacl_Streaming_MD_state_32_s Hacl_Streaming_MD_state_32;
```

The definition lives in the corresponding `internal/` header or in the `.c`
file. Clients cannot allocate these on the stack, cannot inspect them, and
cannot know their size — allocation is always through the library's
`malloc_`/`create_in` function. This is a deliberate abstraction boundary that
mirrors the F\* `val state : Type0` abstraction; it also means the library can
change the layout without breaking the ABI.

Where the state type *is* exposed (e.g. some BLAKE2 and Poly1305 SIMD state
types whose fields mention vector types), it is only because the type must be
sized by the caller's compiler; the fields are still not meant to be touched.

---

## 3. Buffer contracts

Every buffer argument carries an implicit contract that F\* checked statically
and that C **does not check at run time**:

1. **Liveness.** All pointers must be non-`NULL` and point to live allocations
   of at least the required length. There are no null checks in generated code
   (with one systematic exception, `EverCrypt_AEAD_encrypt`, which returns
   `InvalidKey` if the state pointer is `NULL`).
2. **Length.** The required length is a function of the algorithm and, for
   variable-length arguments, of the accompanying `uint32_t` length parameter.
   Sizes are documented per function in the API chapters; they are *not*
   validated.
3. **Disjointness (no aliasing).** Unless a function's documentation explicitly
   permits in-place operation, **all buffer arguments must be pairwise
   disjoint.** In F\* this is a `disjoint` precondition; in C it is silently
   assumed. Passing overlapping input/output to a function that did not promise
   in-place support is undefined behaviour and may silently produce wrong
   results.
4. **Order.** The prevailing (but *not* universal) convention in HACL\* is
   `f(out, in, in_len, …)` — output first. EverCrypt and the streaming APIs
   generally put the state first and the output last. Check every signature;
   the argument order is not uniform across the library. (Compare
   `Hacl_Hash_SHA2_hash_256(output, input, input_len)` with
   `Hacl_Hash_SHA2_digest_256(state, output)`.)

Violating any of these voids all of the verification guarantees. The correct
mental model is: *the generated C is the residue of a proof that assumed these
preconditions; nothing re-establishes them at the C boundary.*

---

## 4. Memory ownership

The library has three allocation behaviours, and it is important to know which
one you are in:

- **No allocation (the common case).** One-shot functions such as
  `Hacl_Hash_SHA2_hash_256` allocate nothing on the heap. They may use stack
  arrays (C11 VLAs in the gcc distribution, `alloca` in the msvc
  distribution).
- **Explicit `malloc_`/`create_in` + `free_`.** All streaming states, the
  EverCrypt AEAD state, the DRBG state. `malloc_*` returns `NULL` on allocation
  failure and the client **must** check. `free_*` releases everything the state
  owns.
- **Functions that return a freshly-`malloc`ed buffer.** Mostly in the bignum
  and RSA-PSS APIs (`Hacl_Bignum64_new_bn_from_bytes_be`,
  `Hacl_Bignum64_mont_ctx_init`, `Hacl_RSAPSS_new_rsapss_load_pkey`, …). These
  return `NULL` on failure and transfer ownership to the caller, who frees with
  plain `free()` or a dedicated `*_free` function. See
  [api-bignum.md](api-bignum.md).

The library never installs an allocator hook; it calls `KRML_HOST_MALLOC` /
`KRML_HOST_CALLOC` / `KRML_HOST_FREE`, which are macros in the KaRaMeL runtime
headers that default to `malloc`/`calloc`/`free`. Redefining them is the
supported way to plug in a custom allocator.

Secret erasure is available as `Lib_Memzero0_memzero` (`lib_memzero0.h`) and is
used internally by DRBG, FrodoKEM and BLAKE2 to scrub state. It is
*not* automatically applied to caller-owned buffers.

---

## 5. The streaming (incremental) lifecycle

Every incremental API in the library is generated from one functor
(`Hacl.Streaming.Functor`, see [implementation.md](implementation.md) §4) and
therefore has an identical shape:

```c
State *X_malloc(void);                       /* or X_malloc(key) / X_malloc(alg) */
void   X_reset(State *s);                    /* or X_reset(s, key) */
error  X_update(State *s, uint8_t *in, uint32_t len);
void   X_digest(State *s, uint8_t *out);     /* some variants take an out_len */
State *X_copy(State *s);                     /* deep copy */
void   X_free(State *s);
```

Semantics that are guaranteed across *all* instantiations:

- `update` may be called with **any** chunk sizes, including 0. The functor
  maintains an internal block-sized buffer, so the client never does modulo
  arithmetic.
- `update` returns `MaximumLengthExceeded` when the *cumulative* length since
  the last `reset` would exceed the algorithm's maximum message length (e.g.
  2^61−1 bytes for SHA-2/256). This is the only error most instantiations can
  return.
- **`digest` does not consume or invalidate the state.** It operates on an
  internal copy, so the client may keep calling `update` afterwards. This is
  unusual compared with most C crypto libraries, where `final()` destroys the
  context, and it is the reason `digest` is not called `final`.
- `copy` is a deep copy, intended for the "hash a common prefix then diverge"
  pattern.
- `reset` returns the state to the "empty input" state, reusing the allocation
  (and, for keyed constructions, optionally installing a new key).

---

## 6. Constant time / secret independence

- Secrecy is a *type-level* property in the source: `Lib.IntTypes` has
  `uint8`, `uint32`, … (secret) versus `pub_uint8`, … (public). Secret integers
  support no comparison, no division/modulo, and cannot be used as array
  indices or branch conditions. Downgrading requires an explicit call in
  `Lib.RawIntTypes`, which is auditable.
- Consequently, generated code never branches on, or indexes with, secret data.
  Table lookups over secret indices are done with constant-time selection or
  with the "read the whole table and mask" idiom.
- The guarantee stops at the C level. The C compiler is trusted not to
  reintroduce data-dependent branches, and the hand-written intrinsic shims in
  `lib/c/` are outside the proof.
- **`_vartime` functions are an explicit opt-out.** They exist for operations
  on public values (e.g. modular inversion of a public modulus during
  verification). Never feed them secrets.
- Comparison of MAC tags and similar is done with constant-time helpers; the
  API returns a boolean or an error code, never a "position of first
  difference".

---

## 7. Thread safety

- All one-shot functions are pure with respect to global state and are
  therefore thread-safe and reentrant.
- State objects are **not** internally synchronized: two threads must not use
  the same state concurrently. Distinct states are independent.
- `EverCrypt_AutoConfig2` writes to process-global cached flags. The intended
  usage is a single call to `EverCrypt_AutoConfig2_init()` during process
  startup, before any threads are spawned. Concurrent `init` with concurrent
  `has_*` reads is not synchronized.

---

## 8. Headers, includes and the `internal/` directory

A public header:

- is `#include`-guarded, wrapped in `extern "C"` for C++, and pulls in
  `krml/internal/types.h`, `krml/lowstar_endianness.h`,
  `krml/internal/target.h`;
- lists its dependencies explicitly, so an individual algorithm can be
  cherry-picked out of the distribution;
- contains doc comments extracted from the F\* source (`/** … */` blocks with
  `@param`/`@return` tags in the newer modules).

`dist/gcc-compatible/internal/*.h` are **not public API**. They exist so that
one generated `.c` file can call into another (e.g. `Hacl_Hash_SHA2.c` calling
BLAKE2 internals for HMAC). Their contents may change at any time. When an API
chapter mentions something declared only in `internal/`, it is flagged as
non-public.

A handful of hand-written headers are shipped alongside and are also not API in
the usual sense: `libintvector.h` (SIMD intrinsic wrappers),
`lib_intrinsics.h`, `lib_memzero0.h`, `evercrypt_targetconfig.h`,
`curve25519-inline.h`, `libintvector-shim.h`. `TestLib.h` and
`Lib_PrintBuffer.h` are test-only.

---

## 9. Preconditions on CPU features

Functions in `_Simd128`/`_Simd256`/`_Vec128`/`_Vec256` modules, and everything
that dispatches to Vale assembly, have an *unchecked* precondition that the
required instruction-set extension is available. The library provides two ways
to satisfy it:

1. Use the `EverCrypt_*` entry point, which calls `EverCrypt_AutoConfig2_has_*`
   for you and falls back to a portable implementation.
2. Call `EverCrypt_AutoConfig2_init()` and the `has_*` queries yourself, then
   call the `Hacl_*_Simd256_*` function directly.

Calling a SIMD entry point on a CPU that lacks the extension is undefined
behaviour (in practice, SIGILL). See
[api-pq-hpke-random.md](api-pq-hpke-random.md) for the full `AutoConfig2`
surface.
