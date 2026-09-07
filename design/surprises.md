# Surprising and non-obvious design choices

A list of things that are likely to trip up someone who reads the API or the
code with expectations formed by other cryptographic libraries. Every item here
was verified against the tree; file references are given so the claim can be
rechecked.

---

## API-shape surprises

### 1. There are four different error conventions

| Convention | Where | Values |
|---|---|---|
| `Hacl_Streaming_Types_error_code` | streaming/incremental APIs | `Success=0, InvalidAlgorithm=1, InvalidLength=2, MaximumLengthExceeded=3, OutOfMemory=4` |
| `EverCrypt_Error_error_code` | EverCrypt AEAD, DRBG, … | `Success=0, UnsupportedAlgorithm=1, InvalidKey=2, AuthenticationFailure=3, InvalidIVLength=4, DecodeError=5, MaximumLengthExceeded=6` |
| `bool` | most HACL\* validation/verify functions | `true` = valid/success |
| `uint32_t` 0 / `0xffffffff` | `Hacl_NaCl.*` | `0U` success, `0xffffffffU` failure — i.e. NaCl's `-1`, widened |

The two enumerations both have a `MaximumLengthExceeded` case with *different*
numeric values (3 vs 6). Nothing in C prevents you from comparing one against
the other. See `dist/gcc-compatible/Hacl_Streaming_Types.h`,
`EverCrypt_Error.h`, and `Hacl_NaCl.c` (`return 0xffffffffU;`).

### 2. Enum values are part of the ABI, and are assigned by source order

`Spec_Hash_Definitions_hash_alg` is a `uint8_t` with `#define`d constants whose
values come from the declaration order of an F\* inductive type. The order is
*not* alphabetical, *not* grouped by family, and includes SHAKE:

```c
SHA2_224=0, SHA2_256=1, SHA2_384=2, SHA2_512=3, SHA1=4, MD5=5,
Blake2S=6, Blake2B=7, SHA3_256=8, SHA3_224=9, SHA3_384=10, SHA3_512=11,
Shake128=12, Shake256=13
```

Note `SHA3_256` precedes `SHA3_224`. Inserting a new algorithm in the middle of
the F\* type silently renumbers everything after it.

### 3. `digest` does not finalize the state

Unlike almost every other C hashing API, `X_digest(state, out)` leaves the
state usable: it finalizes an internal *copy*. Clients may keep calling
`update`. This is why the function is not named `final`. (See the doc comment
on `Hacl_Hash_SHA2_digest_256` in `dist/gcc-compatible/Hacl_Hash_SHA2.h`.)

### 4. Every length is a `uint32_t`

There is no `size_t` anywhere in the API, because Low\*'s buffer index type is
`UInt32.t`. A single call therefore cannot process more than 4 GiB − 1. The
streaming APIs work around this with an internal 64-bit `total_len` while still
accepting only `uint32_t` chunks. On a 64-bit platform this is a silent
truncation hazard for callers that hold `size_t` lengths.

### 5. Argument order is not uniform

One-shot HACL\* functions are usually `f(out, in, in_len)`; streaming functions
are `f(state, in, in_len)` and `digest(state, out)`; some EverCrypt functions
put the output last. Compare:

```c
void Hacl_Hash_SHA2_hash_256(uint8_t *output, uint8_t *input, uint32_t input_len);
void Hacl_Hash_SHA2_digest_256(Hacl_Streaming_MD_state_32 *state, uint8_t *output);
```

There is no rule to memorize; read each signature.

### 6. `_no_check` entry points bypass CPU feature detection

`EverCrypt_AEAD.h` exposes both
`EverCrypt_AEAD_encrypt_expand_aes128_gcm` and
`EverCrypt_AEAD_encrypt_expand_aes128_gcm_no_check`. The latter omits the
`AutoConfig2` query: the caller asserts the CPU has AES-NI/PCLMULQDQ/AVX/SSE/MOVBE.
Getting that wrong is an illegal instruction, not an error code. This is a
deliberate escape hatch for callers who have already done detection.

### 7. Runtime feature flags default to *disabled*

`EverCrypt_AutoConfig2` caches all CPU feature bits as `false` until
`EverCrypt_AutoConfig2_init()` is called
(`providers/evercrypt/EverCrypt.AutoConfig2.fsti`: "By default, all feature
flags are disabled. A client must call init to get meaningful results"). A
client that forgets `init()` silently gets the slowest portable path — which is
the safe failure mode, but is easy to miss when benchmarking.

There are also `EverCrypt_AutoConfig2_disable_*` functions, so the test suite
(and any client) can force specific code paths.

### 8. `Hacl_AES128.h` ships declarations with no implementation

```c
extern void Hacl_AES128_aes128_key_expansion(uint8_t *key, uint8_t *expanded_key);
extern void Hacl_AES128_aes128_encrypt_block(uint16_t *cipher, uint16_t *plain,
                                             uint8_t *expanded_key);
```

`code/frodo/Hacl.AES128.fsti` has no `.fst`: it is an *assumed* interface,
consumed by FrodoKEM's AES-based matrix generation
(`code/frodo/Hacl.Impl.Frodo.Gen.fst`). But all four shipped Frodo variants are
instantiated with SHAKE128, not AES, so nothing in `dist/` calls these symbols.
The header is a linkage trap: it looks like a portable AES implementation and
is not one. Note also the odd `uint16_t *` block type.

### 9. FrodoKEM exposes its parameter sizes as mutable global variables

```c
extern uint32_t Hacl_Frodo640_crypto_publickeybytes;   /* = 9616U */
extern uint32_t Hacl_Frodo640_crypto_ciphertextbytes;  /* = 9720U */
```

Not `#define`s, not `const` — writable globals (`dist/gcc-compatible/Hacl_Frodo640.c`).

### 10. `Hacl_Frodo64` is a toy

It exists to make the (very slow) FrodoKEM proofs and tests tractable at a
small parameter size. It provides no security. It sits in the same directory,
with the same API shape, as the real parameter sets.

### 11. MD5 and SHA-1 are shipped as first-class modules

`Hacl_Hash_MD5.h` and `Hacl_Hash_SHA1.h` offer the full streaming API, and both
are reachable through the agile `EverCrypt_Hash` enum. They exist because
protocols still need them (e.g. legacy TLS PRF), not because they are
recommended.

---

## Structural surprises

### 12. The C file structure has nothing to do with the F\* module structure

Header and file layout is decided by `-bundle` flags in `Makefile.common`, not
by module names. `Hacl.Streaming.Poly1305_256` becomes
`Hacl_MAC_Poly1305_Simd256_*`; `Hacl.Streaming.SHA2` becomes `Hacl_Hash_SHA2_*`;
a dozen `Hacl.Impl.*` modules vanish into `static` functions. A grep for a C
symbol will frequently find nothing in the F\* sources under that name.

### 13. Vectorized variants are separate C files *for correctness*

Putting the scalar and AVX2 instances in the same translation unit would let
the compiler emit AVX2 instructions in the "portable" function, breaking
runtime dispatch. Hence `-bundle` splits by vector width and the Makefile
compiles each file with different `-m` flags. This is why the API has
`Hacl_Chacha20_Vec128`, `_Vec256`, `_Vec32` rather than one function with a
width parameter.

### 14. Generated code is checked into the repository

`dist/` (C, headers, assembly for five targets) and `hints/` (Z3 proof replay
data) are version-controlled, and CI fails if a regeneration produces a diff.
Consumers never install F\*, Z3, Vale or KaRaMeL. The generated code is a
reviewed artifact.

### 15. `-funroll-loops 16` is applied globally at the KaRaMeL level

`Makefile.common`'s `BASE_FLAGS` unrolls every loop with at most 16 iterations
*before* the C compiler sees it. Some "surprising" verbosity in the generated C
is this, not the algorithm.

### 16. `Hacl_Krmllib.h` is a catch-all for F\* standard-library residue

```
-bundle Prims,C.Failure,C,C.String,C.Loops,Spec.Loops,C.Endianness,FStar.*,LowStar.*[rename=Hacl_Krmllib]
```

Anything from the F\* standard library that survives extraction lands there. It
is not a designed API; it is a sweepings bin that happens to be public.

### 17. Inline assembly is delivered through a hand-written header

`curve25519-inline.h` contains GCC inline-assembly implementations of the
radix-2^64 field operations, injected into `Hacl_Curve25519_64.c` by
`-add-include`. So one "C" algorithm is really assembly, gated by the
compile-time flag `HACL_CAN_COMPILE_INLINE_ASM`, with the MSVC distribution
falling back to external linkage instead.

### 18. Precomputed tables are `static const` in headers

`Hacl.P256.PrecompTable`, `Hacl.K256.PrecompTable`, `Hacl.Ed25519.PrecompTable`
are extracted with `-static-header`, so the tables are duplicated into every
translation unit that includes them, rather than being a single shared symbol.

### 19. The public state type sometimes leaks SIMD types

The project's stated invariant is that `libintvector.h` must never be included
from a public header (it breaks consumers such as CPython). Four modules
violate it necessarily, because their *state type* mentions a vector type:
`Hacl_Hash_Blake2b_Simd256`, `Hacl_Hash_Blake2s_Simd128`,
`Hacl_MAC_Poly1305_Simd128/256` — plus `EverCrypt_Hash.h`.
`Hacl_Streaming_HMAC.h` gets `libintvector-shim.h` instead, a stub header that
declares the types opaquely. `Hacl_Hash_SHA3_Simd256` is called out in the
Makefile as an unenforceable case because it has no internal header.

---

## Verification-related surprises

### 20. Constant-timeness is a *typing* property, not an audit

`Lib.IntTypes` distinguishes secret from public integers; secret integers admit
no comparison, no division, no branching, no use as an index. Nothing inspects
the generated assembly. The C compiler is trusted not to reintroduce branches,
and the hand-written intrinsics in `lib/c/` are outside the proof.

### 21. `_vartime` functions are deliberately *not* constant-time

`Hacl_Bignum64_mod_inv_prime_vartime`, `mod_exp_vartime`, and similar are safe
only on public data. They are in the same header, next to their constant-time
siblings, distinguished only by a name suffix.

### 22. Preconditions are checked by the verifier, never at run time

Disjointness, liveness, buffer lengths, "modulus must be odd", "input length
< 2^61" — all of these are F\* preconditions that evaporate at extraction.
The C code does not check them and does not report them. A C client violating a
precondition gets undefined behaviour with no diagnostic. The verification
guarantee is *conditional on the client*.

### 23. Some of the fastest paths are unverified

The two fast `FStar.UInt128` implementations (GCC `unsigned __int128`, MSVC
intrinsics) are hand-written; `KRML_VERIFIED_UINT128` selects the slow verified
one. `libintvector.h`, `lib_intrinsics.h`, `Lib_RandomBuffer_System.c` and
`Lib_Memzero0.c` are hand-written C. Randomness — arguably the most
security-critical primitive — is entirely a trusted shim.

### 24. The specifications themselves are trusted

Nothing proves that `Spec.SHA2.fst` is SHA-2. Correspondence with the standard
rests on human review plus test vectors in `specs/tests/`. Functional
correctness means "agrees with the spec", and the spec is the axiom.

### 25. The bignum library uses type classes while everything else uses a tactic

`code/meta/DOCUMENTATION.md` explains: the specialize/inline tactic cannot
handle two indices (limb type *and* limb count), requires the index to come
first syntactically, and had only been debugged for inductive indices — so the
bignum development was written by hand with type classes instead. Four distinct
code-reuse mechanisms coexist in the tree for historical and pragmatic reasons.

### 26. Agility and multiplexing are separate axes and are easy to confuse

"Agile" = algorithm chosen by a runtime enum argument. "Multiplexed" =
implementation chosen by runtime CPU detection. A function can be one, both, or
neither. `EverCrypt_Hash` is both; `Hacl_Hash_SHA2` is neither;
`EverCrypt_Curve25519` is multiplexed but not agile.

---

## Surprises specific to the F\* API

These affect verified clients rather than C clients. See
[fstar-api.md](fstar-api.md) and the `fstar-api-*.md` chapters.

### 27. `_vartime` is a naming convention, not a typing rule

This is the F\*-level sharpening of #21, and it is the most important caveat
for verified clients. The buffer arguments to `mod_exp_vartime`,
`exp_vartime`, `load_point_vartime` and friends are `lbuffer uint8 ...` — that
is, **secret** bytes. Nothing in the type system prevents a client from passing
genuinely secret data to a variable-time function. Secret independence is
enforced *within* the constant-time implementations; the boundary between the
constant-time and variable-time worlds is maintained by the caller reading the
function name. A reimplementation could do better here at essentially zero
cost, by giving variable-time entry points public-integer argument types.

### 28. Several theorems a client would expect simply do not exist

`Spec.Agile.AEAD.correctness` gives the AEAD round trip, but there is **no
exported sign-then-verify lemma** for Ed25519, P-256 or K-256, and **no
exported ECDH/DH commutativity lemma** for Curve25519, `Spec.Agile.DH`, P-256,
K-256 or FFDHE. A verified client that needs
`verify pk m (sign sk m) == true` must prove it itself from the spec
definitions. The full catalogue, including these absences, is in
[fstar-specs.md](fstar-specs.md) §4.

### 29. The C API and the F\* API do not have the same arity

Erased and implicit arguments (`#a: G.erased alg`, index arguments,
propositional parameters `p: Type0`) appear in the F\* signature and vanish at
extraction. Conversely, `Lib.Buffer`'s length-carrying types mean the F\*
signature often has *fewer* explicit length arguments than the C prototype.
Do not expect a 1:1 correspondence in either direction.

### 30. The contract is usually one file away from the `val`

HACL\* interfaces declare functions by instantiating a shared type
abbreviation: `val scalarmult: scalarmult_st M51 True`. The actual
`requires`/`ensures` live in `Hacl.Impl.Curve25519.Generic.fsti`. This is what
makes one signature serve a C implementation and a Vale implementation with
different CPU preconditions — but it means "read the `.fsti`" is often a
two-hop operation.

### 31. Multiplexed frontends are weaker *preconditions*, not just convenience

`Hacl.Curve25519_64.scalarmult` requires the caller to prove
`adx_enabled /\ bmi2_enabled`. `EverCrypt.Curve25519.scalarmult` has the same
postcondition and no CPU precondition at all. The entire value of the EverCrypt
layer is visible in the types as precondition weakening — which also means that
a C client, having no types, cannot see it.

### 32. CPU feature detection returns a proof, and the implication is one-way

`EverCrypt.AutoConfig2` getters have postcondition `b ==> flag`, never
`b <==> flag`. A `true` result is a capability that discharges a precondition;
a `false` result tells you *nothing* (the feature may exist but have been
disabled via the corresponding `disable_*` function). This is sound — you just
take the slower path — but it means you cannot prove a fast path is reachable.

### 33. Some usage protocols exist only for verified clients

`EverCrypt.AEAD.fsti:10-11` states plainly that the expand-key-then-reuse
protocol "is enforced for verified F\* clients but, naturally, isn't for C
clients." The same is true of the streaming lifecycle and of every
disjointness requirement. Two audiences, two very different levels of
guarantee, from one codebase.

### 34. In-place encryption is explicitly permitted — and stated as a disjunction

`EverCrypt.AEAD.fsti:274` requires `(B.disjoint plain cipher \/ plain == cipher)`.
Full aliasing is allowed; partial overlap is not. This is exactly the kind of
precise permission that a C header cannot express and that documentation
usually gets wrong in one direction or the other.

### 35. `frame_invariant` carries an SMT pattern and still sometimes needs a manual call

`providers/test/Test.fst:191` contains a literal
`EverCrypt.AEAD.frame_invariant B.loc_none st h1 h2` — in the library's *own*
test code, despite the lemma being declared with
`[SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1)]`. Automation is
best-effort; verified clients should expect to write framing calls by hand.
