# Implementation design

This chapter describes *how* the library is written: the layering from
specification to optimized code, the code-reuse mechanisms, and the recurring
design patterns. It deliberately omits proof engineering and loop-level
details. The goal is that a reader could rebuild an equivalent library in a
different language while keeping the same overall structure.

Prerequisites: [architecture.md](architecture.md) (build pipeline, bundling)
and [conventions.md](conventions.md) (C-level contracts).

---

## 1. The three-tier source structure

Every algorithm exists at three levels of abstraction, in three different
places in the tree.

### Tier 1 — pure specification (`specs/`)

A direct, unoptimized, *executable* transcription of the standard, written in
total functional F\* over mathematical integers and immutable sequences:

```
Spec.SHA2.fst, Spec.Curve25519.fst, Spec.Poly1305.fst, Spec.Blake2.fst,
Spec.Ed25519.fst, Spec.K256.fst, Spec.P256.fst, Spec.RSAPSS.fst, …
```

Some specs are *agile* — parameterized over an algorithm identifier:

```
Spec.Agile.Hash.fsti, Spec.Agile.AEAD.fsti, Spec.Agile.HMAC.fsti,
Spec.Agile.HKDF.fsti, Spec.Agile.HPKE.fsti, Spec.Agile.Cipher.fsti,
Spec.Agile.DH.fst
```

The agile specs are the ones EverCrypt's API is written against; `Spec.Agile.Hash`
dispatches on `Spec.Hash.Definitions.hash_alg`, which is exactly the enum a C
client passes to `EverCrypt_Hash_*`. Specs are erased at extraction and appear
in no generated C file (they are swept into `Hacl_Spec.h` if any residue
survives).

Specs are also *executable in OCaml*, which is how `specs/tests/` runs test
vectors against the spec rather than against the implementation.

### Tier 2 — the Low\* library (`lib/`)

A thin layer over Low\* giving crypto-friendly abstractions:

| Module | Role |
|---|---|
| `Lib.IntTypes` | The secret/public integer discipline. Machine integers indexed by width and by *secrecy*; secret integers admit no comparison, division or branching. |
| `Lib.RawIntTypes` | The auditable escape hatch that declassifies a secret integer. |
| `Lib.Buffer` | Mutable arrays with length in the type (`lbuffer a len`), plus `gbuffer` (immutable) and `ibuffer`. |
| `Lib.Sequence` | The pure counterpart used in specs, with `lseq a len`. |
| `Lib.ByteBuffer` / `Lib.ByteSequence` | Serialization: `uint_from_bytes_le/be`, `uints_from_bytes_*`, constant-time equality. |
| `Lib.LoopCombinators` | `repeat`, `repeati`, `repeat_blocks` — the pure loop combinators specs are written with. |
| `Lib.Loops` | Their imperative counterparts, which extract to C `for` loops. |
| `Lib.IntVector` | The SIMD abstraction: `vec_t t w`, `vec_add_mod`, `vec_load`, `vec_permute`, `vec_interleave_*`, etc. |
| `Lib.IntVector.Transpose`, `Lib.IntVector.Serialize` | Multi-buffer transposition and vector (de)serialization. |
| `Lib.MultiBuffer`, `Lib.NTuple` | N-way "array of pointers" abstraction used by the SIMD multi-buffer hash APIs. |
| `Lib.NatMod`, `Lib.Exponentiation` | Generic modular arithmetic and a generic (windowed, constant-time) exponentiation used by bignum, P-256, K-256 and Ed25519. |
| `Lib.UpdateMulti` | The block-decomposition lemmas shared by all block-based constructions. |

The single most consequential idea here is the *secret integer type*.
Constant-timeness is not audited after the fact; it is a typing property.
A reimplementation in another language should reproduce this with whatever
mechanism it has (a newtype with a restricted API is enough, as long as the
restriction is enforced).

### Tier 3 — implementations (`code/<alg>/`)

Written against `lib/`, proved equivalent to the Tier-1 spec, and extracted to
C. Naming inside a directory is consistent:

- `Hacl.Impl.<Alg>*` — the generic, `inline_for_extraction`, index-parametric
  implementation. Usually *not* extracted on its own.
- `Hacl.<Alg>_<variant>` — a specialization that *is* extracted (e.g.
  `Hacl.Chacha20_Vec128`, `Hacl.Curve25519_51`, `Hacl.Poly1305_256`).
- `Hacl.Spec.<Alg>*` — intermediate specifications that bridge the gap between
  `Spec.<Alg>` and the low-level representation (e.g. reasoning about limbs and
  vectors rather than mathematical integers).

---

## 2. Representation choices are visible in module names

HACL\* does not hide the internal number representation behind a runtime
abstraction: it *promotes it into the module name*, because each
representation compiles to different C.

- `Hacl_Curve25519_51`: field elements as 5 × 64-bit limbs, radix 2^51.
  Portable C, no 128-bit multiply needed beyond what KaRaMeL supplies.
- `Hacl_Curve25519_64`: radix 2^64 (4 limbs), requiring either
  `unsigned __int128` or, preferentially, Vale assembly / GCC inline assembly
  (`curve25519-inline.h`).
- Poly1305: `Field32xN` parameterized by lane count 1/4/8, giving
  `Hacl_MAC_Poly1305`, `_Simd128`, `_Simd256`.
- K-256 field: 5 × 52-bit limbs; P-256: 4 × 64-bit limbs.

Consequence: **the choice of representation is a compile-time, per-module
decision, and multiplexing between representations happens one level up, in
EverCrypt.** A reimplementation that wants runtime-selectable representations
must add a dispatch layer of its own.

---

## 3. Code reuse: four mechanisms, chosen per-algorithm

This is the most distinctive part of the design and is documented at length in
`code/meta/DOCUMENTATION.md`. The problem: an algorithm like ChaCha20 has one
logical definition but three lane widths, and SHA-256 has both a C and a Vale
implementation of its compression function. Writing the code three times is
unacceptable; writing it once generically produces code that cannot be
compiled to idiomatic C.

Four solutions coexist in the tree:

1. **`inline_for_extraction` + partial application.** Write the algorithm
   parameterized by an index; mark the whole call graph
   `inline_for_extraction`; apply to a concrete index. F\* normalizes away the
   index and produces fully specialized code. Simple, but it *flattens the
   call graph* into one enormous function and cannot be split across files.
2. **Wrappers** (`let f i = match i with 1 -> f_32 | 4 -> f_128 | …`). Easy to
   read but a *closed* parameterization: you cannot add a new implementation
   (e.g. a Vale one) without editing the match. Mostly removed from the
   codebase for that reason.
3. **Explicit function parameters / type classes.** The generic code takes its
   primitive operations as arguments. Used by the **bignum** development, via
   F\* type classes, because the specialize tactic could not handle two indices
   (limb type *and* limb count) and because precise control over reduction was
   wanted.
4. **The specialize/inline tactic** (`code/meta/Meta.Interface.fst`) — the
   preferred mechanism. Functions that should survive as C functions are
   annotated `[@ Meta.Attribute.specialize ]`; functions that should be
   inlined but traversed are annotated `[@ Meta.Attribute.inline_ ]`. A
   `%splice` invocation of `Meta.specialize_call_graph` rewrites the call graph
   into higher-order form automatically, so that each specialized instance
   calls *specialized* callees rather than re-inlining them.

The tactic's goals, in the words of the design doc, are four properties that
naive inlining cannot deliver simultaneously:

- (i) full specialization of the code,
- (ii) each instance in its own C file (so that `-mavx2` can be applied
  file-by-file),
- (iii) preservation of the call-graph shape, so the emitted C is readable,
- (iv) modularity: the ability to substitute one node (e.g. `double_round`)
  with an assembly implementation without touching the rest.

Property (ii) is a *security/correctness* requirement, not cosmetics: if the
scalar and AVX2 instances lived in the same translation unit, the compiler
could legally emit AVX2 instructions inside the "portable" function, breaking
runtime dispatch.

This whole mechanism is essentially **C++-templates-by-tactic**. A
reimplementation in a language with generics/monomorphization gets it for free
— but must retain the "one instance per translation unit, compiled with
different flags" discipline.

`Hacl.Meta.HPKE` is the extreme case: HPKE is monomorphized into 15 separate
top-level modules (KEM × AEAD × KDF), each extracted to its own C file.

---

## 4. The streaming functor

`code/streaming/Hacl.Streaming.Functor.fst` implements, once and for all, the
transformation from a *block-based* API to a *byte-stream* API. Everything
incremental in the library — every hash, HMAC, Poly1305 — is an instance.

The functor is parameterized by a record type `Hacl.Streaming.Interface.block`
whose fields are, in essence, the algorithm's block-level specification and
implementation:

| Field | Meaning |
|---|---|
| `km` | Key management: `Erased` (no runtime key) or `Runtime` (key stored in the state). |
| `state`, `key` | The stateful types for the block state and the key. |
| `max_input_len` | Algorithm-specific bound (e.g. 2^61−1 for SHA-256). |
| `block_len`, `blocks_state_len` | Block size, and the (multiple-of-block) size of the internal buffer — the latter can be larger to enable multi-block processing. |
| `init_input_len` / `init_input_s` | Data implicitly prepended to the stream (this is how keyed constructions such as HMAC and keyed BLAKE2 are modelled). |
| `init_s`, `update_multi_s`, `update_last_s`, `finish_s` | The pure block-level spec. |
| `spec_s` | The one-shot spec. |
| `update_multi_zero`, `update_multi_associative`, `spec_is_incremental` | The proof obligations the instance must discharge: that block-wise processing is associative and agrees with the one-shot spec. |
| `init`, `update_multi`, `update_last`, `finish` | The Low\* implementations. |
| `output_length_t` | A value type for variable-length outputs — this is how SHAKE fits the same functor. |

The generated state is a flat struct:

```
{ block_state; buf : uint8[blocks_state_len]; total_len : uint64;
  seen : erased;  p_key }
```

`seen` is ghost (erased at extraction) and exists only for the proof; `total_len`
is a genuine 64-bit counter, which is how the API supports streams larger than
the `uint32_t` chunk size. See [conventions.md](conventions.md) §5 for the
client-visible lifecycle.

Two design points worth copying:

- **`digest` copies the block state and finalizes the copy**, leaving the
  client's state usable. This costs one state copy per digest and is the reason
  the operation is not called `final`.
- The functor provides `digest`, `digest_erased`, `digest_heap` variants to
  accommodate instances whose finalization needs heap scratch space.

`Hacl.Streaming.HMAC` is the interesting instance: it is *agile*, so its state
carries a runtime tag (`Hacl.Agile.Hash`) identifying the underlying hash, and
its allocation function takes both an implementation selector and a key.

---

## 5. SIMD

- SIMD is expressed in F\* as `Lib.IntVector`, an abstract vector type with
  operations that mirror the intersection of SSE/AVX/AVX2/NEON.
- `Lib.IntVector.Intrinsics` is `-drop`ped at extraction: there is no generated
  implementation. It is realized by the **hand-written, unverified**
  `lib/c/libintvector.h`, which maps each operation to compiler intrinsics
  selected by `#if defined(__x86_64__) || defined(_M_X64)`, `__aarch64__`,
  `__powerpc64__`, etc.
- Vectorized code comes in two idioms:
  - **Vectorization within one message**: ChaCha20, Poly1305, BLAKE2.
  - **Multi-buffer / multi-lane**: SHA-2 and SHA-3 process 4 or 8 *independent*
    messages in parallel (`Hacl_SHA2_Vec128/256`, `Hacl_Hash_SHA3_Simd256`).
    Their APIs take *tuples of pointers* (`Hacl_Hash_SHA2_uint8_4p`), and
    internally rely on `Lib.IntVector.Transpose` to interleave lanes.
- Vector width appears in the module name, one C file per width; the caller (or
  EverCrypt) picks. See §3, property (ii).

---

## 6. Vale interop

Assembly routines are integrated, not merely linked:

- Vale code is verified against a formal model of the x64 (and PPC64LE)
  instruction set in `vale/specs/hardware/`, including a taint-tracking
  semantics used to prove secret independence of memory accesses and branches.
- `Vale.Stdcalls.*` and `Vale.Wrapper.X64.*` are the *interop* layer: F\*
  functions with Low\* types whose implementation is the assembly routine. The
  Makefile marks them `-library` and `-no-prefix`, so KaRaMeL emits calls to
  them but no definitions.
- `Vale.Inline.X64.F{add,mul,sqr,swap}_inline` are emitted as `-static-header`,
  i.e. GCC inline assembly inlined into the generated C — this is how
  `Hacl_Curve25519_64` gets fast 64×64 field arithmetic without a function call
  (`curve25519-inline.h`, injected via
  `-add-include 'Hacl_Curve25519_64.c:"curve25519-inline.h"'`, and gated by the
  `HACL_CAN_COMPILE_INLINE_ASM` target flag).
- Assembly is shipped for five targets: Linux/GAS, Darwin/GAS, MinGW,
  MSVC/MASM, and PPC64LE.
- Algorithms with Vale implementations: AES-GCM (128/256), AES-CTR, SHA-256
  compression (SHA-EXT), Poly1305, Curve25519 field arithmetic, and CPUID.

The important architectural claim: because both sides are F\* functions with
the same specification, EverCrypt can call either one and prove the same
post-condition. The C/ASM boundary is *inside* the verified perimeter.

---

## 7. EverCrypt: agility and multiplexing

Two orthogonal features, often conflated:

- **Agility**: one function, algorithm chosen by a runtime enum argument
  (`EverCrypt_Hash_*`, `EverCrypt_AEAD_*`, `EverCrypt_HMAC_compute`,
  `EverCrypt_HKDF_*`). Implemented as a `match` on the algorithm; the
  post-condition refers to the agile spec `Spec.Agile.Hash.hash a`.
- **Multiplexing**: one function, *implementation* chosen at runtime by CPU
  feature detection. Implemented as nested conditionals of the shape

  ```fstar
  if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
    let vec256 = EverCrypt.AutoConfig2.has_vec256 () in
    if vec256 then <AVX2 path> else <fallback>
  else <fallback>
  ```

  which KaRaMeL turns into a `#if` wrapping an `if`.

`EverCrypt.AutoConfig2` is itself written in Low\*+Vale (no C shim): the CPUID
instruction is a Vale routine, and the results are cached in mutable globals
hidden behind an abstract footprint `fp ()`, so clients never have to reason
about them. Flags default to `false` — a client that forgets `init()` gets
correct, portable behaviour rather than an illegal instruction.

The `disable_*` functions exist so tests can force each code path; the test
suite exercises every multiplexing branch this way.

EverCrypt also *adds* API surface rather than merely dispatching: the agile
incremental hash (`EverCrypt.Hash.Incremental`, bundled into
`EverCrypt_Hash.h`) is built by instantiating the same streaming functor at an
agile index.

---

## 8. Bignum and generic exponentiation

The bignum development (`code/bignum/`) is the one place using **type classes**
rather than the specialize tactic, because it is parameterized by two indices:
the limb type (`uint32`/`uint64`) and the number of limbs (a `nat`, not an
inductive).

Its structure:

- `Hacl.Bignum.Base/Addition/Multiplication/Convert/Lib` — schoolbook
  primitives, extracted as `static inline` into `Hacl_Bignum_Base.h`.
- `Hacl.Bignum.Montgomery`, `Hacl.Bignum.Exponentiation`, `Hacl.Bignum.ModInv`
  — Montgomery arithmetic and constant-time (plus explicitly variable-time)
  modular exponentiation.
- `Lib.Exponentiation` / `Spec.Exponentiation` — a *generic* windowed
  exponentiation, proved once over an arbitrary commutative monoid and reused
  by bignum, P-256, K-256 and Ed25519 scalar multiplication. This is a
  significant piece of reuse: the same verified ladder serves modular
  exponentiation and elliptic-curve scalar multiplication.
- Specializations at 256 and 4096 bits, at 32- and 64-bit limbs, produce the
  six `Hacl_Bignum*` modules; RSA-PSS and FFDHE are clients.

Precomputed tables (`Hacl.P256.PrecompTable`, `Hacl.K256.PrecompTable`,
`Hacl.Ed25519.PrecompTable`) are generated as constant arrays and extracted
`-static-header`, i.e. as `static const` data inlined into whichever C file
uses them.

---

## 9. Testing

- `specs/tests/` — test vectors run against the *specifications*, in OCaml.
- `providers/test/` — test vectors written in Low\*, extracted to C, and run
  against the compiled library; `Test.Lowstarize.fst` is a meta-program that
  turns literal test vectors into Low\* buffer initializers.
- `tests/` — C-level tests compiled against a built distribution.
- CI regenerates `dist/` and `hints/` and fails if the checked-in output
  differs, which makes the generated code part of the reviewed artifact.

---

## 10. What a reimplementation should keep

In rough order of importance:

1. The spec/implementation split, with the spec written in a form a human can
   compare against the RFC.
2. The secret-integer discipline, enforced by the type system.
3. One translation unit per (algorithm × vector width), compiled with
   per-file flags, with dispatch strictly above that boundary.
4. The streaming functor: implement buffering *once*, not per algorithm.
5. The compile-time/run-time configuration split, with runtime feature flags
   defaulting to off.
6. Explicit, named `_vartime` opt-outs instead of silently variable-time code.
7. Abstract, heap-allocated state objects with `malloc`/`free`/`copy`/`reset`.
