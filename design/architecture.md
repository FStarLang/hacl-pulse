# Architecture

This document describes the overall structure of the HACL\*/ValeCrypt/EverCrypt
codebase: what the layers are, what artifacts they produce, and how a consumer
ends up with a `libevercrypt.a`. It is the map; the API chapters
(`api-*.md`) are the territory.

See also: [conventions.md](conventions.md) for the C-level contracts that every
generated function obeys, and [implementation.md](implementation.md) for how
the source is written.

---

## 1. The three sub-projects

The repository is a single verification workspace containing three closely
related but distinct deliverables.

| Sub-project | Source language | Output | Directory |
|---|---|---|---|
| **HACL\*** | Low\* (a C-like subset of F\*) | portable, standalone C | `code/`, `lib/` |
| **ValeCrypt** | Vale DSL (verified in F\*) | x64 / PPC64LE assembly | `vale/` |
| **EverCrypt** | Low\* (with Vale interop) | C dispatch layer over both | `providers/evercrypt/` |

The key architectural claim is that all three are verified *in the same
logic* (F\*), which is what makes it sound for a C function in EverCrypt to
call into a Vale assembly routine and inherit its post-condition. A
reimplementation that does not have a shared logic across C and assembly
loses this property and must treat assembly as trusted.

### Layer diagram

```
                 ┌──────────────────────────────────────────────┐
   clients  ───► │  EverCrypt_*.h   (agile + multiplexing API)   │
                 └───────┬──────────────────────────┬───────────┘
                         │                          │
                 ┌───────▼──────────┐      ┌────────▼─────────────┐
                 │  Hacl_*.h        │      │ Vale assembly        │
                 │  (portable C,    │      │ (aesgcm, sha256,     │
                 │   per-algorithm, │      │  poly1305, curve25519│
                 │   per-vector-    │      │  cpuid)              │
                 │   width modules) │      └──────────────────────┘
                 └───────┬──────────┘
                         │
                 ┌───────▼──────────────────────────────────────┐
                 │  lib/  (Lib.IntTypes, Lib.Buffer,            │
                 │         Lib.Sequence, Lib.IntVector, …)      │
                 └───────┬──────────────────────────────────────┘
                         │
                 ┌───────▼──────────────────────────────────────┐
                 │  specs/  (pure functional specifications;    │
                 │           erased at extraction)              │
                 └──────────────────────────────────────────────┘
```

Clients may enter at either of the top two levels. `Hacl_*` is the "I know
what I want and I do my own CPU detection" entry point; `EverCrypt_*` is the
"pick the best thing for me" entry point. Nothing below `Hacl_*` is a
supported API, even though some of it is unavoidably visible in headers
(see [conventions.md](conventions.md) §"internal headers").

---

## 2. Directory map

| Path | Contents |
|---|---|
| `specs/` | Pure, executable, non-optimized functional specifications (`Spec.SHA2.fst`, `Spec.Curve25519.fst`, `Spec.Agile.AEAD.fsti`, …). These are the mathematical reference. They are *not* extracted to C. |
| `specs/lemmas/`, `specs/tests/` | Proofs relating specs to each other; spec-level test vectors. |
| `lib/` | The Low\* standard library layer specific to HACL\*: `Lib.IntTypes` (secret/public integers), `Lib.Buffer`, `Lib.Sequence`, `Lib.IntVector` (SIMD), `Lib.LoopCombinators`, `Lib.NatMod`, `Lib.Exponentiation`. |
| `lib/c/` | The *hand-written*, unverified C shims: `libintvector.h` (SIMD intrinsics), `lib_intrinsics.h` (addcarry/mul64x64), `Lib_RandomBuffer_System.c` (OS entropy), `Lib_Memzero0.c`, `evercrypt_targetconfig.h`. |
| `lib/ml/` | Hand-written OCaml glue for the ctypes bindings. |
| `code/<algorithm>/` | One directory per algorithm family; `Hacl.Impl.*` (implementation) and `Hacl.<Alg>*` (the extracted, specialized instances). |
| `code/meta/` | `Meta.Interface.fst`: the "specialize/inline" F\* tactic used to monomorphize generic code (see [implementation.md](implementation.md) §3). |
| `code/streaming/` | The streaming/incremental functor (`Hacl.Streaming.Functor`) and its instantiations. |
| `providers/evercrypt/` | EverCrypt `.fsti` interfaces; `providers/evercrypt/fst/` holds the implementations. |
| `providers/test/` | Test vectors and test drivers, written in Low\* and extracted to C. |
| `vale/` | Vale sources: `vale/code/` (implementations, `.vaf`), `vale/specs/` (hardware model, crypto specs). |
| `dist/` | **Checked-in generated output.** One subdirectory per *distribution*. |
| `obj/` | Build scratch: `.checked` files, `.krml` files, extracted `.ml`. |
| `hints/` | Checked-in SMT hint files (proof replay data) — one per F\* source file. |
| `doc/` | The Sphinx user manual published at hacl-star.github.io. |
| `tests/` | C-level tests run against a built distribution. |

---

## 3. The build pipeline

```
  .fst/.fsti ──F*──► .checked ──F* --codegen krml──► .krml ──KaRaMeL──► .c/.h
  .vaf ──Vale──► .fst/.fsti ──F*──► .checked ──┬──► .krml (interop stubs)
                                                └──► .S/.asm (via a printer)
```

Concretely:

1. **F\* verification.** Every `.fst`/`.fsti` is type-checked and its proof
   obligations discharged by Z3 (pinned to 4.8.5, see `Makefile.common`).
   Success produces a `.checked` file. Hints in `hints/` make replay fast and
   deterministic.
2. **Extraction to KaRaMeL IR.** F\* erases all specifications, ghost code,
   proofs and refinements, and emits a `.krml` file per module.
3. **KaRaMeL.** The `krml` compiler turns the IR into C. This step is where
   most of the *shape* of the public API is decided — see §4.
4. **Vale.** `.vaf` files are compiled to F\* modules (verified against a
   machine model of x64/PPC) and, separately, printed as GAS/MASM assembly
   for five targets (`linux`, `darwin`, `mingw`, `msvc`, `ppc64le`).
   The checked-in results live in `dist/vale/`.
5. **Assembly.** The generated `.S`/`.asm` files are assembled and linked into
   the same library as the C code.

The generated code is checked into `dist/`, so a consumer never needs F\*,
Z3, Vale or KaRaMeL. That is a deliberate design choice: the verification
toolchain is a *build-time-only, developer-only* dependency.

---

## 4. KaRaMeL bundling: how F\* modules become C files

This is the single most important mechanism to understand when reading the
public API, because **the C file/header structure does not match the F\*
module structure**. It is decided by `-bundle` flags in `Makefile.common`
and `Makefile`.

A bundle has the form:

```
-bundle Api.Module1+Api.Module2=Internal.Module,Internal.*[rename=Public_Name,rename-prefix]
```

- Modules on the **left** of `=` keep their declarations *public* (they end up
  in the generated `.h`).
- Modules on the **right** of `=` are *absorbed* into the same C file, and
  anything not reachable from the left-hand side becomes `static` or is
  dropped entirely.
- `rename=X` sets the resulting C file name; `rename-prefix` also rewrites the
  function-name prefix so that, e.g., `Hacl.Streaming.SHA2.malloc_256` is
  emitted as `Hacl_Hash_SHA2_malloc_256`.

Real examples from `Makefile.common`:

```make
HASH_BUNDLE= \
  -bundle Hacl.Streaming.Types+Hacl.Streaming.MD=Spec.Hash.Definitions[rename=Hacl_Streaming_Types] \
  -bundle Hacl.Streaming.SHA2=Hacl.Hash.SHA2,Hacl.Hash.Core.SHA2,Hacl.Impl.SHA2.*,Hacl.SHA2.Scalar32[rename=Hacl_Hash_SHA2,rename-prefix] \
  -bundle Hacl.Hash.Definitions=Hacl.Hash.*[rename=Hacl_Hash_Base]

POLY_BUNDLE=-bundle 'Hacl.Streaming.Poly1305_32=Hacl.Poly1305_32,Hacl.Impl.Poly1305.Field32xN_32[rename=Hacl_MAC_Poly1305,rename-prefix]' \
  -bundle 'Hacl.Streaming.Poly1305_128=…[rename=Hacl_MAC_Poly1305_Simd128,rename-prefix]' \
  -bundle 'Hacl.Streaming.Poly1305_256=…[rename=Hacl_MAC_Poly1305_Simd256,rename-prefix]'
```

The stated policy is: **one C file per algorithm for HACL\*, one C file per
logical unit for EverCrypt.**

Consequences a reimplementer must reproduce or consciously reject:

- The *public* symbol set is exactly "what a bundle's left-hand side exports",
  not "what an interface file declares". A function can be verified and
  present in F\* and yet be invisible in C.
- Each vector width is a *separate C file* on purpose, so that the compiler
  may be invoked with `-mavx2` on one file without contaminating the scalar
  file with AVX2 instructions. This is a correctness-of-dispatch requirement,
  not an aesthetic one.
- `internal/Foo.h` headers exist for declarations that must be shared between
  generated C files but are not part of the supported API.

Other important flags (in `BASE_FLAGS`/`REQUIRED_FLAGS`):

| Flag | Effect |
|---|---|
| `-minimal` | Do not emit KaRaMeL's default prelude includes; the project supplies its own. |
| `-funroll-loops 16` | Unroll loops with ≤16 iterations — a *performance* knob applied globally. |
| `-static-header M` | Emit `M`'s functions as `static inline` in a header rather than as external symbols (used for `Hacl.Impl.Curve25519.Field51`, precomputed-table modules, `EverCrypt.TargetConfig`, `Hacl.IntTypes.Intrinsics`). |
| `-library M` / `-no-prefix M` | Declare `M` as externally implemented (Vale stubs, `EverCrypt.TargetConfig`) and do not prefix its names. |
| `-drop Lib.IntVector.Intrinsics` | The SIMD "module" has no generated implementation; it is realized by the hand-written `libintvector.h`. |
| `-add-include 'X.c:"y.h"'` | Inject a hand-written header into a generated file. This is how `libintvector.h`, `lib_intrinsics.h`, `lib_memzero0.h` and `config.h` reach the generated code. |
| `-ctypes EverCrypt.*,Hacl.*` | Generate OCaml ctypes bindings (only in the `gcc-compatible` distribution). |
| `-bundle Prims,C,FStar.*,LowStar.*[rename=Hacl_Krmllib]` | Sweep all leftover F\* standard-library residue into a single `Hacl_Krmllib` catch-all. |

An explicitly documented invariant (as of Feb 2025): **`libintvector.h` should
never be included from a public header.** It is included from `.c` files
wherever possible; the exceptions are the four modules whose *public state
type* mentions a vector type (`Hacl_Hash_Blake2b_Simd256`,
`Hacl_Hash_Blake2s_Simd128`, `Hacl_MAC_Poly1305_Simd128/256`), plus
`EverCrypt_Hash.h`. `Hacl_Streaming_HMAC.h` gets `libintvector-shim.h`
instead, which declares opaque stand-ins.

---

## 5. Distributions

`dist/` holds several *distributions*: the same verified code compiled with
different KaRaMeL options for different consumers.

| Distribution | Purpose |
|---|---|
| `gcc-compatible` | The flagship. Assumes C11 VLAs and GCC/Clang; also ships OCaml ctypes bindings (`lib_gen/`). **This is the reference for the API chapters.** |
| `msvc-compatible` | Uses `alloca` instead of VLAs (`-falloca`), KaRaMeL-performed tail calls (`-ftail-calls`), no GCC inline assembly for Curve25519. |
| `portable-gcc-compatible` | Built without `-march=native`, to prove that every CPU-feature assumption is explicit in the Makefile rather than accidentally supplied by the compiler. Adds `-rst-snippets` for documentation extraction. |
| `mozilla` | A curated subset for NSS. |
| `wasm` | Pure-Low\* subset only: no intrinsics, no Vale, no EverCrypt, no 128-bit-integer-dependent code. Compiled by KaRaMeL's WASM backend (`-wasm -minimal`). |
| `vale` | The generated assembly for all five target triples, plus `curve25519-inline.h`. |
| `karamel` | The KaRaMeL runtime headers a consumer needs (`krml/internal/types.h`, `FStar_UInt128*`, endianness helpers). |

`doc/Obtaining.rst` states the ordering `msvc-compatible <= gcc-compatible <=
gcc64-only` in terms of assumptions made about the C compiler.

There are ~85 generated `.c` files and ~98 public headers in
`dist/gcc-compatible`, totalling roughly 80k lines of C, plus 22 assembly
files in `dist/vale`.

### 128-bit integers

`FStar.UInt128` is realized three ways, selected by preprocessor macros in
`karamel/include/krml/internal/types.h`:

1. GCC/Clang 64-bit: hand-written using `unsigned __int128` (unverified).
2. MSVC: hand-written using intrinsics (unverified).
3. Otherwise, or when `KRML_VERIFIED_UINT128` is defined: the *verified*
   (slow) implementation extracted from `FStar.UInt128`.

This matters because several algorithms (`Hacl_Curve25519_64`,
`Hacl_Bignum64` on some paths, Poly1305's 64-bit field) depend on it.

---

## 6. Compile-time vs. run-time configuration

EverCrypt distinguishes two orthogonal axes, and a reimplementation must keep
them separate:

- **Compile-time (target) configuration** — `EverCrypt.TargetConfig`,
  extracted as `#define`s in `evercrypt_targetconfig.h`:
  `HACL_CAN_COMPILE_VALE`, `HACL_CAN_COMPILE_VEC128`, `HACL_CAN_COMPILE_VEC256`,
  `HACL_CAN_COMPILE_INLINE_ASM`. These say whether the *toolchain and target*
  can even build a given code path. They are marked `[@@ CIfDef ]` in F\* so
  KaRaMeL emits them as preprocessor conditionals rather than runtime booleans
  — otherwise the linker would demand symbols that were never compiled.
- **Run-time configuration** — `EverCrypt.AutoConfig2`, a set of cached
  boolean flags populated by a CPUID call (itself implemented in Vale).

The idiomatic dispatch shape, quoted from `EverCrypt.AutoConfig2.fsti`, is:

```fstar
if EverCrypt.TargetConfig.hacl_can_compile_vec128 && has_vec128 () then ...
```

which compiles to:

```c
#if defined(HACL_CAN_COMPILE_VEC128)
  if (EverCrypt_AutoConfig2_has_vec128()) { ... }
#endif
```

Note the *ordering requirement*: the compile-time flag must be the left operand
so that KaRaMeL can lift it to a `#if`. This is a genuine, load-bearing
syntactic constraint in the source.

`AutoConfig2`'s flags default to **all-false**; a client that never calls
`EverCrypt_AutoConfig2_init()` gets the slow-but-correct portable path. There
are also `disable_*` functions so a client (or a fuzzer, or a test harness)
can force a particular code path.

---

## 7. What is trusted

A reimplementer should know exactly where the verified/unverified boundary is,
because it is smaller than marketing suggests:

- The F\* type-checker, Z3, KaRaMeL, the Vale printer, and the C compiler are
  trusted.
- `lib/c/*.c` and `lib/c/*.h` are **hand-written and unverified**: the SIMD
  intrinsics layer (`libintvector.h`), the carry/multiply intrinsics
  (`lib_intrinsics.h`), OS randomness (`Lib_RandomBuffer_System.c`), and
  `Lib_Memzero0.c`.
- The two fast `FStar.UInt128` implementations are unverified.
- The *specifications* in `specs/` are trusted to correctly transcribe the
  RFCs/NIST standards; nothing checks that `Spec.SHA2.fst` is really SHA-2
  except human review and test vectors.
- Secret independence is enforced by typing (`Lib.IntTypes` secret integers do
  not support comparison or division), not by inspecting the emitted assembly.
  The C compiler is trusted not to reintroduce a branch.
