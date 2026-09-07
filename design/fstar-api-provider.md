# F* API: provider/platform layer, randomness, DRBG, HPKE, FrodoKEM, and Vale interop

Audience: verified Low*/F* clients of HACL*/EverCrypt, and reimplementers who
need the F* contracts behind the generated C. This chapter covers the F*
interface surface for CPU autodetection, target configuration, randomness,
DRBG, HPKE, FrodoKEM, and the Vale interop boundary. It deliberately does not
inventory the C API; see [api-pq-hpke-random.md](api-pq-hpke-random.md).

Cross-references: [README.md](README.md), [fstar-api.md](fstar-api.md),
[fstar-specs.md](fstar-specs.md), [architecture.md](architecture.md),
[implementation.md](implementation.md), and [surprises.md](surprises.md).

---

## 1. Orientation and trusted boundary

| Topic | F* source | What is verified / trusted |
|---|---|---|
| Run-time CPU/provider flags | `providers/evercrypt/EverCrypt.AutoConfig2.fsti` | Low* + Vale implementation; getters expose CPU facts as propositions. |
| Compile-time target flags | `providers/evercrypt/EverCrypt.TargetConfig.fsti` | Build macros trusted; KaRaMeL turns `[@@ CIfDef]` into `#if` guards. |
| Vale interop | `vale/code/arch/x64/interop/Vale.Wrapper.X64.*.fsti`, `Vale.Stdcalls.X64.*.fsti` | Vale proof connects assembly to Low* signatures; ABI bridge is a boundary. |
| OS randomness | `lib/Lib.RandomBuffer.System.fsti` | Assumed F* interface, realized by hand-written C; randomness quality is not proved. |
| Spec entropy | `lib/Lib.RandomSequence.fsti` | Abstract entropy-transition model. |
| Zeroization shim | `lib/Lib.Memzero0.fsti` | Hand-written C; visible postcondition is only a footprint property. |
| DRBG | `providers/evercrypt/EverCrypt.DRBG.fsti`, `code/drbg/Hacl.HMAC_DRBG.fsti` | HMAC-DRBG is related to `Spec.HMAC_DRBG`; EverCrypt layer trusts OS entropy. |
| HPKE | `code/hpke/Hacl.HPKE.Interface.*`, `Hacl.Impl.HPKE.*`, `Hacl.Meta.HPKE.fst` | Generic implementation specialized by F* metaprogramming. |
| FrodoKEM | `code/frodo/Hacl.Frodo.KEM.fst`, `Hacl.Frodo*.fst`, `Hacl.Frodo.Random.fsti`, `Hacl.AES128.fsti` | SHAKE-based KEM path; `Hacl.AES128.fsti` is axiomatized external here. |

## 2. `EverCrypt.AutoConfig2` as an F* API

`EverCrypt.AutoConfig2` is the centerpiece. It is not merely a collection of
booleans; it lets a verified caller turn a run-time branch into an F* fact.

```fstar
// providers/evercrypt/EverCrypt.AutoConfig2.fsti:1-6
(** This module, unlike the previous attempt at autoconfig, is entirely written
  in Low* + Vale, and does not play dirty tricks with global variables. As such,
  there is no C implementation for it, only an .fst file.

  This module revolves around individual feature flags, which can be selectively
  disabled. *)
```

### 2.1 `getter`

```fstar
// providers/evercrypt/EverCrypt.AutoConfig2.fsti:18-24
unfold
inline_for_extraction noextract
let getter (flag: bool) = unit -> Stack bool
  (requires (fun _ -> true))
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b ==> flag)))
```

The postcondition is one-directional: `b ==> flag`, not `b <==> flag`. If the
getter returns `true`, F* learns the feature proposition. If it returns `false`,
F* learns no negated fact. This is essential because features can be masked by
`disable_*`, or not initialized, even when hardware supports them.

For a verified client, branching on `has_aesni ()` gives
`Vale.X64.CPU_Features_s.aesni_enabled` in the true branch. That is exactly the
precondition fact needed by Vale-backed functions whose `requires` mention
`aesni_enabled`. The getter also promises `B.(modifies loc_none h0 h1)`, so the
caller need not frame any global CPU-cache location merely to query a feature.

### 2.2 Getters

```fstar
// providers/evercrypt/EverCrypt.AutoConfig2.fsti:26-38
val has_shaext: getter Vale.X64.CPU_Features_s.sha_enabled
val has_aesni: getter Vale.X64.CPU_Features_s.aesni_enabled
val has_pclmulqdq: getter Vale.X64.CPU_Features_s.pclmulqdq_enabled
val has_avx2: getter Vale.X64.CPU_Features_s.avx2_enabled
val has_avx: getter Vale.X64.CPU_Features_s.avx_enabled
val has_bmi2: getter Vale.X64.CPU_Features_s.bmi2_enabled
val has_adx: getter Vale.X64.CPU_Features_s.adx_enabled
val has_sse: getter Vale.X64.CPU_Features_s.sse_enabled
val has_movbe: getter Vale.X64.CPU_Features_s.movbe_enabled
val has_rdrand: getter Vale.X64.CPU_Features_s.rdrand_enabled
(** At the moment, has_avx512 contains the AVX512_F, AVX512_DQ, AVX512_BW and AVX512_VL flags
    See Vale.X64.CPU_Features_s for more details. **)
val has_avx512: getter Vale.X64.CPU_Features_s.avx512_enabled
```

| Getter | True-branch fact |
|---|---|
| `has_shaext` | `sha_enabled` |
| `has_aesni` | `aesni_enabled` |
| `has_pclmulqdq` | `pclmulqdq_enabled` |
| `has_avx2` | `avx2_enabled` |
| `has_avx` | `avx_enabled` |
| `has_bmi2` | `bmi2_enabled` |
| `has_adx` | `adx_enabled` |
| `has_sse` | `sse_enabled` |
| `has_movbe` | `movbe_enabled` |
| `has_rdrand` | `rdrand_enabled` |
| `has_avx512` | `avx512_enabled` |

### 2.3 Footprint, `recall`, and `init`

```fstar
// providers/evercrypt/EverCrypt.AutoConfig2.fsti:40-58
(** A set of functions that modify the global cached results. For this, the
  client needs to reason about the abstract footprint. *)

val fp: unit -> GTot B.loc

(* A client that needs to allocate first then call init should use recall before
  anything else; this way, the client will be able to derive disjointness of their
  allocations and of fp. *)
val recall: unit -> Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    B.(loc_not_unused_in h1 `loc_includes` (fp ())) /\ h0 == h1))

(* By default, all feature flags are disabled. A client must call init to get
  meaningful results from the various has_* functions. *)
val init: unit -> Stack unit
  (requires (fun _ -> True))
  (ensures (fun h0 _ h1 ->
    B.modifies (fp ()) h0 h1))
```

`fp ()` is the abstract Low* footprint of the global flag cache. `init` may
modify that footprint and must be called before `has_*` gives meaningful
run-time information. `recall` changes no memory (`h0 == h1`) but recalls that
`fp ()` is included in live memory; clients that allocate first can then derive
that their fresh allocations are disjoint from the global flag state.

### 2.4 Disablers

```fstar
// providers/evercrypt/EverCrypt.AutoConfig2.fsti:60-79
inline_for_extraction
let disabler = unit -> Stack unit
  (requires (fun _ -> true))
  (ensures (fun h0 _ h1 -> B.(modifies (fp ()) h0 h1)))

(* In order to selectively take codepaths, a client might disable either feature
  flags, to, say, pick one Vale implementation over another. Alternatively, if the
  codepath taken does not depend on a particular feature flag (e.g. OpenSSL vs.
  BCrypt) the client can disable a provider entirely. *)
val disable_avx2: disabler
val disable_avx: disabler
val disable_bmi2: disabler
val disable_adx: disabler
val disable_shaext: disabler
val disable_aesni: disabler
val disable_pclmulqdq: disabler
val disable_sse: disabler
val disable_movbe: disabler
val disable_rdrand: disabler
val disable_avx512: disabler
```

Every disabler may modify only `fp ()`. Disablers are: `disable_avx2`,
`disable_avx`, `disable_bmi2`, `disable_adx`, `disable_shaext`,
`disable_aesni`, `disable_pclmulqdq`, `disable_sse`, `disable_movbe`,
`disable_rdrand`, and `disable_avx512`.

### 2.5 Vector guards

```fstar
// providers/evercrypt/EverCrypt.AutoConfig2.fsti:81-103
(** Some predicates to dynamically guard the vectorized code *)
(* Note that those predicates don't check [EverCrypt.TargetConfig.hacl_can_compile_vec128],
 * [EverCrypt.TargetConfig.hacl_can_compile_vale], etc.
 * The reason is that the above booleans are static preconditions, checked at
 * compilation time. The F* code must thus be guard the following way (note that
 * the order of the arguments is important for syntactic reasons):
 * [> if EverCrypt.TargetConfig.hacl_can_compile_vec128 && has_vec128 ... then
 * Leading to the following C code:
 * [> #if defined(COMPILE_128)
 * [>   if has_vec128 ... { ... }
 * [> #endif
 * Note that if one forgets to guard the code with flags like
 * [EverCrypt.TargetConfig.hacl_can_compile_vec128], the code will not compile on platforms
 * not satisfying the requirements.
 *)

noextract
let vec128_enabled = Vale.X64.CPU_Features_s.avx_enabled || vec128_not_avx_enabled
noextract
let vec256_enabled = Vale.X64.CPU_Features_s.avx2_enabled || vec256_not_avx2_enabled

val has_vec128: getter vec128_enabled
val has_vec256: getter vec256_enabled
```

`has_vec128` proves `avx_enabled || vec128_not_avx_enabled`; `has_vec256` proves
`avx2_enabled || vec256_not_avx2_enabled`. They deliberately do not check
compile-time availability.

---

## 3. `EverCrypt.TargetConfig`

Non-x64 vector detection is hand-written in C:

```fstar
// providers/evercrypt/EverCrypt.TargetConfig.fsti:6-22
// Those functions are called on non-x64 platforms for which the feature detection
// is not covered by vale's CPUID support; therefore, we hand-write in C ourselves.
// See the hand-written evercrypt_targetconfig.h for more explanations.
val vec128_not_avx_enabled : bool
val vec256_not_avx2_enabled : bool

val has_vec128_not_avx : unit ->
  Stack bool (requires fun _ -> True)
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b ==> vec128_not_avx_enabled)))

val has_vec256_not_avx2 : unit ->
  Stack bool (requires fun _ -> True)
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b ==> vec256_not_avx2_enabled)))
```

The compile-time flags are `[@@ CIfDef]` booleans:

```fstar
// providers/evercrypt/EverCrypt.TargetConfig.fsti:24-43
/// A set of flags that are compiled in C as #if preprocessor statements. Branch
/// on these flags to avoid generating a reference at link-time. For instance,
/// calling CPUID is guarded by ``x64``, otherwise, compiling for an ARM
/// target, we would get a reference in the C code to a function for which we have
/// no implementation at link-time.

/// Note that this file is extracted with the -no-prefix-flag, meaning the
/// below macros don't have the EVERCRYPT_TARGETCONFIG_ prefix.
[@@ CIfDef ]
val hacl_can_compile_vale : bool

[@@ CIfDef ]
val hacl_can_compile_vec128 : bool

[@@ CIfDef ]
val hacl_can_compile_vec256 : bool

// Only for Curve25519 64
[@@ CIfDef ]
val hacl_can_compile_inline_asm : bool
```

The syntactic rule, quoted verbatim from `AutoConfig2`, is that the compile-time
flag must be the left operand of `&&`:

```fstar
// providers/evercrypt/EverCrypt.AutoConfig2.fsti:82-95
(* Note that those predicates don't check [EverCrypt.TargetConfig.hacl_can_compile_vec128],
 * [EverCrypt.TargetConfig.hacl_can_compile_vale], etc.
 * The reason is that the above booleans are static preconditions, checked at
 * compilation time. The F* code must thus be guard the following way (note that
 * the order of the arguments is important for syntactic reasons):
 * [> if EverCrypt.TargetConfig.hacl_can_compile_vec128 && has_vec128 ... then
 * Leading to the following C code:
 * [> #if defined(COMPILE_128)
 * [>   if has_vec128 ... { ... }
 * [> #endif
 * Note that if one forgets to guard the code with flags like
 * [EverCrypt.TargetConfig.hacl_can_compile_vec128], the code will not compile on platforms
 * not satisfying the requirements.
 *)
```

If this shape is lost, KaRaMeL may not lift the guard to `#if`; the generated C
can contain link-time references to Vale/vector code that was never compiled.
The build then fails even though the F* branch looked guarded. Correct dispatch
uses both axes: `hacl_can_compile_*` for build availability and `has_*` for
run-time CPU/provider support.

---

## 4. Vale interop as F* API

### 4.1 Feature propositions

`Vale.X64.CPU_Features_s` defines assumed CPUID/XGETBV feature
propositions. Representative declarations and derived flags:

```fstar
// vale/specs/hardware/Vale.X64.CPU_Features_s.fst:9-28
assume val aesni_enabled : bool      // CPUID.01H:ECX.AESNI[bit 25]
assume val pclmulqdq_enabled : bool  // CPUID.01H:ECX.PCLMULQDQ[bit 1]
assume val bmi2_enabled : bool       // CPUID.7.0.EBX[8]
assume val adx_enabled : bool        // CPUID.7.0.EBX[19]
assume val sha_enabled : bool        // CPUID.7.0.EBX[29]
assume val movbe_enabled : bool      // CPUID.01H.ECX.MOVBE[bit 22]
assume val rdrand_enabled : bool     // CPUID.01H.ECX.RDRAND[bit 30] = 0

let sse_enabled : bool = sse2_enabled && ssse3_enabled && sse4_1_enabled
```

```fstar
// vale/specs/hardware/Vale.X64.CPU_Features_s.fst:73-83
let avx_xcr0 : bool = sse_xcr0_enabled && avx_xcr0_enabled

let avx512_xcr0 : bool =
  avx_xcr0_enabled && opmask_xcr0_enabled && zmm_hi256_xcr0_enabled && hi16_zmm_xcr0_enabled


(* Full AVX detection *)

let avx_enabled : bool = avx_cpuid_enabled && avx_xcr0
let avx2_enabled : bool = avx2_cpuid_enabled && avx_xcr0
let avx512_enabled : bool = avx512_cpuid_enabled && avx512_xcr0
```

```

```fstar
// vale/code/arch/x64/interop/Vale.Stdcalls.X64.Aes.fsti:167-171
[@ (CCConv "stdcall") ]
val aes128_key_expansion : normal lowstar_key128_t

[@ (CCConv "stdcall") ]
val aes256_key_expansion : normal lowstar_key256_t
```

`Vale.Wrapper.X64.*` modules expose ordinary-looking Low* `val`s with buffers,
`Stack`, `requires`, and `ensures`. A real wrapper example:

```fstar
// vale/code/arch/x64/interop/Vale.Wrapper.X64.AES.fsti:41-66
inline_for_extraction
let key_expansion_st (a: algorithm { a = AES_128 \/ a = AES_256 }) =
  (input_key_b:uint8_p) ->
  (output_key_expansion_b:uint8_p) ->
  Stack unit
    (requires fun h0 ->
      B.disjoint input_key_b output_key_expansion_b /\

      B.live h0 input_key_b /\ B.live h0 output_key_expansion_b /\

      B.length input_key_b = key_length a /\
      B.length output_key_expansion_b = key_offset a /\

      aesni_enabled && avx_enabled && sse_enabled)
    (ensures fun h0 _ h1 ->
      B.modifies (B.loc_buffer output_key_expansion_b) h0 h1 /\

      (let key = seq_nat8_to_seq_nat32_LE (seq_uint8_to_seq_nat8 (B.as_seq h0 input_key_b)) in
      Seq.equal (B.as_seq h1 output_key_expansion_b)
         (seq_nat8_to_seq_uint8 (le_seq_quad32_to_bytes (key_to_round_keys_LE a key)))))

inline_for_extraction
val aes128_key_expansion_stdcall: key_expansion_st AES_128

inline_for_extraction
val aes256_key_expansion_stdcall: key_expansion_st AES_256
```

Because scalar C and assembly providers can satisfy the same F* signature,
EverCrypt can dispatch to either and prove the same postcondition. The wrapper
is what makes assembly appear to F* clients as an ordinary Low* function.

---

## 5. Randomness

### 5.1 `Lib.RandomBuffer.System`

This is an **assumed** F* interface realized by hand-written C
`lib/c/Lib_RandomBuffer_System.c`. It is trusted, not verified. The deprecated
API only says the buffer may be modified:

```fstar
// lib/Lib.RandomBuffer.System.fsti:12-19
[@@ deprecated "random_crypto" ]
val randombytes:
    buf: buffer uint8
  -> len: size_t{v len == length buf} ->
  Stack bool
  (requires (fun h -> live h buf))
  (ensures (fun h0 _ h1 -> modifies1 buf h0 h1))
```

The current API uses a ghost entropy pointer:

```fstar
// lib/Lib.RandomBuffer.System.fsti:20-41
// In order to be able to reason about disjointness, we make the entropy pointer
// recallable. Use Lib.Buffer.recall to recall that entropy_p is included
// in the current memory snapshot.
val entropy_p : b:lbuffer (Ghost.erased entropy) 1ul{ recallable b }

/// This function waits until it has received enough entropy before
/// generating random bytes. Note that it may wait for some time.
val crypto_random:
     buf: buffer uint8
  -> len: size_t{v len == length buf} ->
  Stack unit
  (requires (fun h0 ->
    live h0 buf /\
    disjoint buf entropy_p))
  (ensures (fun h0 () h1 ->
    modifies2 buf entropy_p h0 h1 /\
    begin
    let e0_v = B.deref h0 (entropy_p <: B.buffer (Ghost.erased entropy)) in
    let e1_v = B.deref h1 (entropy_p <: B.buffer (Ghost.erased entropy)) in
    let buf_v = B.as_seq h1 buf in
    (Ghost.reveal e1_v, buf_v) == R.crypto_random e0_v (size_v len)
    end))
```

The postcondition says the output bytes and next ghost entropy equal the
abstract `R.crypto_random` transition. It says nothing about statistical quality
or cryptographic strength of the randomness. That quality is part of the
trusted C/OS boundary.

### 5.2 `Lib.RandomSequence`

```fstar
// lib/Lib.RandomSequence.fsti:8-20
///
/// This module uses the OCaml cryptokit package to provide Hardware randomness
/// (Currently only usable from platforms that support RDRAND)
///

val entropy: Type0
val entropy0: entropy


val crypto_random: entropy -> len:size_nat -> Tot (entropy & lbytes len)

val unsound_crypto_random1: len:size_nat -> Tot (option (lbytes len))

val unsound_crypto_random2: len:size_nat -> Tot (lbytes len)
```

### 5.3 `Lib.Memzero0`

```fstar
// lib/Lib.Memzero0.fsti:1-9
/// Separate module that does not depend on Lib.Buffer to avoid a dependency loop.
module Lib.Memzero0

module B = LowStar.Buffer

/// This variant is polymorphic and is implemented in C.
val memzero: #a:Type0 -> b:B.buffer a -> l:UInt32.t { B.len b == l } -> FStar.HyperStack.ST.Stack unit
  (requires fun h -> B.live h b)
  (ensures fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1))
```

The visible interface does not state that bytes become zero; from this contract
alone, that content fact is unconfirmed.

---

## 6. DRBG in F*

`EverCrypt.DRBG` wraps HMAC-DRBG and uses `Lib.RandomBuffer.System` as the
entropy source. The relationship to SP 800-90A is explicit:

```fstar
// providers/evercrypt/EverCrypt.DRBG.fsti:14-49
/// HMAC-DRBG
///
/// See 10.1.2 and B.2 of
/// https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-90Ar1.pdf
///
/// This module implements
/// - HMAC_DRBG_Instantiate_function
/// - HMAC_DRBG_Reseed_function
/// - HMAC_DRBG_Generate_function
/// - HMAC_DRBG_Uninstantiate_function
///
/// Internally, it uses Lib.RandomBuffer.System as the Get_entropy_input function,
/// for instantiation, reseeding, and prediction resistance.
///
/// - Supports SHA-1, SHA2-256, SHA2-384 and SHA2-512
///
/// - Supports reseeding
///
/// - Supports optional personalization_string for instantiation
///
/// - Supports optional additional_input for reseeding and generation
///
/// - Always provides prediction resistance (i.e. reseeds before generation)
///
/// - The internal state is (Key,V,reseed_counter)
///
/// - The security_strength is the HMAC-strength of the hash algorithm as per p.54 of
///   https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-57pt1r4.pdf
///
/// - The minimum entropy for instantiation is 3/2 * security_strength.
///    - entropy_input must have at least security_strength bits.
///    - nonce must have at least 1/2 security_strength bits.
///    - entropy_input and nonce can have at most max_length = 2^16 bits.
///
/// - At most max_number_of_bits_per_request = 2^16 bits can be generated per request.
```

State abstraction, invariant, footprint, framing, and representation:

```fstar
// providers/evercrypt/EverCrypt.DRBG.fsti:87-127
/// This has a @CAbstractStruct attribute in the implementation.
/// See https://github.com/FStarLang/karamel/issues/153
/// 
/// It instructs KaRaMeL to include only a forward-declarartion
/// in the header file, forcing code to always use `state_s` abstractly
/// through a pointer.
inline_for_extraction noextract
val state_s: supported_alg -> Type0

inline_for_extraction noextract
let state a = B.pointer (state_s a)

inline_for_extraction noextract
val freeable_s: #a:supported_alg -> st:state_s a -> Type0

inline_for_extraction noextract
let freeable (#a:supported_alg) (st:state a) (h:HS.mem) =
  B.freeable st /\ freeable_s (B.deref h st)

val footprint_s: #a:supported_alg -> state_s a -> GTot B.loc

let footprint (#a:supported_alg) (st:state a) (h:HS.mem) =
  B.loc_union (B.loc_addr_of_buffer st) (footprint_s (B.deref h st))

inline_for_extraction noextract
val invariant_s: #a:supported_alg -> state_s a -> HS.mem -> Type0

inline_for_extraction noextract
let invariant (#a:supported_alg) (st:state a) (h:HS.mem) =
  B.live h st /\
  B.loc_disjoint (B.loc_addr_of_buffer st) (footprint_s (B.deref h st)) /\
  invariant_s (B.deref h st) h

inline_for_extraction noextract
let disjoint_st (#t:Type) (#a:supported_alg) 
  (st:state a) (b:B.buffer t) (h:HS.mem) 
=
  B.loc_disjoint (footprint st h) (B.loc_buffer b)
 
val repr: #a:supported_alg -> st:state a -> h:HS.mem -> GTot (S.state a)
```

```fstar
// providers/evercrypt/EverCrypt.DRBG.fsti:145-159
/// Needed to prove that the footprint is disjoint from any fresh location
val invariant_loc_in_footprint: #a:supported_alg -> st:state a -> h:HS.mem 
  -> Lemma
  (requires invariant st h)
  (ensures  B.loc_in (footprint st h) h)
  [SMTPat (invariant st h)]

val frame_invariant: #a:supported_alg -> l:B.loc -> st:state a -> h0:HS.mem -> h1:HS.mem 
  -> Lemma
  (requires
    invariant st h0 /\
    B.loc_disjoint l (footprint st h0) /\
    B.modifies l h0 h1)
  (ensures
    invariant st h1 /\
    repr st h0 == repr st h1)
```

Allocation functions (`alloca`, `create_in`, `create`) establish fresh state,
`invariant`, and when heap-allocated `freeable`; their pattern is the standard
Low* state pattern covered by [fstar-api.md](fstar-api.md).


The four main contract abbreviations:

```fstar
// providers/evercrypt/EverCrypt.DRBG.fsti:203-230
inline_for_extraction noextract
let instantiate_st (a:supported_alg) =
    st:state a
  -> personalization_string:B.buffer uint8
  -> personalization_string_len:size_t
  -> Stack bool
  (requires fun h0 ->
    invariant st h0 /\
    B.live h0 personalization_string /\ 
    disjoint_st st personalization_string h0 /\
    B.length personalization_string = v personalization_string_len)
  (ensures  fun h0 b h1 ->
    S.hmac_input_bound a;
    if not b then
      B.modifies B.loc_none h0 h1
    else
      v personalization_string_len <= S.max_personalization_string_length /\
      invariant st h1 /\
      preserves_freeable st h0 h1 /\
      footprint st h0 == footprint st h1 /\
      B.modifies (footprint st h0) h0 h1 /\
      (exists entropy_input nonce.
        S.min_length a <= Seq.length entropy_input /\
        Seq.length entropy_input <= S.max_length /\
        S.min_length a / 2 <= Seq.length nonce /\
        Seq.length nonce <= S.max_length /\
        repr st h1 ==
        S.instantiate entropy_input nonce (B.as_seq h0 personalization_string)))
```

```fstar
// providers/evercrypt/EverCrypt.DRBG.fsti:233-258
inline_for_extraction noextract
let reseed_st (a:supported_alg) =
    st:state a
  -> additional_input:B.buffer uint8
  -> additional_input_len:size_t
  -> Stack bool
  (requires fun h0 ->
    invariant st h0 /\
    B.live h0 additional_input /\
    disjoint_st st additional_input h0 /\
    B.length additional_input = v additional_input_len)
  (ensures  fun h0 b h1 ->
    S.hmac_input_bound a;
    if not b then
      B.modifies B.loc_none h0 h1
    else
      v additional_input_len <= S.max_additional_input_length /\
      footprint st h0 == footprint st h1 /\
      invariant st h1 /\
      preserves_freeable st h0 h1 /\
      B.modifies (footprint st h0) h0 h1 /\
      (exists entropy_input.
        S.min_length a <= Seq.length entropy_input /\
        Seq.length entropy_input <= S.max_length /\
        repr st h1 ==
        S.reseed (repr st h0) entropy_input (B.as_seq h0 additional_input)))
```

```fstar
// providers/evercrypt/EverCrypt.DRBG.fsti:261-295
inline_for_extraction noextract
let generate_st (a:supported_alg) =
    output:B.buffer uint8
  -> st:state a
  -> n:size_t
  -> additional_input:B.buffer uint8
  -> additional_input_len:size_t
  -> Stack bool
  (requires fun h0 ->
    invariant st h0 /\
    B.live h0 output /\ B.live h0 additional_input /\
    disjoint_st st output h0 /\ disjoint_st st additional_input h0 /\
    B.disjoint output additional_input /\
    B.length additional_input = v additional_input_len /\
    v n = B.length output)
  (ensures  fun h0 b h1 ->
    S.hmac_input_bound a;
    if not b then
      B.modifies B.loc_none h0 h1
    else
      v n <= S.max_output_length /\
      v additional_input_len <= S.max_additional_input_length /\
      invariant st h1 /\
      preserves_freeable st h0 h1 /\
      footprint st h0 == footprint st h1 /\
      B.modifies (B.loc_union (B.loc_buffer output) (footprint st h0)) h0 h1 /\
      (exists entropy_input.
       S.min_length a <= Seq.length entropy_input /\
       Seq.length entropy_input <= S.max_length /\
       (let st1 = S.reseed (repr st h0) entropy_input (B.as_seq h0 additional_input) in
        match S.generate st1 (v n) (B.as_seq h0 additional_input) with
        | None -> False // Always reseeds, so generation cannot fail
        | Some (out, st_) ->
          repr st h1 == st_ /\
          B.as_seq h1 output == out)))
```

```fstar
// providers/evercrypt/EverCrypt.DRBG.fsti:298-303
inline_for_extraction noextract
let uninstantiate_st (a:supported_alg) =
    st:state a
  -> ST unit
  (requires fun h0 -> freeable st h0 /\ invariant st h0)
  (ensures  fun h0 _ h1 -> B.modifies (footprint st h0) h0 h1)
```

And the agile exported values:

```fstar
// providers/evercrypt/EverCrypt.DRBG.fsti:306-349
/// Agile variants that dispatch dynamically to the appropriate monomorphic variants above
/// by pattern matching on the struct tag (rather than the algorithm, which is erased)

(** @type: true 
*)
[@@ Comment "Instantiate the DRBG.

@param st Pointer to DRBG state.
@param personalization_string Pointer to `personalization_string_len` bytes of memory where personalization string is read from.
@param personalization_string_len Length of personalization string.

@return True if and only if instantiation was successful." ]
val instantiate: a:(Ghost.erased supported_alg) -> instantiate_st (Ghost.reveal a)

(** @type: true 
*)
[@@ Comment "Reseed the DRBG.

@param st Pointer to DRBG state.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
@param additional_input_input_len Length of additional input.

@return True if and only if reseed was successful." ]
val reseed: a:(Ghost.erased supported_alg) -> reseed_st (Ghost.reveal a)

(** @type: true 
*)
[@@ Comment "Generate output.

@param output Pointer to `n` bytes of memory where random output is written to.
@param st Pointer to DRBG state.
@param n Length of desired output.
@param additional_input_input Pointer to `additional_input_input_len` bytes of memory where additional input is read from.
@param additional_input_input_len Length of additional input.

@return True if and only if generate was successful." ]
val generate:  a:(Ghost.erased supported_alg) -> generate_st (Ghost.reveal a)

(** @type: true
*)
[@@ Comment "Uninstantiate and free the DRBG.

@param st Pointer to DRBG state." ]
val uninstantiate: a:(Ghost.erased supported_alg) -> uninstantiate_st (Ghost.reveal a)
```

`repr st h` connects concrete state to `Spec.HMAC_DRBG.state`; successful calls
state that the new representation equals the corresponding SP 800-90A spec
transition. The entropy values are existential because EverCrypt obtains them
through the trusted OS randomness shim.

---

## 7. HPKE in F*

HPKE is generated from abstract interfaces, a generic implementation, and a

### 7.1 Abstract parameter interfaces

AEAD:

```fstar
// code/hpke/Hacl.HPKE.Interface.AEAD.fsti:19-68
inline_for_extraction noextract
let aead_encrypt_st (a:S.aead) =
     _:squash (S.Seal? a /\ S.is_valid_aead a)
  -> key:kv (S.Seal?.alg a)
  -> nonce:iv (S.Seal?.alg a)
  -> alen:size_t{v alen <= AEAD.max_length (S.Seal?.alg a)}
  -> aad:lbuffer uint8 alen
  -> len:size_t{v len + 16 <= max_size_t}
  -> input:lbuffer uint8 len
  -> output:lbuffer uint8 (size (v len + 16)) ->
  Stack unit
  (requires fun h ->
    live h key /\ live h nonce /\ live h aad /\
    live h input /\ live h output /\
    disjoint key output /\ disjoint nonce output /\
    eq_or_disjoint input output /\ disjoint aad output)
  (ensures  fun h0 _ h1 -> modifies (loc output) h0 h1 /\
    (as_seq h1 output) `Seq.equal`
    AEAD.encrypt #(S.Seal?.alg a) (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 aad) (as_seq h0 input))

inline_for_extraction noextract
let aead_decrypt_st (a:S.aead) =
    _:squash (S.Seal? a /\ S.is_valid_aead a)
  -> key:kv (S.Seal?.alg a)
  -> nonce:iv (S.Seal?.alg a)
  -> alen:size_t{v alen <= AEAD.max_length (S.Seal?.alg a)}
  -> aad:lbuffer uint8 alen
  -> len:size_t{v len <= AEAD.max_length (S.Seal?.alg a) /\ v len + 16 <= max_size_t}
  -> input:lbuffer uint8 len
  -> output:lbuffer uint8 (size (v len  + 16)) ->
  Stack UInt32.t
  (requires fun h ->
    live h key /\ live h nonce /\ live h aad /\
    live h input /\ live h output /\
    eq_or_disjoint input output)
  (ensures  fun h0 z h1 -> modifies1 input h0 h1 /\
   (let plain = AEAD.decrypt #(S.Seal?.alg a) (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 aad) (as_seq h0 output) in
    match z with
    | 0ul -> Some? plain /\ as_seq h1 input `Seq.equal` Some?.v plain // decryption succeeded
    | 1ul -> None? plain
    | _ -> false)  // decryption failed
  )

[@ Meta.Attribute.specialize]
noextract
val aead_encrypt: #cs:S.ciphersuite -> aead_encrypt_st (S.aead_of_cs cs)

[@ Meta.Attribute.specialize]
noextract
val aead_decrypt: #cs:S.ciphersuite -> aead_decrypt_st (S.aead_of_cs cs)
```

DH/hash/HKDF specialization nodes:

```fstar
// code/hpke/Hacl.HPKE.Interface.DH.fst:27-65
inline_for_extraction noextract
let dh_st (a:DH.algorithm) (p:Type0) =
     o:lbuffer uint8 (nsize_public a)
  -> k:lbuffer uint8 (nsize_key a)
  -> i:lbuffer uint8 (nsize_public a)
  -> Stack UInt32.t
     (requires fun h0 ->
       p /\
       live h0 o /\ live h0 k /\ live h0 i /\
       disjoint o i /\ disjoint o k)
     (ensures fun h0 result h1 -> modifies (loc o) h0 h1 /\ (
       let output = DH.dh a (as_seq h0 k) (as_seq h0 i) in
       match result with
       | 0ul -> Some? output /\ as_seq h1 o `Seq.equal` Some?.v output // DH succeeded
       | 1ul -> None? output
       | _ -> False))

inline_for_extraction noextract
let secret_to_public_st (a: DH.algorithm) (p:Type0) =
    o:lbuffer uint8 (nsize_public a)
  -> i:lbuffer uint8 (nsize_key a)
  -> Stack UInt32.t
    (requires fun h0 ->
      p /\
      live h0 o /\ live h0 i /\ disjoint o i)
    (ensures  fun h0 result h1 -> modifies (loc o) h0 h1 /\
      (let output = DH.secret_to_public a (as_seq h0 i) in
      match result with
      | 0ul -> Some? output /\ as_seq h1 o `Seq.equal` Some?.v output
      | 1ul -> None? output
      | _ -> False))

[@ Meta.Attribute.specialize]
noextract
assume val dh: #a:S.ciphersuite -> dh_st (S.kem_dh_of_cs a) True

[@ Meta.Attribute.specialize]
noextract
assume val secret_to_public: #a:S.ciphersuite -> secret_to_public_st (S.kem_dh_of_cs a) True
```

```fstar
// code/hpke/Hacl.HPKE.Interface.Hash.fst:6-17
[@ Meta.Attribute.specialize ]
noextract
assume val hash: #cs:S.ciphersuite -> Hash.hash_st (S.hash_of_cs cs)

(** Instantiations of hash **)

inline_for_extraction noextract
let hash_sha256 : Hash.hash_st Spec.Agile.Hash.SHA2_256 =
  Hacl.Streaming.SHA2.hash_256
inline_for_extraction noextract
let hash_sha512 : Hash.hash_st Spec.Agile.Hash.SHA2_512 =
  Hacl.Streaming.SHA2.hash_512
```

```fstar
// code/hpke/Hacl.HPKE.Interface.HKDF.fst:7-21
[@ Meta.Attribute.specialize ]
noextract
assume val hkdf_extract: #cs:S.ciphersuite -> HK.extract_st (S.hash_of_cs cs)

[@ Meta.Attribute.specialize ]
noextract
assume val hkdf_expand: #cs:S.ciphersuite -> HK.expand_st (S.hash_of_cs cs)

[@ Meta.Attribute.specialize ]
noextract
assume val hkdf_extract_kem: #cs:S.ciphersuite -> HK.extract_st (S.kem_hash_of_cs cs)

[@ Meta.Attribute.specialize ]
noextract
assume val hkdf_expand_kem: #cs:S.ciphersuite -> HK.expand_st (S.kem_hash_of_cs cs)
```

The `assume val`s are specialization holes in the generic call graph, not a C
API promise. Concrete instantiations replace them during monomorphization.

### 7.2 Generic implementation contracts

```fstar
// code/hpke/Hacl.Impl.HPKE.fsti:31-39
val context_s (cs:S.ciphersuite) : Type0
val ctx_loc (#cs:S.ciphersuite) (ctx:context_s cs) : GTot B.loc
val ctx_invariant (#cs:S.ciphersuite) (h:mem) (ctx:context_s cs) : GTot prop
val as_ctx (#cs:S.ciphersuite) (h:mem) (ctx:context_s cs) : GTot (S.encryption_context cs)

val frame_ctx (#cs:S.ciphersuite) (ctx:context_s cs) (l:B.loc) (h0 h1:mem)
  : Lemma (requires ctx_invariant h0 ctx /\ B.loc_disjoint (ctx_loc ctx) l /\ modifies l h0 h1)
          (ensures ctx_invariant h1 ctx /\ as_ctx h0 ctx == as_ctx h1 ctx)
          [SMTPat (modifies l h0 h1); SMTPat (ctx_invariant h0 ctx)]
```

```fstar
// code/hpke/Hacl.Impl.HPKE.fsti:41-91
inline_for_extraction noextract
let setupBaseS_st (cs:S.ciphersuite) (p:Type0) =
     o_pkE: key_dh_public cs
  -> o_ctx: context_s cs
  -> skE: key_dh_secret cs
  -> pkR: serialized_point_dh cs
  -> infolen: size_t{v infolen <= max_length_info (S.hash_of_cs cs)}
  -> info: lbuffer uint8 infolen
  -> Stack UInt32.t
     (requires fun h0 ->
        p /\
        live h0 o_pkE /\
        ctx_invariant h0 o_ctx /\
        live h0 skE /\ live h0 pkR /\ live h0 info /\
        disjoint o_pkE skE /\ disjoint o_pkE pkR /\ disjoint o_pkE info /\
        B.loc_disjoint (ctx_loc o_ctx) (loc info) /\
        B.loc_disjoint (loc o_pkE) (ctx_loc o_ctx))
     (ensures fun h0 result h1 -> modifies (loc o_pkE |+| ctx_loc o_ctx) h0 h1 /\
       (let output = S.setupBaseS cs (as_seq h0 skE) (as_seq h0 pkR) (as_seq h0 info) in
        match result with
        | 0ul -> Some? output /\ (let pkE, ctx = Some?.v output in
          as_seq h1 o_pkE == pkE /\
          as_ctx h1 o_ctx == ctx)
        | 1ul -> None? output
        | _ -> False
        )
     )

inline_for_extraction noextract
let setupBaseR_st (cs:S.ciphersuite) (p:Type0) =
     o_ctx : context_s cs
  -> pkE: key_dh_public cs
  -> skR: key_dh_secret cs
  -> infolen: size_t{v infolen <= max_length_info (S.hash_of_cs cs)}
  -> info: lbuffer uint8 infolen
  -> Stack UInt32.t
     (requires fun h0 ->
        p /\
        ctx_invariant h0 o_ctx /\
        live h0 pkE /\ live h0 skR /\ live h0 info /\
        B.loc_disjoint (ctx_loc o_ctx) (loc info)
      )
     (ensures fun h0 result h1 -> modifies (ctx_loc o_ctx) h0 h1 /\
       (let output = S.setupBaseR cs (as_seq h0 pkE) (as_seq h0 skR) (as_seq h0 info) in
       match result with
       | 0ul -> Some? output /\ (let ctx = Some?.v output in
         as_ctx h1 o_ctx == ctx)
       | 1ul -> None? output
       | _ -> False
       )
     )
```

```fstar
// code/hpke/Hacl.Impl.HPKE.fsti:93-160
(* The error code here is not exact w.r.t. the spec.
   The reason is that, in the spec, the overflow of an internal counter is defined
   when it runs above 2**96.
   In the code, this counter is represented as a uint64, so the overflow occurs earlier.
   Apart from this case, the behaviour of the impl and the spec should be identical *)
inline_for_extraction noextract
let sealBase_st (cs:S.ciphersuite) (p:Type0) =
     skE: key_dh_secret cs { S.is_valid_not_export_only_ciphersuite cs }
  -> pkR: serialized_point_dh cs
  -> infolen: size_t {v infolen <= max_length_info (S.hash_of_cs cs)}
  -> info: lbuffer uint8 infolen
  -> aadlen: size_t {v aadlen <= SAEAD.max_length (S.aead_alg_of cs)}
  -> aad: lbuffer uint8 aadlen
  -> plainlen: size_t {v plainlen <= SAEAD.max_length (S.aead_alg_of cs) /\ v plainlen + 16 <= max_size_t}
  -> plain: lbuffer uint8 plainlen
  -> o_enc: key_dh_public cs
  -> o_ct: lbuffer uint8 (size (v plainlen +  16))
  -> Stack UInt32.t
       (requires fun h0 ->
         p /\
         live h0 o_enc /\ live h0 o_ct /\
         live h0 skE /\ live h0 pkR /\ live h0 info /\
         live h0 aad /\ live h0 plain /\
         disjoint o_enc skE /\ disjoint o_enc pkR /\ disjoint o_enc info /\
         disjoint o_enc aad /\ disjoint o_enc plain /\
         disjoint o_ct skE /\ disjoint o_ct pkR /\ disjoint o_ct info /\
         disjoint o_ct aad /\ disjoint o_ct plain /\ disjoint o_ct o_enc
       )
       (ensures fun h0 result h1 -> modifies (loc o_enc |+| loc o_ct) h0 h1 /\
         (let sealed = S.sealBase cs (as_seq h0 skE) (as_seq h0 pkR) (as_seq h0 info) (as_seq h0 aad) (as_seq h0 plain) in
         match result with
         | 0ul -> Some? sealed /\
           (let enc, ct = Some?.v sealed in
           as_seq h1 o_enc `Seq.equal` enc /\ as_seq h1 o_ct `Seq.equal` ct)
         | 1ul -> True
         | _ -> False)
       )

(* Same issue as above for the exactness of the error code *)
inline_for_extraction noextract
let openBase_st (cs:S.ciphersuite) (p:Type0) =
     pkE: key_dh_public cs { S.is_valid_not_export_only_ciphersuite cs }
  -> skR: key_dh_secret cs
  -> infolen: size_t {v infolen <= max_length_info (S.hash_of_cs cs)}
  -> info: lbuffer uint8 infolen
  -> aadlen: size_t {v aadlen <= SAEAD.max_length (S.aead_alg_of cs)}
  -> aad: lbuffer uint8 aadlen
  -> ctlen: size_t{16 < v ctlen /\ v ctlen <= SAEAD.max_length (S.aead_alg_of cs) }
  -> ct:lbuffer uint8 ctlen
  -> o_pt: lbuffer uint8 (size (v ctlen - 16))
  -> Stack UInt32.t
       (requires fun h0 ->
         p /\
         live h0 o_pt /\
         live h0 skR /\ live h0 pkE /\ live h0 info /\
         live h0 aad /\ live h0 ct /\
         disjoint o_pt skR /\ disjoint o_pt pkE /\ disjoint o_pt info /\
         disjoint o_pt aad /\ disjoint o_pt ct
       )
       (ensures fun h0 result h1 -> modifies (loc o_pt) h0 h1 /\
         (let sealed = S.openBase cs (as_seq h0 pkE) (as_seq h0 skR) (as_seq h0 info) (as_seq h0 aad) (as_seq h0 ct) in
         match result with
         | 0ul -> Some? sealed /\
           (let pt = Some?.v sealed in
           as_seq h1 o_pt `Seq.equal` pt)
         | 1ul -> True
         | _ -> False)
       )
```

```fstar
// code/hpke/Hacl.Impl.HPKE.fsti:162-172
noextract inline_for_extraction
val setupBaseS: #cs:S.ciphersuite -> setupBaseS_st cs True

noextract inline_for_extraction
val setupBaseR: #cs:S.ciphersuite -> setupBaseR_st cs True

noextract inline_for_extraction
val sealBase: #cs:S.ciphersuite -> sealBase_st cs True

noextract inline_for_extraction
val openBase: #cs:S.ciphersuite -> openBase_st cs True
```

### 7.3 Specialize/inline mechanism

```fstar
// code/meta/Meta.Attribute.fst:1-4
module Meta.Attribute

let specialize = ()
let inline_ = ()
```

The specialization tactic rewrites a ciphersuite-indexed call graph: nodes
marked `specialize` become parameters of generated `mk_*` functions, while
nodes marked `inline_` are duplicated through the specialized call graph
(`code/meta/DOCUMENTATION.md`):

```
/// - For each specialize node ``f``, clients instantiate as follows:
///   ``let f_specialized = mk_f I1 g1_specialized ... gn_specialized``
///   where the gn_specialized have been recursively generated the same way.
```

HPKE uses `Spec.Agile.HPKE.ciphersuite` as the index:

```fstar
// code/hpke/Hacl.Meta.HPKE.fst:1-15
module Hacl.Meta.HPKE

friend Hacl.Impl.HPKE

%splice[
  hpke_setupBaseS_higher;
  hpke_setupBaseR_higher;
  hpke_sealBase_higher;
  hpke_openBase_higher
] (Meta.Interface.specialize (`Spec.Agile.HPKE.ciphersuite) [
    `Hacl.Impl.HPKE.setupBaseS;
    `Hacl.Impl.HPKE.setupBaseR;
    `Hacl.Impl.HPKE.sealBase;
    `Hacl.Impl.HPKE.openBase
])
```

A generated fixed module is ordinary F* API again:

```fstar
// code/hpke/Hacl.HPKE.Curve51_CP128_SHA256.fsti:9-18
noextract unfold
let cs:S.ciphersuite = (DH.DH_Curve25519, Hash.SHA2_256, S.Seal AEAD.CHACHA20_POLY1305, Hash.SHA2_256)

val setupBaseS: setupBaseS_st cs True

val setupBaseR: setupBaseR_st cs True

val sealBase: sealBase_st cs True

val openBase: openBase_st cs True
```

---

## 8. FrodoKEM in F*

### 8.1 Parameter-set index and sizes

```fstar
// specs/frodo/Spec.Frodo.Params.fst:12-17
type frodo_alg =
  | Frodo64 (* this variant is used only for testing purposes *)
  | Frodo640
  | Frodo976
  | Frodo1344
```

The implementation refines these indices to concrete Low\* sizes in
`Hacl.Impl.Frodo.Params`; the relevant KEM contracts below use those size
functions (`crypto_publickeybytes`, `crypto_secretkeybytes`,
`crypto_ciphertextbytes`, and `crypto_bytes`).

```fstar
inline_for_extraction noextract
let params_extracted_bits (a:S.frodo_alg) : x:size_t{v x == S.params_extracted_bits a} =
  match a with
  | S.Frodo64 | S.Frodo640 -> 2ul
  | S.Frodo976 -> 3ul
  | S.Frodo1344 -> 4ul


inline_for_extraction noextract
let crypto_bytes (a:S.frodo_alg) : x:size_t{v x == S.crypto_bytes a} =
  match a with
  | S.Frodo64 | S.Frodo640 -> 16ul
  | S.Frodo976 -> 24ul
  | S.Frodo1344 -> 32ul
```

```fstar
// code/frodo/Hacl.Impl.Frodo.Params.fst:111-134
inline_for_extraction noextract
let is_supported (a:S.frodo_gen_a) =
  match a with
  | S.SHAKE128 -> true
  | S.AES128 -> false (* unfortunately, we don't have a verified impl of aes128 in Low* *)


val frodo_gen_matrix:
    a:S.frodo_gen_a{is_supported a}
  -> n:size_t{0 < v n /\ v n * v n <= max_size_t /\ v n <= maxint U16 /\ v n % 4 = 0}
  -> seed:lbuffer uint8 16ul
  -> a_matrix:matrix_t n n
  -> Stack unit
    (requires fun h ->
      live h seed /\ live h a_matrix /\ disjoint seed a_matrix)
    (ensures  fun h0 _ h1 -> modifies1 a_matrix h0 h1 /\
      as_matrix h1 a_matrix == S.frodo_gen_matrix a (v n) (as_seq h0 seed))

[@CInline]
let frodo_gen_matrix a n seed a_matrix =
  match a with
  | S.SHAKE128 -> Hacl.Impl.Frodo.Gen.frodo_gen_matrix_shake_4x n seed a_matrix
(*  | S.AES128 -> Hacl.Impl.Frodo.Gen.frodo_gen_matrix_aes n seed a_matrix *)
```

### 8.2 Randomness and AES boundary

```fstar
// code/frodo/Hacl.Frodo.Random.fsti:14-33
val state: b:lbuffer uint8 48ul{ recallable b }

val randombytes_init_:
    entropy_input:lbuffer uint8 48ul
  -> Stack unit
    (requires fun h -> live h entropy_input)
    (ensures  fun h0 _ h1 ->
      modifies1 state h0 h1 /\
      as_seq h1 state == S.randombytes_init_ (as_seq h0 entropy_input))


val randombytes_:
    len:size_t
  -> res:lbuffer uint8 len
  -> Stack unit
    (requires fun h -> live h res)
    (ensures  fun h0 _ h1 ->
      modifies2 res state h0 h1 /\
      (let r, st = S.randombytes_ (as_seq h0 state) (v len) in
       r == as_seq h1 res /\ st == as_seq h1 state))
```

`Hacl.AES128.fsti` has no matching `.fst` in `code/frodo/`; it is an
axiomatized external in this slice.

```fstar
// code/frodo/Hacl.AES128.fsti:15-35
val aes128_key_expansion:
    key:lbuffer uint8 16ul
  -> expanded_key:lbuffer uint8 176ul
  -> Stack unit
    (requires fun h0 -> live h0 key /\ live h0 expanded_key /\ disjoint key expanded_key)
    (ensures  fun h0 _ h1 ->
      modifies1 expanded_key h0 h1 /\
      as_seq h1 expanded_key == S.aes128_key_expansion (as_seq h0 key))


val aes128_encrypt_block:
    cipher:lbuffer uint16 8ul
  -> plain:lbuffer uint16 8ul
  -> expanded_key:lbuffer uint8 176ul
  -> Stack unit
    (requires fun h0 -> live h0 cipher /\ live h0 plain /\ live h0 expanded_key)
    (ensures  fun h0 _ h1 ->
      let c = S.aes_encrypt_block S.AES128 (as_seq h0 expanded_key) (uints_to_bytes_le (as_seq h0 plain)) in
      let c' = as_seq h1 cipher in
      modifies1 cipher h0 h1 /\
      (forall (i:nat{i < 8}). c'.[i] == uint_from_bytes_le (Lib.Sequence.sub c (i * 2) 2)))
```

### 8.3 KEM contract shapes

```fstar
// code/frodo/Hacl.Frodo.KEM.fst:19-34
inline_for_extraction noextract
let crypto_kem_keypair_st (a:FP.frodo_alg) (gen_a:FP.frodo_gen_a{is_supported gen_a}) =
    pk:lbytes (crypto_publickeybytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> Stack uint32
    (requires fun h ->
      live h pk /\ live h sk /\
      disjoint pk sk /\ disjoint state pk /\ disjoint state sk)
    (ensures  fun h0 r h1 -> modifies (loc state |+| (loc pk |+| loc sk)) h0 h1 /\
      (as_seq h1 pk, as_seq h1 sk) == S.crypto_kem_keypair a gen_a (as_seq h0 state))


inline_for_extraction noextract
val crypto_kem_keypair: a:FP.frodo_alg -> gen_a:FP.frodo_gen_a{is_supported gen_a} -> crypto_kem_keypair_st a gen_a
let crypto_kem_keypair a gen_a pk sk =
  Hacl.Impl.Frodo.KEM.KeyGen.crypto_kem_keypair a gen_a pk sk
```

```fstar
// code/frodo/Hacl.Frodo.KEM.fst:37-54
inline_for_extraction noextract
let crypto_kem_enc_st (a:FP.frodo_alg) (gen_a:FP.frodo_gen_a{is_supported gen_a}) =
    ct:lbytes (crypto_ciphertextbytes a)
  -> ss:lbytes (crypto_bytes a)
  -> pk:lbytes (crypto_publickeybytes a)
  -> Stack uint32
    (requires fun h ->
      live h ct /\ live h ss /\ live h pk /\
      disjoint ct ss /\ disjoint ct pk /\ disjoint ss pk /\
      disjoint state ct /\ disjoint state ss /\ disjoint state pk)
    (ensures  fun h0 _ h1 -> modifies (loc state |+| (loc ct |+| loc ss)) h0 h1 /\
      (as_seq h1 ct, as_seq h1 ss) == S.crypto_kem_enc a gen_a (as_seq h0 state) (as_seq h0 pk))


inline_for_extraction noextract
val crypto_kem_enc: a:FP.frodo_alg -> gen_a:FP.frodo_gen_a{is_supported gen_a} -> crypto_kem_enc_st a gen_a
let crypto_kem_enc a gen_a ct ss pk =
  Hacl.Impl.Frodo.KEM.Encaps.crypto_kem_enc a gen_a ct ss pk
```

```fstar
// code/frodo/Hacl.Frodo.KEM.fst:57-73
inline_for_extraction noextract
let crypto_kem_dec_st (a:FP.frodo_alg) (gen_a:FP.frodo_gen_a{is_supported gen_a}) =
    ss:lbytes (crypto_bytes a)
  -> ct:lbytes (crypto_ciphertextbytes a)
  -> sk:lbytes (crypto_secretkeybytes a)
  -> Stack uint32
    (requires fun h ->
      live h ss /\ live h ct /\ live h sk /\
      disjoint ss ct /\ disjoint ss sk /\ disjoint ct sk)
    (ensures  fun h0 r h1 -> modifies (loc ss) h0 h1 /\
      as_seq h1 ss == S.crypto_kem_dec a gen_a (as_seq h0 ct) (as_seq h0 sk))


inline_for_extraction noextract
val crypto_kem_dec: a:FP.frodo_alg -> gen_a:FP.frodo_gen_a{is_supported gen_a} -> crypto_kem_dec_st a gen_a
let crypto_kem_dec a gen_a ss ct sk =
  Hacl.Impl.Frodo.KEM.Decaps.crypto_kem_dec a gen_a ss ct sk
```

Randomness enters through `Hacl.Frodo.Random.state` in keypair and encapsulation:
the contracts require disjointness from `state` and modify it. Decapsulation is
deterministic and modifies only `ss`.

Fixed parameter modules bind the generic API to a parameter set and `SHAKE128`.
For example:

```fstar
// code/frodo/Hacl.Frodo640.fst:29-39
val crypto_kem_keypair: crypto_kem_keypair_st FP.Frodo640 FP.SHAKE128
let crypto_kem_keypair pk sk =
Fixed modules such as `Hacl.Frodo640`, `Hacl.Frodo976`, and
`Hacl.Frodo1344` bind these generic contracts to one parameter set and
`SHAKE128`; `Frodo64` is marked testing-only in the spec.


## 9. Notes for reimplementers

1. **Feature detection as proposition.** A true CPU getter result must yield a
   proof-like fact usable by optimized code preconditions. A false result should
   not prove the opposite.
2. **Compile-time/run-time split.** `hacl_can_compile_*` answers "was this code
   built?"; `has_*` answers "may this process take this path now?" Keep the
   `hacl_can_compile_* && has_*` syntactic shape so unavailable code is removed
   by the C preprocessor.
3. **Trusted shims stay narrow.** OS randomness, zeroization, external AES, and
   assembly ABI calls are trusted/assumed at specific interfaces. Do not let
   their trust leak into unrelated verified code.
