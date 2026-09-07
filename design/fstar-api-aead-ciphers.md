# F* API design: AEAD, stream ciphers, and NaCl box

This document covers the F* interface surface for AEAD, stream ciphers, and NaCl box/secretbox in HACL*/EverCrypt. It is for verified Low*/F* clients and reimplementers. It is not the C API; see [`design/api-aead-ciphers.md`](api-aead-ciphers.md). Cross-reference [`design/README.md`](README.md), [`design/fstar-api.md`](fstar-api.md) for the memory model/effects/pattern, [`design/fstar-specs.md`](fstar-specs.md) for pure specs, [`design/fstar-client-guide.md`](fstar-client-guide.md), [`design/implementation.md`](implementation.md), and [`design/surprises.md`](surprises.md).

## 1. Orientation

Verified clients should usually depend on `EverCrypt.AEAD` for agile stateful AEAD, `Spec.Agile.AEAD` for the pure specs/theorems named in postconditions, `EverCrypt.Error` for result codes, `EverCrypt.AutoConfig2`/`EverCrypt.TargetConfig` for AES-GCM hardware facts, `EverCrypt.Cipher` or `Hacl.Chacha20`/`Hacl.Salsa20` for stream ciphers, `EverCrypt.Chacha20Poly1305` for one-shot non-agile AEAD, and `Hacl.NaCl` for box/secretbox.

The top of `EverCrypt.AEAD.fsti` defines the central usage protocol:

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:1-13`

```fstar
module EverCrypt.AEAD

/// The new AEAD interface for EverCrypt, which supersedes the functions found
/// in EverCrypt.fst
///
/// The expected usage for this module is as follows:
/// - client expands key, obtaining an ``expanded_key a``
/// - client uses ``encrypt``/``decrypt`` with the same ``expanded_key a`` repeatedly.
///
/// This usage protocol is enforced for verified F* clients but, naturally,
/// isn't for C clients.

module S = FStar.Seq
```
The key point is that the protocol is enforced only for verified F* clients. F* clients cannot call stateful `encrypt`/`decrypt` unless they own an `invariant h s` for a state created by `create_in` or `alloca`, and those creation postconditions record the original key using `as_kv`. C clients see a pointer API and runtime errors, so the C documentation can only instruct them to follow this protocol; the F* interface proves it.

## 2. Stateful abstraction pattern in `EverCrypt.AEAD`

### 2.1 Abstract state, freeability, footprint

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:32-63`

```fstar


/// Abstract footprints, with the same machinery as EverCrypt.Hash
/// --------------------------------------------------------------
///
/// Differences from EverCrypt.Hash include: combined framing lemma, the
/// equivalent of the ``repr`` function does *not* require the memory, and order
/// of arguments to be in line with ``B.as_seq``, etc. which take the memory
/// first.

[@@ CAbstractStruct; Comment "Both encryption and decryption require a state that holds the key.
The state may be reused as many times as desired."]
val state_s: alg -> Type0

inline_for_extraction noextract
let state alg = B.pointer (state_s alg)

inline_for_extraction noextract
val freeable_s: #(a: alg) -> state_s a -> Type0

inline_for_extraction noextract
let freeable (#a: alg) (h: HS.mem) (p: state a) =
  B.freeable p /\ freeable_s (B.deref h p)

inline_for_extraction noextract
let preserves_freeable #a (s: state a) (h0 h1: HS.mem): Type0 =
  freeable h0 s ==> freeable h1 s

val footprint_s: #a:alg -> state_s a -> GTot B.loc
let footprint (#a:alg) (m: HS.mem) (s: state a) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

```
`state_s` is abstract and indexed by algorithm; `[@@ CAbstractStruct]` tells extraction it is an abstract C struct. `state` is an F*-only pointer abbreviation (`inline_for_extraction noextract`). `freeable_s` is the representation-specific freeability predicate; `freeable` combines it with `B.freeable`. `preserves_freeable` is the relational fact preserved by encrypt/decrypt. `footprint_s` hides internal mutable locations; `footprint` exposes the union of the state-cell address and hidden footprint so clients can state disjointness and frame calls.

### 2.2 Footprint union lemma and SMT pattern

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:64-82`

```fstar
// TR: the following pattern is necessary because, if we generically
// add such a pattern directly on `loc_includes_union_l`, then
// verification will blowup whenever both sides of `loc_includes` are
// `loc_union`s. We would like to break all unions on the
// right-hand-side of `loc_includes` first, using
// `loc_includes_union_r`.  Here the pattern is on `footprint_s`,
// because we already expose the fact that `footprint` is a
// `loc_union`. (In other words, the pattern should be on every
// smallest location that is not exposed to be a `loc_union`.)

let loc_includes_union_l_footprint_s
  (l1 l2: B.loc) (#a: alg) (s: state_s a)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s s) \/ B.loc_includes l2 (footprint_s s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s s))]
= B.loc_includes_union_l l1 l2 (footprint_s s)
```
This lemma is proof plumbing for location inclusion. It carries `SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s s))`, so it usually fires automatically on that goal shape. Invoke it manually only when SMT fails to combine footprint inclusions.

### 2.3 `config_pre` and CPU-feature proofs

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:84-94`

```fstar
/// The configuration preconditions
inline_for_extraction noextract
let config_pre a =
  match a with
  | AES128_GCM
  | AES256_GCM ->
      EverCrypt.TargetConfig.hacl_can_compile_vale /\
      Vale.X64.CPU_Features_s.(aesni_enabled /\ pclmulqdq_enabled /\ avx_enabled /\
                               movbe_enabled /\ sse_enabled)
  | CHACHA20_POLY1305 -> True
  | _ -> True
```
For AES-GCM, `config_pre` requires `EverCrypt.TargetConfig.hacl_can_compile_vale` and Vale CPU flags (`aesni_enabled`, `pclmulqdq_enabled`, `avx_enabled`, `movbe_enabled`, `sse_enabled`). For ChaCha20-Poly1305 it is `True`. It is `inline_for_extraction noextract`: a proof-side precondition, not a C function.

Feature getters discharge these facts by returning a Boolean whose postcondition is `b ==> flag`:

Source: `providers/evercrypt/EverCrypt.AutoConfig2.fsti:12-39`

```fstar
module B = LowStar.Buffer

(** Each flag can be queried; we cache the results in mutable global variables,
  hidden behind an abstract footprint. Calling a getter requires no reasoning
  about the abstract footprint from the client. *)

unfold
inline_for_extraction noextract
let getter (flag: bool) = unit -> Stack bool
  (requires (fun _ -> true))
  (ensures (fun h0 b h1 ->
    B.(modifies loc_none h0 h1) /\
    (b ==> flag)))

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
Source: `providers/evercrypt/EverCrypt.TargetConfig.fsti:22-39`

```fstar
    (b ==> vec256_not_avx2_enabled)))

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
```
The implementation checks those Booleans before constructing AES-GCM state; on the true branch the getter postconditions supply exactly the propositions needed for `config_pre`.

Source: `providers/evercrypt/fst/EverCrypt.AEAD.fst:101-122`

```fstar
  G.reveal kv

#push-options "--z3rlimit 10 --fuel 0 --ifuel 0 --z3cliopt smt.QI.EAGER_THRESHOLD=5"

let create_in_chacha20_poly1305: create_in_st CHACHA20_POLY1305 = fun r dst k ->
  let h0 = ST.get () in
  let ek = B.malloc r 0uy 32ul in
  let p = B.malloc r (Ek Hacl_CHACHA20 (G.hide (B.as_seq h0 k)) ek) 1ul in
  B.blit k 0ul ek 0ul 32ul;
  B.upd dst 0ul p;
  let h2 = ST.get() in
  B.modifies_only_not_unused_in B.(loc_buffer dst) h0 h2;
  Success

#pop-options

inline_for_extraction noextract
let create_in_aes_gcm (i: vale_impl):
  create_in_st (alg_of_vale_impl i) =
fun r dst k ->
  let a = alg_of_vale_impl i in
  let h0 = ST.get () in
```
Thus clients either call a runtime-checking API, which may return `UnsupportedAlgorithm`, or prove `config_pre a` before using no-check/stack-allocation forms.

### 2.4 Invariant and framing lemmas

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:96-124`

```fstar
inline_for_extraction noextract
val invariant_s: (#a:alg) -> HS.mem -> state_s a -> Type0

inline_for_extraction noextract
let invariant (#a:alg) (m: HS.mem) (s: state a) =
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s m (B.get m s 0)

val invariant_loc_in_footprint
  (#a: alg)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant m s))
  (ensures (B.loc_in (footprint m s) m))
  [SMTPat (invariant m s)]

val frame_invariant: #a:alg -> l:B.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant h0 s /\
    B.loc_disjoint l (footprint h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant h1 s /\
    footprint h0 s == footprint h1 s))
  [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]


```
`invariant_s` is abstract. Public `invariant` requires the state pointer live, its address disjoint from hidden internals, and the representation invariant for `B.get m s 0`. `invariant_loc_in_footprint` has an `SMTPat (invariant m s)`, so invariants automatically imply the footprint is in memory. `frame_invariant` has patterns on `invariant h1 s` and `B.modifies l h0 h1`; it automatically preserves invariants across modifications disjoint from the old footprint, and proves the footprint unchanged.

### 2.5 Algorithm and ghost key accessor

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:132-144`

```fstar

@param s State of the AEAD algorithm.

@return Algorithm used in the AEAD state."]
val alg_of_state (a: G.erased alg) (s: state (G.reveal a)): Stack alg
  (requires (fun h0 -> invariant #(G.reveal a) h0 s))
  (ensures (fun h0 a' h1 ->
    a' == G.reveal a /\
    h0 == h1))

/// The API is constructed in a way that one can always get the original key
/// value behind a state, any any memory.
val as_kv: (#a: alg) -> state_s a -> GTot (kv a)
```
`alg_of_state` reads the algorithm without changing memory. `as_kv` is the ghost accessor connecting a state value to the original key sequence; it is `GTot` and has no C counterpart.

## 3. Error and pure spec surface

Source: `providers/evercrypt/EverCrypt.Error.fsti:1-12`

```fstar
module EverCrypt.Error

/// The unified EverCrypt error type, to be used by all (new) implementations.
/// --------------------------------------------------------------------------

type error_code =
| Success
| UnsupportedAlgorithm
| InvalidKey
| AuthenticationFailure
| InvalidIVLength
| DecodeError
```
Source: `specs/Spec.Agile.AEAD.fsti:15-31`

```fstar
  // EverCrypt or miTLS; they are included e.g. for parsing
  | AES128_CCM  // "Counter with CBC-Message Authentication Code"
  | AES256_CCM
  | AES128_CCM8 // variant with truncated 8-byte tags
  | AES256_CCM8

let _: squash (inversion alg) = allow_inversion alg

let is_supported_alg (a: alg): bool =
  match a with
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305 -> true
  | _ -> false

let supported_alg = a:alg { is_supported_alg a }

```
Source: `specs/Spec.Agile.AEAD.fsti:57-84`

```fstar
  | AES128_CCM        -> 16
  | AES256_CCM        -> 16

/// No sharing with Spec.Agile.Cipher, since AES-GCM offers IV reduction via the
/// GHASH function.
let iv_length (a: supported_alg) (len: nat) =
  match a with
  | AES128_GCM -> len > 0 /\ 8 * len <= pow2 64 - 1
  | AES256_GCM -> len > 0 /\ 8 * len <= pow2 64 - 1
  | CHACHA20_POLY1305 -> len == 12

// Maximum length for both plaintexts and additional data.
//
// Some notes:
// - we have both closed (HACL-style specs) and semi-open (Vale specs)
//   intervals; just picking one arbitrary choice here... see
//   https://github.com/mitls/mitls-papers/wiki/Discussion-to-Converge-on-Design-Decisions
//   for a failure to make decisions
// - because the specs for HACL* are very concrete, they limit the size
//   artificially; we could've limited each of cipher and ad to 16 * 2**31 (see
//   chacha block size) but instead have a smaller bound because of the size of arrays.
let max_length: supported_alg -> nat =
  function
  | CHACHA20_POLY1305 -> pow2 32 - 1 - 16
  | AES128_GCM | AES256_GCM -> pow2 32 - 1

let cipher_max_length (a:supported_alg) = max_length a + tag_length a

```
Source: `specs/Spec.Agile.AEAD.fsti:95-124`

```fstar
let plain (a: supported_alg) = s:S.seq uint8 { S.length s <= max_length a }
let cipher (a: supported_alg) = s:S.seq uint8 { S.length s >= tag_length a /\ S.length s <= cipher_max_length a }

let cipher_length #a (p: plain a) =
  S.length p + tag_length a

// Convenient abbreviations
let encrypted #a (p: plain a) = c:cipher a { S.length c = cipher_length p }
let decrypted #a (c: cipher a) = p:plain a { S.length c = cipher_length p }

// Note: no GTot, specs need to be executable for testing

// Note: the spec starts with key expansion, but we don't reveal it here, and
// leave it up to EverCrypt.AEAD to rely on an abstract invariant to enforce
// that key expansion is performed first, so as not to do it on each encryption:
//
// let encrypt ... =
//   let ekv = expand ... in
//   <rest-of-encrypt>
//
// The implementation will friend this module, and expose expand as a stateful
// function, then will expose a function that does the <rest-of-encrypt> but
// still expresses its post-condition using Spec.Agile.AEAD.encrypt. So, encrypt takes
// a kv, not an ekv.

// Note: adopting the argument order of EverCrypt... which doesn't match other
// specs. Sigh.
val encrypt: #(a: supported_alg) -> kv a -> iv a -> ad a -> p:plain a -> encrypted p
val decrypt: #(a: supported_alg) -> kv a -> iv a -> ad a -> c:cipher a -> option (decrypted c)

```
Source: `specs/Spec.Cipher.Expansion.fsti:18-36`

```fstar
/// ``EverCrypt.AEAD`` -- we assume that an implementation covers both CTR and
/// AEAD. It lists valid combinations, and serves as an index for concrete
/// expanded keys, which include provider-specific representation choices. This
/// type serves several purposes.
type impl =
| Hacl_CHACHA20
| Vale_AES128
| Vale_AES256

let cipher_alg_of_impl (i: impl): cipher_alg =
  match i with
  | Hacl_CHACHA20 -> CHACHA20
  | Vale_AES128 -> AES128
  | Vale_AES256 -> AES256

/// Length of an expanded key per the AES specification.
val xkey_length (a: cipher_alg): Lib.IntTypes.size_nat

let xkey a = Lib.ByteSequence.lbytes (xkey_length a)
```
`Spec.Agile.AEAD.encrypt` returns the sequence `cipher || tag`; `decrypt` returns `option plaintext`; `correctness` proves decrypting an encryption under the same key/nonce/AAD returns `Some p`. Expansion details are deliberately outside the agile spec interface.

## 4. Every stateful `val` in `EverCrypt.AEAD`

### 4.1 Creation and stack allocation

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:147-174`

```fstar
let create_in_st (a: alg) =
  r:HS.rid ->
  dst:B.pointer (B.pointer_or_null (state_s a)) ->
  k:B.buffer uint8 { B.length k = key_length a } ->
  ST error_code
    (requires fun h0 ->
      ST.is_eternal_region r /\
      B.live h0 k /\ B.live h0 dst)
    (ensures fun h0 e h1 ->
      match e with
      | UnsupportedAlgorithm ->
          B.(modifies loc_none h0 h1)
      | Success ->
          let s = B.deref h1 dst in
          // Sanity
          is_supported_alg a /\
          not (B.g_is_null s) /\
          invariant h1 s /\

          // Memory stuff
          B.(modifies (loc_buffer dst) h0 h1) /\
          B.fresh_loc (footprint h1 s) h0 h1 /\
          B.(loc_includes (loc_region_only true r) (footprint h1 s)) /\
          freeable h1 s /\

          // Useful stuff
          as_kv (B.deref h1 s) == B.as_seq h0 k
      | _ -> False)
```
Source: `providers/evercrypt/EverCrypt.AEAD.fsti:181-205`

```fstar
let alloca_st (a: alg) =
  k:B.buffer uint8 { B.length k = key_length a } ->
  StackInline (B.pointer (state_s a))
    (requires fun h0 ->
      B.live h0 k /\ config_pre a /\ is_supported_alg a)
    (ensures fun h0 s h1 ->
      // Sanity
      invariant h1 s /\

      // Memory stuff
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint h1 s) h0 h1 /\
      B.live h1 s /\
      B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint h1 s)) /\

      // Useful stuff
      as_kv (B.deref h1 s) == B.as_seq h0 k)


/// This function takes a pointer to a caller-allocated reference ``dst`` then,
/// if the algorithm is supported (on this platform), allocates a fresh state
/// and modifies ``dst`` to point to it. The key-value associated with this can
/// be obtained via ``kv (B.deref dst)``; as long as ``dst`` is not modified,
/// then the caller can derive that the ``kv`` remains the same, which will be
/// required for encrypt.
```
Source: `providers/evercrypt/EverCrypt.AEAD.fsti:222-225`

```fstar
val create_in: #a:alg -> create_in_st a

inline_for_extraction noextract
val alloca: #a:alg -> alloca_st a
```
`create_in_st` allocates in an eternal region and writes `dst`. On `UnsupportedAlgorithm`, memory is unchanged. On `Success`, the state is supported, non-null, invariant, fresh, inside the region, freeable, and tied to the old key bytes by `as_kv`. `alloca_st` is the stack version: it requires `config_pre a` and support, allocates in the current tip, changes no pre-existing location, and establishes the same key fact.

### 4.2 Encryption preconditions

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:230-283`

```fstar
inline_for_extraction noextract
let iv_p a = iv:B.buffer uint8 { iv_length a (B.length iv)}

inline_for_extraction noextract
let ad_p a = ad:B.buffer uint8 { B.length ad <= max_length a }

inline_for_extraction noextract
let plain_p a = p:B.buffer uint8 { B.length p <= max_length a }

inline_for_extraction noextract
let cipher_p a = p:B.buffer uint8 { B.length p + tag_length a <= max_length a }

// SNIPPET_START: encrypt_pre
inline_for_extraction noextract
let encrypt_gen_pre (a: supported_alg)
  (iv:iv_p a)
  (iv_len: UInt32.t)
  (ad:ad_p a)
  (ad_len: UInt32.t)
  (plain: plain_p a)
  (plain_len: UInt32.t)
  (cipher: B.buffer uint8)
  (tag: B.buffer uint8)
  (h0: HS.mem)
=
  v iv_len = B.length iv /\ v iv_len > 0 /\
  v ad_len = B.length ad /\ v ad_len <= pow2 31 /\
  v plain_len = B.length plain /\ v plain_len <= max_length a /\
  B.length cipher = B.length plain /\
  B.length tag = tag_length a

inline_for_extraction noextract
let encrypt_live_disjoint_pre (a: supported_alg)
  (iv:iv_p a)
  (iv_len: UInt32.t)
  (ad:ad_p a)
  (ad_len: UInt32.t)
  (plain: plain_p a)
  (plain_len: UInt32.t)
  (cipher: B.buffer uint8)
  (tag: B.buffer uint8)
  (h0: HS.mem)
=
  MB.(all_live h0 [ buf iv; buf ad; buf plain; buf cipher; buf tag ]) /\
  (B.disjoint plain cipher \/ plain == cipher) /\
  B.disjoint cipher tag /\
  B.disjoint iv cipher /\ B.disjoint iv tag /\
  B.disjoint plain tag /\
  B.disjoint plain ad /\
  B.disjoint ad cipher /\ B.disjoint ad tag

inline_for_extraction noextract
let encrypt_pre (a: supported_alg)
  (s:B.pointer_or_null (state_s a))
```
These `inline_for_extraction noextract` helpers are proof abbreviations. `encrypt_gen_pre` is length arithmetic. `encrypt_live_disjoint_pre` is the aliasing policy: all buffers live; `(B.disjoint plain cipher \/ plain == cipher)` permits in-place encryption; tag/IV/AAD relations must be disjoint as listed. `encrypt_pre` adds state invariant and state-footprint disjointness when `s` is not null, allowing null-state calls to fail as `InvalidKey`.

### 4.3 `encrypt_st` and `encrypt`

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:307-340`

```fstar
let encrypt_st (a: supported_alg) =
  s:B.pointer_or_null (state_s a) ->
  iv:iv_p a ->
  iv_len: UInt32.t { v iv_len = B.length iv /\ v iv_len > 0 } ->
  ad:ad_p a ->
  ad_len: UInt32.t { v ad_len = B.length ad /\ v ad_len <= pow2 31 } ->
  plain: plain_p a ->
  plain_len: UInt32.t { v plain_len = B.length plain /\ v plain_len <= max_length a } ->
  cipher: B.buffer uint8 { B.length cipher = B.length plain } ->
  tag: B.buffer uint8 { B.length tag = tag_length a } ->
  Stack error_code
    (requires encrypt_pre a s iv iv_len ad ad_len plain plain_len cipher tag)
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          not (B.g_is_null s) /\
        B.(modifies (loc_union (footprint h1 s) (loc_union (loc_buffer cipher) (loc_buffer tag))) h0 h1) /\
        invariant h1 s /\
        footprint h0 s == footprint h1 s /\
        preserves_freeable s h0 h1 /\
        as_kv (B.deref h1 s) == as_kv (B.deref h0 s) /\
        S.equal (S.append (B.as_seq h1 cipher) (B.as_seq h1 tag))
          (Spec.encrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) (B.as_seq h0 plain))
      | InvalidKey ->
          B.g_is_null s /\
          B.(modifies loc_none h0 h1)
      | _ -> False)

/// This function takes a previously expanded key and performs encryption.
///
/// Possible return values are:
/// - ``Success``: encryption was successfully performed
/// - ``InvalidKey``: the function was passed a NULL expanded key (see above)
(** @type: true
```
Source: `providers/evercrypt/EverCrypt.AEAD.fsti:359-359`

```fstar
val encrypt: #a:G.erased (supported_alg) -> encrypt_st (G.reveal a)
```
On success, `modifies` includes state footprint, `cipher`, and `tag`; invariant, footprint, freeability, and `as_kv` are preserved. The exact spec link is the concatenation postcondition:

```fstar
S.equal (S.append (B.as_seq h1 cipher) (B.as_seq h1 tag))
  (Spec.encrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) (B.as_seq h0 plain))
```

On `InvalidKey`, `s` is null and memory is unchanged. Other results are impossible.

### 4.4 One-shot encryption

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:369-416`

```fstar
  (k:B.buffer uint8 { B.length k = key_length a })
  (iv:iv_p a)
  (iv_len: UInt32.t)
  (ad:ad_p a)
  (ad_len: UInt32.t)
  (plain: plain_p a)
  (plain_len: UInt32.t)
  (cipher: B.buffer uint8)
  (tag: B.buffer uint8)
  (h0: HS.mem)
=
  encrypt_gen_pre a iv iv_len ad ad_len plain plain_len cipher tag h0 /\ (
  B.live h0 k /\ B.disjoint k cipher /\
  encrypt_live_disjoint_pre a iv iv_len ad ad_len
                            plain plain_len cipher tag h0)

inline_for_extraction noextract
let encrypt_expand_st (does_runtime_check: bool) (a: supported_alg) =
  k:B.buffer uint8 { B.length k = key_length a } ->
  iv:iv_p a ->
  iv_len: UInt32.t { v iv_len = B.length iv /\ v iv_len > 0 } ->
  ad:ad_p a ->
  ad_len: UInt32.t { v ad_len = B.length ad /\ v ad_len <= pow2 31 } ->
  plain: plain_p a ->
  plain_len: UInt32.t { v plain_len = B.length plain /\ v plain_len <= max_length a } ->
  cipher: B.buffer uint8 { B.length cipher = B.length plain } ->
  tag: B.buffer uint8 { B.length tag = tag_length a } ->
  Stack error_code
    (requires fun h0 ->
      (if does_runtime_check then
        True
      else
        config_pre a) /\
      encrypt_expand_pre a k iv iv_len ad ad_len plain plain_len cipher tag h0)
    (ensures fun h0 r h1 ->
      match r with
      | Success ->
          B.(modifies ((loc_union (loc_buffer cipher) (loc_buffer tag))) h0 h1) /\
          S.equal (S.append (B.as_seq h1 cipher) (B.as_seq h1 tag))
            (Spec.encrypt #a (B.as_seq h0 k) (B.as_seq h0 iv) (B.as_seq h0 ad) (B.as_seq h0 plain))
      | UnsupportedAlgorithm ->
          if does_runtime_check then
            B.(modifies loc_none h0 h1)
          else
            False
      | _ ->
          False)

```
Source: `providers/evercrypt/EverCrypt.AEAD.fsti:430-447`

```fstar
val encrypt_expand_aes128_gcm_no_check: encrypt_expand_st false AES128_GCM

[@@ Comment "WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit."]
val encrypt_expand_aes256_gcm_no_check: encrypt_expand_st false AES256_GCM

/// Those functions take a key, expand it then perform encryption. They do not
/// require calling create_in before.
val encrypt_expand_aes128_gcm: encrypt_expand_st true AES128_GCM
val encrypt_expand_aes256_gcm: encrypt_expand_st true AES256_GCM
val encrypt_expand_chacha20_poly1305: encrypt_expand_st false CHACHA20_POLY1305

/// Run-time agility, run-time multiplexing, but not pre-expansion of the key.
val encrypt_expand: #a:supported_alg -> encrypt_expand_st true (G.reveal a)
```
`does_runtime_check` controls the hardware precondition. If true, the caller need not prove `config_pre`, but `UnsupportedAlgorithm` can occur with `modifies loc_none`. If false, `config_pre a` is required and `UnsupportedAlgorithm` is impossible. The AES `_no_check` variants use `false`; ChaCha20-Poly1305 also uses `false`, but its `config_pre` is `True`.

### 4.5 `decrypt_st` and `decrypt`

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:453-527`

```fstar
let decrypt_st (a: supported_alg) =
  s:B.pointer_or_null (state_s a) ->
  iv:iv_p a ->
  iv_len:UInt32.t { v iv_len = B.length iv /\ v iv_len > 0 } ->
  ad:ad_p a ->
  ad_len: UInt32.t { v ad_len = B.length ad /\ v ad_len <= pow2 31 } ->
  cipher: cipher_p a ->
  cipher_len: UInt32.t { v cipher_len = B.length cipher } ->
  tag: B.buffer uint8 { B.length tag = tag_length a } ->
  dst: B.buffer uint8 { B.length dst = B.length cipher } ->
  Stack error_code
    (requires fun h0 ->
      not (B.g_is_null s) ==>
        invariant h0 s /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer iv)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer ad)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer tag)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer dst)) /\
        B.(loc_disjoint (footprint h0 s) (loc_buffer cipher)) /\
        MB.(all_live h0 [ buf iv; buf ad; buf cipher; buf tag; buf dst ]) /\
        B.disjoint tag dst /\ B.disjoint tag cipher /\
        B.disjoint tag ad /\
        B.disjoint cipher ad /\ B.disjoint dst ad /\
        (B.disjoint cipher dst \/ cipher == dst))
    (ensures fun h0 err h1 ->
      let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
      match err with
      | InvalidKey ->
          B.g_is_null s /\
          B.(modifies loc_none h0 h1)
      | Success ->
          not (B.g_is_null s) /\ (
          let plain = Spec.decrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) cipher_tag in
          B.(modifies (loc_union (footprint h1 s) (loc_buffer dst)) h0 h1) /\
          invariant h1 s /\
          footprint h0 s == footprint h1 s /\
          preserves_freeable s h0 h1 /\
          as_kv (B.deref h1 s) == as_kv (B.deref h0 s) /\
          Some? plain /\ S.equal (Some?.v plain) (B.as_seq h1 dst))
      | AuthenticationFailure ->
          not (B.g_is_null s) /\ (
          let plain = decrypt #a (as_kv (B.deref h0 s)) (B.as_seq h0 iv) (B.as_seq h0 ad) cipher_tag in
          B.(modifies (loc_union (footprint h1 s) (loc_buffer dst)) h0 h1) /\
          invariant h1 s /\
          footprint h0 s == footprint h1 s /\
          preserves_freeable s h0 h1 /\
          as_kv (B.deref h1 s) == as_kv (B.deref h0 s) /\
          None? plain)
      | _ ->
          False)


/// This function takes a previously expanded key and performs decryption.
///
/// Possible return values are:
/// - ``Success``: decryption was successfully performed
/// - ``InvalidKey``: the function was passed a NULL expanded key (see above)
/// - ``Failure``: cipher text could not be decrypted (e.g. tag mismatch)
(** @type: true
*)
[@@ Comment "Verify the authenticity of `ad` || `cipher` and decrypt `cipher` into `dst`.

@param s Pointer to the The AEAD state created by `EverCrypt_AEAD_create_in`. It already contains the encryption key.
@param iv Pointer to `iv_len` bytes of memory where the nonce is read from.
@param iv_len Length of the nonce. Note: ChaCha20Poly1305 requires a 12 byte nonce.
@param ad Pointer to `ad_len` bytes of memory where the associated data is read from.
@param ad_len Length of the associated data.
@param cipher Pointer to `cipher_len` bytes of memory where the ciphertext is read from.
@param cipher_len Length of the ciphertext.
@param tag Pointer to `TAG_LEN` bytes of memory where the tag is read from.
  The length of the `tag` must be of a suitable length for the chosen algorithm:
  * `Spec_Agile_AEAD_AES128_GCM` (TAG_LEN=16)
  * `Spec_Agile_AEAD_AES256_GCM` (TAG_LEN=16)
  * `Spec_Agile_AEAD_CHACHA20_POLY1305` (TAG_LEN=16)
@param dst Pointer to `cipher_len` bytes of memory where the decrypted plaintext will be written to.
```
Source: `providers/evercrypt/EverCrypt.AEAD.fsti:542-542`

```fstar
val decrypt: #a:G.erased supported_alg -> decrypt_st (G.reveal a)
```
Decryption similarly permits in-place `(B.disjoint cipher dst \/ cipher == dst)`. It forms `cipher_tag = old cipher ++ old tag`. On `Success`, `Spec.decrypt` is `Some` and `dst` equals the contained plaintext; invariant, footprint, freeability, and `as_kv` are preserved. On `AuthenticationFailure`, the spec call is `None`, but `dst` may have been modified; no output-preservation fact is provided. On `InvalidKey`, memory is unchanged.

### 4.6 One-shot decryption and free

Source: `providers/evercrypt/EverCrypt.AEAD.fsti:548-584`

```fstar
let decrypt_expand_st (does_runtime_check: bool) (a: supported_alg) =
  k:B.buffer uint8 { B.length k = key_length a } ->
  iv:iv_p a ->
  iv_len:UInt32.t { v iv_len = B.length iv /\ v iv_len > 0 } ->
  ad:ad_p a ->
  ad_len: UInt32.t { v ad_len = B.length ad /\ v ad_len <= pow2 31 } ->
  cipher: cipher_p a ->
  cipher_len: UInt32.t { v cipher_len = B.length cipher } ->
  tag: B.buffer uint8 { B.length tag = tag_length a } ->
  dst: B.buffer uint8 { B.length dst = B.length cipher } ->
  Stack error_code
    (requires fun h0 ->
        (if does_runtime_check then
          True
        else
          config_pre a) /\
        MB.(all_live h0 [ buf k; buf iv; buf ad; buf cipher; buf tag; buf dst ]) /\
        B.disjoint k dst /\
        B.disjoint tag dst /\ B.disjoint tag cipher /\
        B.disjoint tag ad /\
        B.disjoint cipher ad /\ B.disjoint dst ad /\
        (B.disjoint cipher dst \/ cipher == dst))
    (ensures fun h0 err h1 ->
      let cipher_tag = B.as_seq h0 cipher `S.append` B.as_seq h0 tag in
      let plain = Spec.decrypt #a (B.as_seq h0 k) (B.as_seq h0 iv) (B.as_seq h0 ad) cipher_tag in
      B.(modifies (loc_buffer dst) h0 h1) /\
      begin
      match err with
      | Success ->
        Some? plain /\ S.equal (Some?.v plain) (B.as_seq h1 dst)
      | AuthenticationFailure ->
        None? plain
      | UnsupportedAlgorithm ->
          if does_runtime_check then
            B.(modifies loc_none h0 h1)
          else
            False
```
Source: `providers/evercrypt/EverCrypt.AEAD.fsti:596-616`

```fstar
val decrypt_expand_aes128_gcm_no_check: decrypt_expand_st false AES128_GCM

[@@ Comment "WARNING: this function doesn't perform any dynamic
  hardware check. You MUST make sure your hardware supports the
  implementation of AESGCM. Besides, this function was not designed
  for cross-compilation: if you compile it on a system which doesn't
  support Vale, it will compile it to a function which makes the
  program exit."]
val decrypt_expand_aes256_gcm_no_check: decrypt_expand_st false AES256_GCM

/// This function takes a key, expands it and performs decryption.
///
/// Possible return values are:
/// - ``Success``: decryption was successfully performed
/// - ``Failure``: cipher text could not be decrypted (e.g. tag mismatch)
(** @type: true
*)
val decrypt_expand_aes128_gcm: decrypt_expand_st true AES128_GCM
val decrypt_expand_aes256_gcm: decrypt_expand_st true AES256_GCM
val decrypt_expand_chacha20_poly1305: decrypt_expand_st false CHACHA20_POLY1305
val decrypt_expand: #a:supported_alg -> decrypt_expand_st true (G.reveal a)
```
Source: `providers/evercrypt/EverCrypt.AEAD.fsti:623-630`

```fstar
val free:
  #a:G.erased supported_alg -> (
  let a = Ghost.reveal a in
  s:state a -> ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant h0 s)
  (ensures fun h0 _ h1 ->
```
The one-shot decryption shape mirrors encryption: checked APIs may return `UnsupportedAlgorithm`; no-check APIs require `config_pre`. `free` consumes `freeable h0 s` and `invariant h0 s`, and may modify the state footprint.

## 5. Stateful round-trip proof

The pure lemma is:

Source: `specs/Spec.Agile.AEAD.fsti:121-124`

```fstar
// specs. Sigh.
val encrypt: #(a: supported_alg) -> kv a -> iv a -> ad a -> p:plain a -> encrypted p
val decrypt: #(a: supported_alg) -> kv a -> iv a -> ad a -> c:cipher a -> option (decrypted c)

```
A successful `create_in` gives `as_kv state == B.as_seq h0 k`. A successful `encrypt` gives `cipher || tag == Spec.encrypt key nonce aad p` and preserves `as_kv` and `invariant`. Passing those buffers to `decrypt`, its success postcondition gives `Some? (Spec.decrypt key nonce aad (cipher || tag))` and `dst` equal to that plaintext. Rewriting with the encrypt postcondition and applying `Spec.Agile.AEAD.correctness` yields `B.as_seq h_after dst == p`. If decrypt returns `AuthenticationFailure`, the contract gives only `None? (Spec.decrypt ...)`; it does not say `dst` is unchanged or meaningful.

## 6. Non-agile HACL*/EverCrypt F* interfaces

### 6.1 EverCrypt and HACL* ChaCha20

Source: `providers/evercrypt/EverCrypt.Cipher.fsti:1-20`

```fstar
module EverCrypt.Cipher

open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module Spec = Spec.Chacha20

val chacha20:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
```
Source: `code/chacha20/Hacl.Chacha20.fst:9-20`

```fstar
val chacha20_encrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Chacha20.chacha20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))
```
Source: `code/chacha20/Hacl.Chacha20.fst:26-37`

```fstar
val chacha20_decrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h ->
    live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Chacha20.chacha20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))
```
Source: `code/chacha20/Hacl.Impl.Chacha20.Vec.fst:214-235`

```fstar
  let ctx = create_state w in
  chacha20_init #w ctx key n ctr;
  chacha20_update #w ctx len out text;
  pop_frame()

inline_for_extraction noextract
let chacha20_encrypt_st (w:lanes) =
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t{v ctr + w <= max_size_t } ->
  Stack unit
    (requires fun h ->
      live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.Chacha20.chacha20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))

noextract
val chacha20_encrypt: #w:lanes -> chacha20_encrypt_st w
```
Source: `code/chacha20/Hacl.Impl.Chacha20.Vec.fst:259-280`

```fstar
  let ctx = create_state w in
  chacha20_init ctx key n ctr;
  chacha20_update ctx len out cipher;
  pop_frame()

inline_for_extraction noextract
let chacha20_decrypt_st (w:lanes) =
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 12ul
  -> ctr:size_t{v ctr + w <= max_size_t } ->
  Stack unit
    (requires fun h ->
      live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
    (ensures  fun h0 _ h1 ->
      modifies (loc out) h0 h1 /\
      as_seq h1 out == Spec.Chacha20.chacha20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))

noextract
val chacha20_decrypt: #w:lanes -> chacha20_decrypt_st w
```
ChaCha20 contracts require exact 32-byte keys and 12-byte nonces. `eq_or_disjoint` permits in-place operation. Vector-indexed contracts add `ctr:size_t{v ctr + w <= max_size_t}`, a proof obligation not visible from an ordinary C prototype.

### 6.2 ChaCha20-Poly1305

Source: `providers/evercrypt/EverCrypt.Chacha20Poly1305.fsti:15-62`

```fstar
val aead_encrypt:
  k:lbuffer uint8 32ul -> // key
  n:lbuffer uint8 12ul -> // nonce
  aadlen:size_t ->
  aad:lbuffer uint8 aadlen ->
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen -> // input: plaintext
  cipher:lbuffer uint8 mlen -> // output: buffer for cipher + mac
  tag:lbuffer uint8 16ul -> // output: buffer for cipher + mac
  Stack unit
    (requires (fun h ->
      disjoint k cipher /\ disjoint n cipher /\
      disjoint k tag /\ disjoint n tag /\
      disjoint cipher tag /\
      eq_or_disjoint m cipher /\
      disjoint aad cipher /\
      live h k /\ live h n /\ live h aad /\ live h m /\ live h cipher /\ live h tag))
    (ensures  (fun h0 _ h1 -> modifies (loc cipher |+| loc tag) h0 h1 /\
      Seq.equal
        (Seq.concat (as_seq h1 cipher) (as_seq h1 tag))
        (Spec.aead_encrypt (as_seq h0 k) (as_seq h0 n) (as_seq h0 m) (as_seq h0 aad))))

(** @type: true
*)
val aead_decrypt:
  k:lbuffer uint8 32ul -> // key
  n:lbuffer uint8 12ul -> // nonce
  aadlen:size_t -> 
  aad:lbuffer uint8 aadlen ->
  (mlen:size_t{v mlen + 16 <= max_size_t /\ v aadlen + v mlen / 64 <= max_size_t}) ->
  m:lbuffer uint8 mlen -> // output: buffer for decrypted plaintext
  c:lbuffer uint8 mlen -> // input: cipher
  mac:lbuffer uint8 16ul -> // input: mac
  Stack UInt32.t
    (requires (fun h ->
      eq_or_disjoint m c /\
      live h k /\ live h n /\ live h aad /\ live h m /\ live h c /\ live h mac))
    (ensures  (fun h0 z h1 -> modifies (loc m) h0 h1 /\
      (let plain = Spec.aead_decrypt (as_seq h0 k) (as_seq h0 n) (as_seq h0 c) (as_seq h0 mac) (as_seq h0 aad) in
      match z with
      | 0ul -> Some? plain /\ as_seq h1 m == Some?.v plain // decryption succeeded
      | 1ul -> None? plain
      | _ -> false)  // decryption failed
      )
    )
```
Source: `code/chacha20poly1305/Hacl.Impl.Chacha20Poly1305.fst:145-205`

```fstar
let aead_encrypt_st (w:field_spec) =
    output:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> input:buffer uint8
  -> input_len:size_t { length input = v input_len /\ length output = v input_len }
  -> data:buffer uint8
  -> data_len:size_t { length data = v data_len }
  -> key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 12ul ->
  Stack unit
  (requires fun h ->
    live h key /\ live h nonce /\ live h data /\
    live h input /\ live h output /\ live h tag /\
    disjoint key output /\ disjoint nonce output /\
    disjoint key tag /\ disjoint nonce tag /\
    disjoint output tag /\
    eq_or_disjoint (input <: lbuffer uint8 input_len) (output <: lbuffer uint8 input_len) /\
    disjoint data output)
  (ensures  fun h0 _ h1 -> modifies2 output tag h0 h1 /\
    Seq.append (as_seq h1 (output <: lbuffer uint8 input_len)) (as_seq h1 tag) ==
    Spec.aead_encrypt (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 (input <: lbuffer uint8 input_len)) (as_seq h0 (data <: lbuffer uint8 data_len)))

noextract
val aead_encrypt: #w:field_spec -> aead_encrypt_st w

[@ Meta.Attribute.specialize ]
let aead_encrypt #w output tag input input_len data data_len key nonce =
  chacha20_encrypt #w input_len output input key nonce 1ul;
  derive_key_poly1305_do #w key nonce data_len data input_len output tag



inline_for_extraction noextract
let aead_decrypt_st (w:field_spec) =
    output:buffer uint8
  -> input:buffer uint8
  -> input_len:size_t { length input = v input_len /\ length output = v input_len }
  -> data:buffer uint8
  -> data_len:size_t { length data = v data_len }
  -> key:lbuffer uint8 32ul
  -> nonce:lbuffer uint8 12ul
  -> tag:lbuffer uint8 16ul ->
  Stack UInt32.t
  (requires fun h ->
    live h key /\ live h nonce /\ live h (data <: lbuffer uint8 data_len) /\
    live h input /\ live h output /\ live h tag /\
    eq_or_disjoint (input <: lbuffer uint8 input_len) (output <: lbuffer uint8 input_len))
  (ensures  fun h0 z h1 -> modifies1 output h0 h1 /\
   (let plain = Spec.aead_decrypt (as_seq h0 key) (as_seq h0 nonce) (as_seq h0 (input <: lbuffer uint8 input_len)) (as_seq h0 tag) (as_seq h0 (data <: lbuffer uint8 data_len)) in
    match z with
    | 0ul -> Some? plain /\ as_seq h1 (output <: lbuffer uint8 input_len) == Some?.v plain // decryption succeeded
    | 1ul -> None? plain
    | _ -> false)  // decryption failed
  )


noextract
val aead_decrypt: #w:field_spec -> aead_decrypt_st w

[@ Meta.Attribute.specialize ]
let aead_decrypt #w output input input_len data data_len key nonce tag =
```
Source: `code/chacha20poly1305/Hacl.Chacha20Poly1305_32.fst:28-29`

```fstar
@param data_len Length of the associated data.
@param key Pointer to 32 bytes of memory where the AEAD key is read from.
```
Source: `code/chacha20poly1305/Hacl.Chacha20Poly1305_32.fst:46-47`

```fstar

```
Source: `code/chacha20poly1305/Hacl.Chacha20Poly1305_128.fst:28-29`

```fstar
@param data_len Length of the associated data.
@param key Pointer to 32 bytes of memory where the AEAD key is read from.
```
Source: `code/chacha20poly1305/Hacl.Chacha20Poly1305_128.fst:46-47`

```fstar

```
Source: `code/chacha20poly1305/Hacl.Chacha20Poly1305_256.fst:27-28`

```fstar
@param data Pointer to `data_len` bytes of memory where the associated data is read from.
@param data_len Length of the associated data.
```
Source: `code/chacha20poly1305/Hacl.Chacha20Poly1305_256.fst:45-46`

```fstar

```
These APIs are non-agile and have no reusable abstract state. Postconditions directly relate output buffers to `Spec.aead_encrypt`/`Spec.aead_decrypt`. Width modules specialize the shared `aead_encrypt_st`/`aead_decrypt_st` shapes by Poly1305 field implementation.

### 6.3 Salsa20 and HSalsa20

Source: `code/salsa20/Hacl.Salsa20.fst:10-21`

```fstar

val salsa20_encrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> text:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h text /\ live h out /\ eq_or_disjoint text out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_encrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 text))
```
Source: `code/salsa20/Hacl.Salsa20.fst:27-38`

```fstar
val salsa20_decrypt:
    len:size_t
  -> out:lbuffer uint8 len
  -> cipher:lbuffer uint8 len
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul
  -> ctr:size_t ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h cipher /\ live h out /\ eq_or_disjoint cipher out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.salsa20_decrypt_bytes (as_seq h0 key) (as_seq h0 n) (v ctr) (as_seq h0 cipher))

```
Source: `code/salsa20/Hacl.Salsa20.fst:43-51`

```fstar
val salsa20_key_block0:
    out:lbuffer uint8 64ul
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 8ul ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.Salsa20.salsa20_key_block0 (as_seq h0 key) (as_seq h0 n))

```
Source: `code/salsa20/Hacl.Salsa20.fst:56-64`

```fstar
val hsalsa20:
    out:lbuffer uint8 32ul
  -> key:lbuffer uint8 32ul
  -> n:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h -> live h key /\ live h n /\ live h out)
  (ensures  fun h0 _ h1 -> modifies (loc out) h0 h1 /\
    as_seq h1 out == Spec.hsalsa20 (as_seq h0 key) (as_seq h0 n))

```
Salsa20 uses exact 32-byte keys, 8-byte nonces for stream encryption, and a 16-byte nonce for `hsalsa20`. Stream encryption/decryption permit exact aliasing or disjoint buffers.

### 6.4 NaCl box/secretbox

Source: `code/nacl-box/Hacl.NaCl.fst:27-39`

```fstar
val crypto_secretbox_detached:
    c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies2 c tag h0 h1 /\
```
Source: `code/nacl-box/Hacl.NaCl.fst:57-72`

```fstar
val crypto_secretbox_open_detached:
    m:buffer uint8
  -> c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SS.secretbox_open_detached (as_seq h0 k) (as_seq h0 n) (as_seq h0 tag) (as_seq #MUT #uint8 #mlen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #mlen h1 m == Some?.v msg
```
Source: `code/nacl-box/Hacl.NaCl.fst:86-99`

```fstar
val crypto_secretbox_easy:
    c:buffer uint8
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen + 16 /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 c h0 h1 /\
    as_seq #MUT #uint8 #(mlen +! 16ul) h1 c ==
      SS.secretbox_easy (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m))

```
Source: `code/nacl-box/Hacl.NaCl.fst:114-129`

```fstar
val crypto_secretbox_open_easy:
    m:buffer uint8
  -> c:buffer uint8
  -> clen:size_t{length c = v clen /\ v clen = length m + 16}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SS.secretbox_open_easy (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #clen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #(clen -! 16ul) h1 m == Some?.v msg
    | _ -> None? msg))

```
Source: `code/nacl-box/Hacl.NaCl.fst:139-151`

```fstar
val crypto_box_beforenm:
    k:lbuffer uint8 32ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h -> live h k /\ live h pk /\ live h sk /\
    disjoint k pk /\ disjoint k sk)
  (ensures  fun h0 r h1 -> modifies1 k h0 h1 /\
   (let key = SB.box_beforenm (as_seq h0 pk) (as_seq h0 sk) in
    match r with
    | 0ul -> Some? key /\ as_seq h1 k == Some?.v key
    | _ -> None? key))

```
Source: `code/nacl-box/Hacl.NaCl.fst:157-171`

```fstar
val crypto_box_detached_afternm:
    c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies2 c tag h0 h1 /\
    (as_seq h1 tag, as_seq #MUT #uint8 #mlen h1 c) == SB.box_detached_afternm (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m))

```
Source: `code/nacl-box/Hacl.NaCl.fst:185-202`

```fstar
val crypto_box_detached:
    c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies2 c tag h0 h1 /\
   (let tag_cipher = SB.box_detached (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m) in
    match r with
    | 0ul -> Some? tag_cipher /\ (let (tag_s, cipher_s) = Some?.v tag_cipher in (as_seq h1 tag, as_seq #MUT #uint8 #mlen h1 c) == (tag_s, cipher_s))
    | _ -> None? tag_cipher))
```
Source: `code/nacl-box/Hacl.NaCl.fst:209-224`

```fstar
val crypto_box_open_detached_afternm:
    m:buffer uint8
  -> c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SB.box_open_detached_afternm (as_seq h0 k) (as_seq h0 n) (as_seq h0 tag) (as_seq #MUT #uint8 #mlen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #mlen h1 m == Some?.v msg
```
Source: `code/nacl-box/Hacl.NaCl.fst:240-256`

```fstar
val crypto_box_open_detached:
    m:buffer uint8
  -> c:buffer uint8
  -> tag:lbuffer uint8 16ul
  -> mlen:size_t{length c = v mlen /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\ live h tag /\
    disjoint tag c /\ eq_or_disjoint (m <: lbuffer uint8 mlen) (c <: lbuffer uint8 mlen) /\
    disjoint tag m /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SB.box_open_detached (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq h0 tag) (as_seq #MUT #uint8 #mlen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #mlen h1 m == Some?.v msg
```
Source: `code/nacl-box/Hacl.NaCl.fst:264-276`

```fstar
val crypto_box_easy_afternm:
    c:buffer uint8
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen + 16 /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 c h0 h1 /\
    as_seq #MUT #uint8 #(mlen +! 16ul) h1 c ==
      SB.box_easy_afternm (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m))
```
Source: `code/nacl-box/Hacl.NaCl.fst:290-306`

```fstar
val crypto_box_easy:
    c:buffer uint8
  -> m:buffer uint8
  -> mlen:size_t{length c = v mlen + 16 /\ length m = v mlen}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h sk /\ live h pk /\ live h n /\
    disjoint m c /\ disjoint n m /\ disjoint n c)
  (ensures  fun h0 r h1 -> modifies1 c h0 h1 /\
    (let cipher = SB.box_easy (as_seq h0 sk) (as_seq h0 pk) (as_seq h0 n) (as_seq #MUT #uint8 #mlen h0 m) in
    match r with
    | 0ul -> Some? cipher /\ as_seq #MUT #uint8 #(mlen +! 16ul) h1 c == Some?.v cipher
    | _ -> None? cipher))

```
Source: `code/nacl-box/Hacl.NaCl.fst:312-327`

```fstar
val crypto_box_open_easy_afternm:
    m:buffer uint8
  -> c:buffer uint8
  -> clen:size_t{length c = v clen /\ v clen = length m + 16}
  -> n:lbuffer uint8 24ul
  -> k:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h k /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SB.box_open_easy_afternm (as_seq h0 k) (as_seq h0 n) (as_seq #MUT #uint8 #clen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #(clen -! 16ul) h1 m == Some?.v msg
    | _ -> None? msg))

```
Source: `code/nacl-box/Hacl.NaCl.fst:340-356`

```fstar
val crypto_box_open_easy:
    m:buffer uint8
  -> c:buffer uint8
  -> clen:size_t{length c = v clen /\ v clen = length m + 16}
  -> n:lbuffer uint8 24ul
  -> pk:lbuffer uint8 32ul
  -> sk:lbuffer uint8 32ul ->
  Stack size_t
  (requires fun h ->
    live h c /\ live h m /\ live h pk /\ live h sk /\ live h n /\
    disjoint m c /\ disjoint m n /\ disjoint c n)
  (ensures fun h0 r h1 -> modifies1 m h0 h1 /\
   (let msg = SB.box_open_easy (as_seq h0 pk) (as_seq h0 sk) (as_seq h0 n) (as_seq #MUT #uint8 #clen h0 c) in
    match r with
    | 0ul -> Some? msg /\ as_seq #MUT #uint8 #(clen -! 16ul) h1 m == Some?.v msg
    | _ -> None? msg))

```
NaCl detached APIs permit in-place message/ciphertext via `eq_or_disjoint`; easy APIs with combined tag+cipher buffers require input/output disjointness. Length refinements (`length c = v mlen + 16`, `v clen = length m + 16`) are verified preconditions. Success branches prove output buffers equal `SS.secretbox_*` or `SB.box_*`; failure branches prove the pure spec returned `None`, not that outputs were preserved.

## 7. Notes for reimplementers

Essential contracts: keep `state_s` abstract; preserve the creation/use/free protocol; cover all mutable representation memory in `footprint`; maintain precise `modifies`; preserve `as_kv` across encrypt/decrypt; keep the in-place policy `(plain == cipher)` and `(cipher == dst)` only where specified; and connect outputs exactly to pure specs.

F*-specific plumbing may be reorganized but needs equivalents: `inline_for_extraction noextract` abbreviations, erased indices, abstract ghost accessors, footprint lemmas, and `SMTPat` triggers. Changing these can break verified clients even if extracted C is unchanged.
