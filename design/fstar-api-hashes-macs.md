# F\* APIs for hashes, streaming, HMAC, HKDF, and Poly1305

This chapter documents the **F\*** interface surface for verified Low\*/F\*
clients and reimplementers: `val` declarations, refinements, `requires` /
`ensures`, effects, ghost accessors, and framing lemmas. It is not the C API;
see [api-hashes.md](api-hashes.md) and [api-macs-kdf.md](api-macs-kdf.md). Read
with [README.md](README.md), [fstar-api.md](fstar-api.md),
[fstar-specs.md](fstar-specs.md), [implementation.md](implementation.md), and
[surprises.md](surprises.md).

## 1. Orientation

Hashing has four F\* layers.

| Layer | Modules | Verified-client use |
|---|---|---|
| Vocabulary | `Hacl.Hash.Definitions` | Shared state, word, length and `*_st` type abbreviations. |
| Fixed implementations | `Hacl.Hash.SHA2`, `MD5`, `SHA1`, `SHA3`, `Blake2*` | Concrete symbols typed by the abbreviations. |
| Streaming functor | `Hacl.Streaming.Interface`, `Hacl.Streaming.Functor` | Incremental API and proof vocabulary (`seen`, footprints, framing). |
| Agile frontends | `EverCrypt.Hash(.Incremental)`, `Hacl.Agile.Hash`, streaming HMAC | Runtime algorithm/implementation selection and CPU dispatch. |

Verified clients should usually depend on `EverCrypt.Hash.Incremental` for
streaming hashes, `EverCrypt.HMAC`/`EverCrypt.HKDF`/`EverCrypt.Poly1305` for
agile one-shot APIs, and `Hacl.Streaming.Functor` only when they need the ghost
state and framing lemmas directly.

## 2. `Hacl.Hash.Definitions`

Source: `code/hash/Hacl.Hash.Definitions.fst:20-344`. This module is an `.fst`
in this tree, but it is the shared interface vocabulary imported by the `.fsti`
files. Verbatim definitions:

```fstar
let m_spec (a:hash_alg) : Type0 =
  match a with
  | Blake2S | Blake2B -> Blake2.m_spec
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> unit

inline_for_extraction noextract
let extra_state (a:hash_alg) : Type0 =
  match a with
  | Blake2S -> s:uint_t U64 PUB{ v s % block_length a = 0 }
  | Blake2B -> s:uint_t U128 PUB{ v s % block_length a = 0 }
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> unit

inline_for_extraction noextract
let ev_v (#a:hash_alg) (ev:extra_state a) : Spec.Hash.Definitions.extra_state a =
  match a with
  | Blake2S -> v #U64 #PUB ev
  | Blake2B -> v #U128 #PUB ev
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> ()

inline_for_extraction
type impl = a:hash_alg & m_spec a

inline_for_extraction noextract
let mk_impl (a:hash_alg) (m:m_spec a) : impl = (|a, m|)

inline_for_extraction noextract
let get_alg (i:impl) : hash_alg =
  match i with (|a, m|) -> a

inline_for_extraction noextract
let get_spec (i:impl) : m_spec (get_alg i) =
  match i with (|a, m|) -> m

inline_for_extraction noextract
let impl_word (i:impl) =
  [@inline_let] let a = get_alg i in
  match a with
  | Blake2S | Blake2B -> Blake2.element_t (to_blake_alg a) (get_spec i)
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> word a

inline_for_extraction noextract
let impl_state_length (i:impl) =
  [@inline_let] let a = get_alg i in
  match a with
  | Blake2S | Blake2B -> UInt32.v (4ul *. Blake2.row_len (to_blake_alg a) (get_spec i))
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> state_word_length a

inline_for_extraction noextract
let impl_state_len (i:impl) : s:size_t{size_v s == impl_state_length i} =
  [@inline_let] let a = get_alg i in
  [@inline_let] let m = get_spec i in
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> 8ul
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> 25ul
  | _ ->
    (**) mul_mod_lemma 4ul (Blake2.row_len (to_blake_alg a) (get_spec i));
    match a, m with
    | Blake2S, Blake2.M32
    | Blake2B, Blake2.M32 | Blake2B, Blake2.M128 -> 16ul
    | Blake2S, Blake2.M128 | Blake2S, Blake2.M256
    | Blake2B, Blake2.M256 -> 4ul

inline_for_extraction noextract
type state (i:impl) =
  b:B.buffer (impl_word i) { B.length b = impl_state_length i }

inline_for_extraction noextract
let as_seq (#i:impl) (h:HS.mem) (s:state i) : GTot (words_state (get_alg i)) =
  match get_alg i with
  | Blake2S -> Blake2.state_v #Spec.Blake2.Blake2S #(get_spec i) h s
  | Blake2B -> Blake2.state_v #Spec.Blake2.Blake2B #(get_spec i) h s
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> B.as_seq h s

inline_for_extraction
let word_len (a: md_alg) : n:size_t { v n = word_length a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 4ul
  | SHA2_384 | SHA2_512 -> 8ul

inline_for_extraction
let block_len (a: hash_alg): n:size_t { v n = block_length a } =
  match a with
  | MD5 | SHA1 | SHA2_224 | SHA2_256 -> 64ul
  | SHA2_384 | SHA2_512 -> 128ul
  | SHA3_224 -> assert_norm (rate SHA3_224/8/8*8 = 144); 144ul
  | SHA3_256 -> assert_norm (rate SHA3_256/8/8*8 = 136); 136ul
  | SHA3_384 -> assert_norm (rate SHA3_384/8/8*8 = 104); 104ul
  | SHA3_512 -> assert_norm (rate SHA3_512/8/8*8 = 72); 72ul
  | Shake128 -> assert_norm (rate Shake128/8/8*8 = 168); 168ul
  | Shake256 -> assert_norm (rate Shake256/8/8*8 = 136); 136ul
  | Blake2S -> 64ul
  | Blake2B -> 128ul

inline_for_extraction
let hash_word_len (a: md_alg): n:size_t { v n = hash_word_length a } =
  match a with
  | MD5 -> 4ul
  | SHA1 -> 5ul
  | SHA2_224 -> 7ul
  | SHA2_256 -> 8ul
  | SHA2_384 -> 6ul
  | SHA2_512 -> 8ul

inline_for_extraction
let hash_len (a: fixed_len_alg): n:size_t { v n = hash_length a } =
  match a with
  | MD5 -> 16ul
  | SHA1 -> 20ul
  | SHA2_224 -> 28ul
  | SHA2_256 -> 32ul
  | SHA2_384 -> 48ul
  | SHA2_512 -> 64ul
  | Blake2S -> 32ul
  | Blake2B -> 64ul
  | SHA3_224 -> 28ul
  | SHA3_256 -> 32ul
  | SHA3_384 -> 48ul
  | SHA3_512 -> 64ul

/// Maximum input length, but fitting on a 64-bit integer (since the streaming
/// module doesn't bother taking into account lengths that are greater than
/// that). The comment previously was:
///
/// Note that we keep the total length at run-time, on 64 bits, but require that
/// it abides by the size requirements for the smaller hashes -- we're not
/// interested at this stage in having an agile type for lengths that would be
/// up to 2^125 for SHA384/512.

module U64 = FStar.UInt64

inline_for_extraction noextract
let max_input_len64 a: U64.(x:t { 0 < v x /\ v x `less_than_max_input_length` a }) =
  let _ = allow_inversion hash_alg in
  match a with
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 ->
      assert_norm (0 < pow2 61 - 1 && pow2 61 < pow2 64);
      normalize_term_spec (pow2 61 - 1);
      U64.uint_to_t (normalize_term (pow2 61 - 1))
  | SHA2_384 | SHA2_512 ->
      assert_norm (pow2 64 < pow2 125 - 1);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | Blake2S ->
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | Blake2B ->
      assert_norm (pow2 64 < pow2 128);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 ->
      // TODO: relax this?
      assert_norm (pow2 64 < pow2 128);
      normalize_term_spec (pow2 64 - 1);
      U64.uint_to_t (normalize_term (pow2 64 - 1))

noextract inline_for_extraction
let blocks_t (a: hash_alg) =
  b:B.buffer uint8 { B.length b % block_length a = 0 }

let hash_t (a: fixed_len_alg) = b:B.buffer uint8 { B.length b = hash_length a }

(** The types of all stateful operations for a hash algorithm. *)

noextract inline_for_extraction
let alloca_st (i:impl) = unit -> ST.StackInline (state i)
  (requires (fun h ->
    HS.is_stack_region (HS.get_tip h)))
  (ensures (fun h0 s h1 ->
    M.(modifies M.loc_none h0 h1) /\
    B.frameOf s == HS.get_tip h0 /\
    as_seq h1 s == Spec.Agile.Hash.init (get_alg i) /\
    B.live h1 s /\
    B.fresh_loc (M.loc_buffer s) h0 h1))

noextract inline_for_extraction
let malloc_st (i:impl) = r:HS.rid -> ST.ST (B.buffer (impl_word i))
  (requires (fun h ->
    ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    if B.g_is_null s then
      M.(modifies M.loc_none h0 h1)
    else
      B.length s == impl_state_length i /\
      B.live h1 s /\
      M.(modifies M.loc_none h0 h1) /\
      B.fresh_loc (M.loc_addr_of_buffer s) h0 h1 /\
      M.(loc_includes (loc_region_only true r) (loc_addr_of_buffer s)) /\
      B.freeable s))

noextract inline_for_extraction
let init_st (i:impl) = s:state i -> ST.Stack unit
  (requires (fun h ->
    B.live h s))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer s) h0 h1) /\
    as_seq h1 s == Spec.Agile.Hash.init (get_alg i)))

noextract inline_for_extraction
let update_st (i:impl{is_md (get_alg i)}) =
  s:state i ->
  block:B.buffer uint8 { B.length block = block_length (get_alg i) } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h block /\ B.disjoint s block))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer s) h0 h1) /\
      as_seq h1 s ==
        Spec.Agile.Hash.update (get_alg i) (as_seq h0 s) (B.as_seq h0 block)))

noextract inline_for_extraction
let pad_st (a: md_alg) = len:len_t a -> dst:B.buffer uint8 ->
  ST.Stack unit
    (requires (fun h ->
      len_v a len `less_than_max_input_length` a /\
      B.live h dst /\
      B.length dst = pad_length a (len_v a len)))
    (ensures (fun h0 _ h1 ->
      M.(modifies (loc_buffer dst) h0 h1) /\
      Seq.equal (B.as_seq h1 dst) (Spec.Hash.MD.pad a (len_v a len))))

// Note: we cannot take more than 4GB of data because we are currently
// constrained by the size of buffers...
noextract inline_for_extraction
let update_multi_st (i:impl) =
  s:state i ->
  ev:extra_state (get_alg i) ->
  blocks:blocks_t (get_alg i) ->
  n:size_t { B.length blocks = block_length (get_alg i) * v n } ->
  ST.Stack unit
    (requires (fun h ->
      Spec.Agile.Hash.update_multi_pre (get_alg i) (ev_v ev) (B.as_seq h blocks) /\
      B.live h s /\ B.live h blocks /\ B.disjoint s blocks))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      as_seq h1 s ==
        Spec.Agile.Hash.update_multi (get_alg i) (as_seq h0 s) (ev_v ev) (B.as_seq h0 blocks)))

noextract inline_for_extraction
let prev_len_t (a: hash_alg) =
  if is_keccak a then
    unit
  else
    prev_len:len_t a { len_v a prev_len % block_length a = 0 }

noextract inline_for_extraction
let prev_len_v #a (prev_len: prev_len_t a): Spec.Hash.Incremental.Definitions.prev_length_t a
=
  if is_keccak a then
    ()
  else
    len_v a prev_len

noextract inline_for_extraction
let extra_state_of_prev_length #a (x: Spec.Hash.Incremental.Definitions.prev_length_t a): Spec.Agile.Hash.extra_state a =
  match a with
  | Blake2B | Blake2S -> x
  | _ -> ()

noextract inline_for_extraction
let update_last_st (i:impl) =
  let a = get_alg i in
  s:state i ->
  prev_len:prev_len_t a ->
  input:B.buffer uint8 {
    (if is_keccak a then True else (B.length input + len_v a prev_len) `less_than_max_input_length` a) /\
    B.length input <= block_length a
  } ->
  input_len:size_t { B.length input = v input_len } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h s /\ B.live h input /\ B.disjoint s input /\
      Spec.Agile.Hash.update_multi_pre a (extra_state_of_prev_length (prev_len_v prev_len)) (B.as_seq h input)))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer s) h0 h1) /\
      as_seq h1 s ==
        Spec.Hash.Incremental.update_last a (as_seq h0 s)
                                          (prev_len_v prev_len)
                                          (B.as_seq h0 input)))

inline_for_extraction noextract
let fixed_len_impl = i:impl { not (is_shake (dfst i)) }

noextract inline_for_extraction
let finish_st (i:fixed_len_impl) =
  s:state i -> dst:hash_t (get_alg i) -> ST.Stack unit
  (requires (fun h ->
    B.live h s /\ B.live h dst /\ B.disjoint s dst))
  (ensures (fun h0 _ h1 ->
    M.(modifies (loc_buffer dst `loc_union` loc_buffer s) h0 h1) /\
    Seq.equal (B.as_seq h1 dst) (Spec.Agile.Hash.finish (get_alg i) (as_seq h0 s) ())))

noextract inline_for_extraction
let hash_st (a: fixed_len_alg) =
  output:hash_t a->
  input:B.buffer uint8 ->
  input_len:size_t { B.length input = v input_len } ->
  ST.Stack unit
    (requires (fun h ->
      B.live h input /\
      B.live h output /\
      B.disjoint input output /\
      B.length input `less_than_max_input_length` a))
    (ensures (fun h0 _ h1 ->
      B.(modifies (loc_buffer output) h0 h1) /\
```

`impl` pairs an algorithm with an implementation metadata selector. `state i` is
the Low\* buffer state; `as_seq` is its ghost view. The `*_st` abbreviations are
contracts: allocation yields fresh live state; update functions expose
`Spec.Agile.Hash.update_multi` or `Spec.Hash.Incremental.update_last`; `hash_st`
proves output equals `Spec.Agile.Hash.hash`. Most helpers are
`inline_for_extraction noextract`/`noextract`, i.e. F\*-only proof vocabulary.

### 2.1 Fixed hash modules

The fixed modules bind names to these contracts (sources listed inline):

```fstar
// code/hash/Hacl.Hash.SHA2.fsti:7-49
val init_224: init_st (|SHA2_224, ()|)
val init_256: init_st (|SHA2_256, ()|)
val init_384: init_st (|SHA2_384, ()|)
val init_512: init_st (|SHA2_512, ()|)
val alloca_224: alloca_st (|SHA2_224, ()|)
val alloca_256: alloca_st (|SHA2_256, ()|)
val alloca_384: alloca_st (|SHA2_384, ()|)
val alloca_512: alloca_st (|SHA2_512, ()|)
val update_multi_224: update_multi_st (|SHA2_224, ()|)
val update_multi_256: update_multi_st (|SHA2_256, ()|)
val update_multi_384: update_multi_st (|SHA2_384, ()|)
val update_multi_512: update_multi_st (|SHA2_512, ()|)
val update_last_224: update_last_st (|SHA2_224, ()|)
val update_last_256: update_last_st (|SHA2_256, ()|)
val update_last_384: update_last_st (|SHA2_384, ()|)
val update_last_512: update_last_st (|SHA2_512, ()|)
val finish_224: finish_st (|SHA2_224, ()|)
val finish_256: finish_st (|SHA2_256, ()|)
val finish_384: finish_st (|SHA2_384, ()|)
val finish_512: finish_st (|SHA2_512, ()|)

// code/hash/Hacl.Hash.MD5.fsti:8-10; code/hash/Hacl.Hash.SHA1.fsti:8-10
val update_multi: update_multi_st (|MD5, ()|)
val update_last: update_last_st (|MD5, ()|)
val hash_oneshot: hash_st MD5
val update_multi: update_multi_st (|SHA1, ()|)
val update_last: update_last_st (|SHA1, ()|)
val hash_oneshot: hash_st SHA1

// code/hash/Hacl.Hash.SHA3.fsti:25-41, 74
val block_len (a: keccak_alg): Lib.IntTypes.(n:size_t { v n = block_length a })
val hash_len (a: keccak_alg { not (is_shake a) }): Lib.IntTypes.(n:size_t { v n = hash_length a })
val init (a: keccak_alg): init_st (| a, () |)
val update_multi (a: keccak_alg): update_multi_st (|a, ()|)
val update_last (a: keccak_alg): update_last_st (|a, ()|)
val finish (a: keccak_alg { not (is_shake a) }): finish_st (| a, ()|)
val hash (a: keccak_alg { not (is_shake a) }): hash_st a
val finish_keccak (a: keccak_alg): finish_st a

// code/hash/Hacl.Hash.Blake2{s,b}_{32,128,256}.fsti:18-45
val malloc: malloc_st (|Blake2S, M32|)
val alloca: alloca_st (|Blake2S, M32|)
val init: init_st (|Blake2S, M32|)
val update_multi: update_multi_st (|Blake2S, M32|)
val update_last: update_last_st (|Blake2S, M32|)
val finish: finish_st (|Blake2S, M32|)
val hash: hash_st Blake2S
val malloc: malloc_st (|Blake2S, M128|)
val alloca: alloca_st (|Blake2S, M128|)
val init: init_st (|Blake2S, M128|)
val update_multi: update_multi_st (|Blake2S, M128|)
let update_multi_no_inline: update_multi_st (|Blake2S, M128|) = update_multi
val update_last: update_last_st (|Blake2S, M128|)
let update_last_no_inline: update_last_st (|Blake2S, M128|) = update_last
val finish: finish_st (|Blake2S, M128|)
val hash: hash_st Blake2S
val copy_internal_state (src dst: state (| Spec.Agile.Hash.Blake2S, Hacl.Impl.Blake2.Core.M128 |)): Stack unit
val malloc: malloc_st (|Blake2B, M32|)
val alloca: alloca_st (|Blake2B, M32|)
val init: init_st (|Blake2B, M32|)
val update_multi: update_multi_st (|Blake2B, M32|)
val update_last: update_last_st (|Blake2B, M32|)
val finish: finish_st (|Blake2B, M32|)
val hash: hash_st Blake2B
val malloc: malloc_st (|Blake2B, M256|)
val alloca: alloca_st (|Blake2B, M256|)
val init: init_st (|Blake2B, M256|)
val update_multi: update_multi_st (|Blake2B, M256|)
let update_multi_no_inline: update_multi_st (|Blake2B, M256|) = update_multi
val update_last: update_last_st (|Blake2B, M256|)
let update_last_no_inline: update_last_st (|Blake2B, M256|) = update_last
val finish: finish_st (|Blake2B, M256|)
val hash: hash_st Blake2B
val copy_internal_state (src dst: state (| Spec.Agile.Hash.Blake2B, Hacl.Impl.Blake2.Core.M256 |)): Stack unit
```

## 3. Streaming functor API

### 3.1 `stateful`

Source: `code/streaming/Hacl.Streaming.Interface.fsti:55-144`.

```fstar
type stateful (index: Type0) =
| Stateful:
  // Low-level types
  s: (index -> Type0) ->

  // Astract footprint.
  footprint: (#i:index -> h:HS.mem -> s:s i -> GTot B.loc) ->
  freeable: (#i:index -> h:HS.mem -> p:s i -> Type) ->
  invariant: (#i:index -> h:HS.mem -> s:s i -> Type) ->

  // A pure representation of an s
  t: (index -> Type0) ->
  v: (i:index -> h:HS.mem -> s:s i -> GTot (t i)) ->

  // Adequate framing lemmas, relying on v.
  invariant_loc_in_footprint: (#i:index -> h:HS.mem -> s:s i -> Lemma
    (requires (invariant h s))
    (ensures (B.loc_in (footprint #i h s) h))
    [ SMTPat (invariant h s) ]) ->

  frame_invariant: (#i:index -> l:B.loc -> s:s i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      B.loc_disjoint l (footprint #i h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      invariant h1 s /\
      v i h0 s == v i h1 s /\
      footprint #i h1 s == footprint #i h0 s))
    [ SMTPat (invariant h1 s); SMTPat (B.modifies l h0 h1) ]) ->

  frame_freeable: (#i:index -> l:B.loc -> s:s i -> h0:HS.mem -> h1:HS.mem -> Lemma
    (requires (
      invariant h0 s /\
      freeable h0 s /\
      B.loc_disjoint l (footprint #i h0 s) /\
      B.modifies l h0 h1))
    (ensures (
      freeable h1 s))
    [ SMTPat (freeable h1 s); SMTPat (B.modifies l h0 h1) ]) ->

  // Stateful operations
  alloca: (i:index -> StackInline (s i)
    (requires (fun _ -> True))
    (ensures (fun h0 s h1 ->
      invariant #i h1 s /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint #i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint #i h1 s))))) ->

  create_in: (i:index ->
    r:HS.rid ->
    ST (option (s i))
    (requires (fun h0 ->
      HyperStack.ST.is_eternal_region r))
    (ensures (fun h0 s h1 ->
      match s with
      | None ->
          // allocation failure, nothing meaningful to say
          B.(modifies loc_none h0 h1)
      | Some s ->
          invariant #i h1 s /\
          B.(modifies loc_none h0 h1) /\
          B.fresh_loc (footprint #i h1 s) h0 h1 /\
          B.(loc_includes (loc_region_only true r) (footprint #i h1 s)) /\
          freeable #i h1 s))) ->

  free: (
    i: index -> (
    let i = G.reveal i in
    s:s i -> ST unit
    (requires fun h0 ->
      freeable #i h0 s /\
      invariant #i h0 s)
    (ensures fun h0 _ h1 ->
      B.(modifies (footprint #i h0 s) h0 h1)))) ->

  copy: (
    i:index -> (
    s_src:s i ->
    s_dst:s i ->
    Stack unit
      (requires (fun h0 ->
        invariant #i h0 s_src /\
        invariant #i h0 s_dst /\
        B.(loc_disjoint (footprint #i h0 s_src) (footprint #i h0 s_dst))))
      (ensures fun h0 _ h1 ->
        B.(modifies (footprint #i h0 s_dst) h0 h1) /\
        footprint #i h0 s_dst == footprint #i h1 s_dst /\
        (freeable #i h0 s_dst ==> freeable #i h1 s_dst) /\
```

A `stateful` instance gives a low-level representation, footprint, freeability,
invariant, pure view `v`, framing lemmas, allocation, copy and free. The proof
obligation is: modifying disjoint memory cannot change the invariant, footprint,
freeability or pure view. The type class itself is `inline_for_extraction
noextract`.

### 3.2 `block`

Source: `code/streaming/Hacl.Streaming.Interface.fsti:255-432`.

```fstar
type block (index: Type0) =
| Block:
  km: key_management ->

  // Low-level types
  state: stateful index ->
  key: stateful index ->

  // Just a value type; useful for algorithms that have a variable output length.
  output_length_t: Type0 ->

  // Introducing a notion of blocks and final result.
  max_input_len: (index -> x:U64.t { U64.v x > 0 }) ->
  output_length: (index -> output_length_t -> GTot Lib.IntTypes.(x:size_nat { x > 0 })) ->
  block_len: (index -> x:U32.t { U32.v x > 0 }) ->
  // The size of data to process at a time. Must be a multiple of block_len.
  // Controls the size of the internal buffer.
  blocks_state_len: (i:index ->
    x:U32.t { U32.v x > 0 /\ U32.v x >= U32.v (block_len i) /\ U32.v x % U32.v (block_len i) = 0 }) ->
  init_input_len: (i:index -> x:U32.t { U32.v x <= U32.v (block_len i) /\ U32.v x <= U64.v (max_input_len i) }) ->

  /// An init/update/update_last/finish specification. The long refinements were
  /// previously defined as blocks / small / output.
  init_input_s: (i:index -> key.t i -> s:S.seq uint8 { S.length s = U32.v (init_input_len i) }) ->
  init_s: (i:index -> key.t i -> state.t i) ->
  update_multi_s: (i:index ->
    state.t i ->
    prevlen:nat { prevlen % U32.v (block_len i) = 0 } ->
    s:S.seq uint8 { prevlen + S.length s <= U64.v (max_input_len i) /\ S.length s % U32.v (block_len i) = 0 } ->
    state.t i) ->
  update_last_s: (i:index ->
    state.t i ->
    prevlen:nat { prevlen % U32.v (block_len i) = 0 } ->
    s:S.seq uint8 { S.length s + prevlen <= U64.v (max_input_len i) /\ S.length s <= U32.v (block_len i) } ->
    state.t i) ->
  finish_s: (i:index -> key.t i -> state.t i -> l:output_length_t ->
    s:S.seq uint8 { S.length s = output_length i l }) ->

  /// The specification in one shot.
  spec_s: (i:index -> key.t i ->
    input:S.seq uint8 { U32.v (init_input_len i) + S.length input <= U64.v (max_input_len i) } ->
    l:output_length_t ->
    output:S.seq uint8 { S.length output == output_length i l }) ->

  // Required lemmas... clients can enjoy them in their local contexts with the SMT pattern via a let-binding.

  update_multi_zero: (i:index ->
    h:state.t i ->
    prevlen:nat { prevlen % U32.v (block_len i) = 0 /\ prevlen <= U64.v (max_input_len i) } ->
    Lemma
    (ensures (
      Math.Lemmas.modulo_lemma 0 (UInt32.v (block_len i));
      update_multi_s i h prevlen S.empty == h))) ->

  update_multi_associative: (i:index ->
    h:state.t i ->
    prevlen1:nat ->
    prevlen2:nat ->
    input1:S.seq uint8 ->
    input2:S.seq uint8 ->
    Lemma
    (requires (
      prevlen1 % U32.v (block_len i) = 0 /\
      S.length input1 % U32.v (block_len i) = 0 /\
      S.length input2 % U32.v (block_len i) = 0 /\
      prevlen1 + S.length input1 + S.length input2 <= U64.v (max_input_len i) /\
      prevlen2 = prevlen1 + S.length input1))
    (ensures (
      let input = S.append input1 input2 in
      S.length input % U32.v (block_len i) = 0 /\
      prevlen2 % U32.v (block_len i) = 0 /\
      update_multi_s i (update_multi_s i h prevlen1 input1) prevlen2 input2 ==
        update_multi_s i h prevlen1 input))
    [ SMTPat (update_multi_s i prevlen2 (update_multi_s i h prevlen1 input1) input2) ]) ->

  (* TODO: it might be possible to factorize more the proofs between Lib.UpdateMulti
   * and Spec.Hash.Incremental *)
  spec_is_incremental: (i:index ->
    key: key.t i ->
    input:S.seq uint8 { U32.v (init_input_len i) + S.length input <= U64.v (max_input_len i) } ->
    l:output_length_t ->
    Lemma (
      let input1 = S.append (init_input_s i key) input in
      let bs, rest = Lib.UpdateMulti.split_at_last_lazy (U32.v (block_len i)) input1 in
      (**) Math.Lemmas.modulo_lemma 0 (U32.v (block_len i));
      (* TODO: use update_full ? *)
      let hash0 = init_s i key in
      let hash1 = update_multi_s i hash0 0 bs in
      let hash2 = update_last_s i hash1 (S.length bs) rest in
      let hash3 = finish_s i key hash2 l in
      hash3 `S.equal` spec_s i key input l)) ->

  // Stateful operations
  index_of_state: (i:G.erased index -> (
    let i = G.reveal i in
    s: state.s i -> k: optional_key i km key -> Stack index
    (fun h0 -> state.invariant #i h0 s /\ (
      allow_inversion key_management;
      match km with
      | Erased -> True
      | Runtime ->
          key.invariant #i h0 k /\
          B.(loc_disjoint (key.footprint #i h0 k) (state.footprint #i h0 s))))
    (fun h0 i' h1 -> h0 == h1 /\ i' == i))) ->


  init: (i:G.erased index -> (
    let i = G.reveal i in
    k: key.s i ->
    buf_: B.buffer uint8 { B.length buf_ = U32.v (blocks_state_len i) } ->
    s: state.s i -> Stack unit
    (requires fun h0 ->
      key.invariant #i h0 k /\
      B.live h0 buf_ /\
      state.invariant #i h0 s /\
      B.loc_disjoint (key.footprint #i h0 k) (state.footprint #i h0 s) /\
      B.loc_disjoint (key.footprint #i h0 k) (B.loc_buffer buf_) /\
      B.loc_disjoint (B.loc_buffer buf_) (state.footprint #i h0 s))
    (ensures fun h0 _ h1 ->
      key.invariant #i h1 k /\
      (key.freeable #i h0 k ==> key.freeable #i h1 k) /\
      state.invariant #i h1 s /\
      state.v i h1 s == init_s i (key.v i h0 k) /\
      S.equal (S.slice (B.as_seq h1 buf_) 0 (U32.v (init_input_len i))) (init_input_s i (key.v i h0 k)) /\
      B.(modifies (loc_union (state.footprint #i h0 s) (loc_buffer buf_)) h0 h1) /\
      state.footprint #i h0 s == state.footprint #i h1 s /\
      (state.freeable #i h0 s ==> state.freeable #i h1 s)))) ->


  update_multi: (i:G.erased index -> (
    let i = G.reveal i in
    s:state.s i ->
    prevlen:U64.t { U64.v prevlen % U32.v (block_len i) = 0 } ->
    blocks:B.buffer uint8 { B.length blocks % U32.v (block_len i) = 0 } ->
    len: U32.t { U32.v len = B.length blocks /\
                 U64.v prevlen + U32.v len <= U64.v (max_input_len i) } ->
    Stack unit
    (requires fun h0 ->
      allow_inversion key_management;
      state.invariant #i h0 s /\
      B.live h0 blocks /\
      B.(loc_disjoint (state.footprint #i h0 s) (loc_buffer blocks)))
    (ensures fun h0 _ h1 ->
      B.(modifies (state.footprint #i h0 s) h0 h1) /\
      state.footprint #i h0 s == state.footprint #i h1 s /\
      state.invariant #i h1 s /\
      state.v i h1 s == update_multi_s i (state.v i h0 s) (U64.v prevlen) (B.as_seq h0 blocks) /\
      (state.freeable #i h0 s ==> state.freeable #i h1 s)))) ->

  update_last: (
    i: G.erased index -> (
    let i = G.reveal i in
    s:state.s i ->
    prevlen:U64.t { U64.v prevlen % U32.v (block_len i) = 0 } ->
    last:B.buffer uint8 ->
    last_len:U32.t{
      last_len = B.len last /\
      U32.v last_len <= U32.v (block_len i) /\
      U64.v prevlen + U32.v last_len <= U64.v (max_input_len i)} ->
    Stack unit
    (requires fun h0 ->
      allow_inversion key_management;
      state.invariant #i h0 s /\
      B.live h0 last /\
      B.(loc_disjoint (state.footprint #i h0 s) (loc_buffer last)))
    (ensures fun h0 _ h1 ->
      state.invariant #i h1 s /\
      state.v i h1 s == update_last_s i (state.v i h0 s) (U64.v prevlen) (B.as_seq h0 last) /\
      B.(modifies (state.footprint #i h0 s) h0 h1) /\
      state.footprint #i h0 s == state.footprint #i h1 s /\
      (state.freeable #i h0 s ==> state.freeable #i h1 s)))) ->

  finish: (
    i: G.erased index -> (
    let i = G.reveal i in
    k: optional_key i km key ->
    s:state.s i ->
    dst:B.buffer uint8 ->
```

`km` controls key retention (`Erased` for hash/HMAC-style ghost keys, `Runtime`
for Poly1305). The spec fields describe init, multi-block update, last-block
update, finish, and one-shot `spec_s`; `spec_is_incremental` proves the stateful
path equals `spec_s`. The stateful fields must implement those transitions while
respecting liveness, disjointness, footprints, and key/state invariants.

### 3.3 Generated functor surface

Sources: `code/streaming/Hacl.Streaming.Functor.fsti:41-591`.

```fstar
val state_s (#index: Type0) (c: block index) (i: index)
  (t: Type0 { t == c.state.s i })
  (t': Type0 { t' == optional_key i c.km c.key }):
  Type0

inline_for_extraction noextract
let state_s' c i = state_s c i (c.state.s i) (optional_key i c.km c.key)

/// State is equipped with a superfluous type-level parameter to ensure ML-like
/// prenex polymorphism and hence low-level monomorphization via KaRaMeL.
///
/// Run-time functions MUST take t as a parameter. Proof-level functions are
/// welcome to instantiate it directly with ``c.state i``.
let state #index (c: block index) (i: index)
  (t: Type0 { t == c.state.s i })
  (t': Type0 { t' == optional_key i c.km c.key })
=
  B.pointer (state_s c i t t')

inline_for_extraction noextract
let state' c i = state c i (c.state.s i) (optional_key i c.km c.key)

val footprint_s (#index: Type0) (c: block index) (i: index) (h: HS.mem) (s: state_s' c i): GTot B.loc

let footprint (#index: Type0) (c: block index) (i: index) (m: HS.mem) (s: state' c i) =
  B.(loc_union (loc_addr_of_buffer s) (footprint_s c i m (B.deref m s)))

/// Invariants
/// ==========

noextract
let bytes = S.seq uint8

let loc_includes_union_l_footprint_s
  #index
  (c: block index)
  (i: index)
  (m: HS.mem)
  (l1 l2: B.loc) (s: state_s' c i)
: Lemma
  (requires (
    B.loc_includes l1 (footprint_s c i m s) \/ B.loc_includes l2 (footprint_s c i m s)
  ))
  (ensures (B.loc_includes (B.loc_union l1 l2) (footprint_s c i m s)))
  [SMTPat (B.loc_includes (B.loc_union l1 l2) (footprint_s c i m s))]
= B.loc_includes_union_l l1 l2 (footprint_s c i m s)

inline_for_extraction noextract
val invariant_s (#index: Type0) (c: block index) (i: index) (h: HS.mem) (s: state_s' c i): Type0

inline_for_extraction noextract
val freeable (#index : Type0) (c: block index) (i: index) (h: HS.mem) (s: state' c i) : Type0

inline_for_extraction noextract
let preserves_freeable (#index : Type0) (c: block index) (i: index) (s: state' c i) (h0 h1 : HS.mem): Type0 =
  freeable c i h0 s ==> freeable c i h1 s

inline_for_extraction noextract
let invariant #index (c: block index) (i: index) (m: HS.mem) (s: state' c i) =
  invariant_s c i m (B.get m s 0) /\
  B.live m s /\
  B.(loc_disjoint (loc_addr_of_buffer s) (footprint_s c i m (B.deref m s)))

val invariant_loc_in_footprint
  (#index: Type0)
  (c: block index)
  (i: index)
  (s: state' c i)
  (m: HS.mem)
: Lemma
  (requires (invariant c i m s))
  (ensures (B.loc_in (footprint c i m s) m))
  [SMTPat (invariant c i m s)]

/// Keeping track of the bytes fed into the algorithm so far
/// ========================================================
///
/// We offer a stateful predicate that allows the client to tie a particular
/// state to a sequence of bytes hashed so far. There are a variety of styles
/// possible, here's a recap and a discussion of the respective merits of each
/// style, so that we document and avoid going back and forth for future APIs.
///
/// 1. val update (b: erased bytes): unit
///      requires (fun h0 -> hashes h0 s b)
///      ensures (fun h1 -> hashes h1 s (b `append` data))
///
///    The problem with this one is that it requires the client to not only
///    explicitly pass an erased argument, but also requires the client, when
///    chaining calls to construct the "next" value by manually concatenating
///    (ghostly) bytes.
///
/// 2. val update (b: erased bytes): erased bytes
///      requires (fun h0 -> hashes h0 s b)
///      ensures (fun h1 b' -> hashes h1 s b' /\ b' == b `append` data)
///
///    This one is a slight improvement over 1. because the client can "get
///    their hands" on the returned bytes and doesn't need to manually create
///    the concatenation ``b `append` data`` when they chain another call to
///    update.
///
/// 3. val update (): unit
///      requires _
///      ensures (fun h0 _ h1 -> hashed h1 s == hashed h0 s `append` data)
///
///    While 1. and 2. were based on a predicate, this one relies on a function
///    that returns the bytes (ghostly) for any given state and heap. It does
///    not require the client to materialize the erased bytes, and it does not
///    require the client to manually construct intermediary ghost byte values
///    when chaining.
///
/// 4. There's another style based on a state machine and an erased value that
///    materializes all the ghost state in a single record, thus requiring only a
///    single framing lemma (as opposed to three or more for the styles 1. 2. and
///    3.). It appears that this may be overkill for this module and may be better
///    suited to TLS.
///
///                                            JP (20190607)

val seen: #index:Type0 -> c:block index -> i:index -> h:HS.mem -> s:state' c i -> GTot bytes

/// We maintain the invariant that the length of the data hashed so far is smaller
/// than the maximum length accepted by the hash algorithm.
///
/// Note that for hashes like blake2, the key is turned into a block which is then
/// concatenated with the bytes fed into the algorithm (we copy this iniial
/// block into the temporary buffer upon initilization). We count the length of
/// this initial block in the total length of the hashed data.
val seen_bounded: #index:Type0 -> c:block index -> i:index -> h:HS.mem -> s:state' c i -> Lemma
  (requires (
    invariant c i h s))
  (ensures (
    U32.v (c.init_input_len i) + S.length (seen c i h s) <= U64.v (c.max_input_len i)))

/// A fine design point here... There are two styles that have been used in
/// EverCrypt and throughout for key management.
///
/// The first one keeps an erased key in the state_s and therefore clients
/// "know" that the value of the key depends only on the state_s (*not* on a
/// memory) and hence can conclude that the key remains the same *as long as
/// the modified footprints are footprint_s*. This essentially means that you
/// cannot "reallocate" the abstract struct. This works for simple cases like
/// EverCrypt.AEAD.
///
/// Here, we definitely reallocate the abstract struct to functionally update
/// the size of the buffer, so we don't bother and reveal everywhere that the
/// key remains the same (i.e. we specify it fully just like ``seen``).
///
/// Note: annotating the projector because of an interleaving bug.
val reveal_key: #index:Type0 -> c:block index -> i:index -> h:HS.mem -> s:state' c i -> GTot (c.key.I.t i)

/// Framing
/// =======
///
/// Everything a client needs to know when they modify something **disjoint**
/// from a hash state.
///
/// Note that the invariant now bundles a variety of conditions related to the
/// hashing predicate, meaning that the only way to establish the invariant is
/// actually to initialize the underlying state. This means that the framing
/// lemmas for invariant and hashed could be bundled together. If we committed
/// to always heap allocating, then we could conceivably have a single framing
/// lemma.

val frame_invariant: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state' c i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (
    invariant c i h1 s /\
    footprint c i h0 s == footprint c i h1 s /\
    preserves_freeable c i s h0 h1))
  [ SMTPat (invariant c i h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_seen: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state' c i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (seen c i h0 s == seen c i h1 s))
  [ SMTPat (seen c i h1 s); SMTPat (B.modifies l h0 h1) ]

val frame_key: #index:Type0 -> c:block index -> i:index -> l:B.loc -> s:state' c i -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant c i h0 s /\
    B.loc_disjoint l (footprint c i h0 s) /\
    B.modifies l h0 h1))
  (ensures (reveal_key c i h0 s == reveal_key c i h1 s))
  [ SMTPat (reveal_key c i h1 s); SMTPat (B.modifies l h0 h1) ]


/// Stateful API
/// ============

inline_for_extraction noextract
val index_of_state:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  s:state c i t t' ->
  Stack index
  (fun h0 -> invariant c i h0 s)
  (fun h0 i' h1 -> h0 == h1 /\ i' == i))

// The number of bytes fed so far into the hash, so that the client doesn't have
// to track it themselves, since this module does it anyhow.
inline_for_extraction noextract
val seen_length:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  s:state c i t t' ->
  Stack U64.t
  (fun h0 -> invariant c i h0 s)
  (fun h0 l h1 -> h0 == h1 /\ U64.v l == U32.v (c.init_input_len i) +  S.length (seen c i h0 s)))

inline_for_extraction noextract
let malloc_st
  (#index: Type0)
  (c:block index)
  (i:index)
  (t:Type0 { t == c.state.s i })
  (t':Type0 { t' == optional_key i c.km c.key }) =
  k:c.key.s i ->
  r: HS.rid ->
  ST (B.buffer (state_s c i t t'))
  (requires (fun h0 ->
    c.key.invariant #i h0 k /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    if B.g_is_null s then
      // out of memory, underlying calls to the system malloc failed
      B.(modifies loc_none h0 h1)
    else
      B.length s == 1 /\ // this turns the return type into a `state c i t t'`
      invariant c i h1 s /\
      freeable c i h1 s /\
      seen c i h1 s == S.empty /\
      reveal_key c i h1 s == c.key.v i h0 k /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint c i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))

inline_for_extraction noextract
val malloc:
  #index: Type0 ->
  c:block index ->
  i:index ->
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  malloc_st c i t t'

inline_for_extraction noextract
let copy_st
  (#index: Type0)
  (c:block index)
  (i:index)
  (t:Type0 { t == c.state.s i })
  (t':Type0 { t' == optional_key i c.km c.key }) =
  s0:state c i t t' ->
  r: HS.rid ->
  ST (B.buffer (state_s c i t t'))
  (requires (fun h0 ->
    invariant c i h0 s0 /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    if B.g_is_null s then
      // out of memory, underlying calls to the system malloc failed
      B.(modifies loc_none h0 h1)
    else
      B.length s == 1 /\ // this turns the return type into a `state c i t t'`
      invariant c i h1 s /\
      freeable c i h1 s /\
      seen c i h1 s == seen c i h0 s0 /\
      reveal_key c i h1 s == reveal_key c i h0 s0 /\
      B.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint c i h1 s) h0 h1 /\
      B.(loc_includes (loc_region_only true r) (footprint c i h1 s))))

inline_for_extraction noextract
val copy:
  #index: Type0 ->
  c:block index ->
  i:G.erased index ->
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key (G.reveal i) c.km c.key } ->
  copy_st c i t t'

inline_for_extraction noextract
let alloca_st
  (#index: Type0)
  (c:block index)
  (i:index)
  (t:Type0 { t == c.state.s i })
  (t':Type0 { t' == optional_key i c.km c.key }) =
  k:c.key.s i ->
  StackInline (state c i t t')
  (requires (fun h0 ->
    c.key.invariant #i h0 k))
  (ensures (fun h0 s h1 ->
    invariant c i h1 s /\
    seen c i h1 s == S.empty /\
    reveal_key c i h1 s == c.key.v i h0 k /\
    B.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint c i h1 s) h0 h1 /\
    B.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint c i h1 s))))

inline_for_extraction noextract
val alloca:
  #index: Type0 ->
  c:block index ->
  i:index ->
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  alloca_st #index c i t t'

inline_for_extraction noextract
let reset_st
  (#index: Type0)
  (c:block index)
  (i:G.erased index)
  (t:Type0 { t == c.state.s i })
  (t':Type0 { t' == optional_key (G.reveal i) c.km c.key }) =
  state:state c i t t' ->
  key:c.key.s i ->
  Stack unit
  (requires (fun h0 ->
    c.key.invariant #i h0 key /\
    B.loc_disjoint (c.key.footprint #i h0 key) (footprint c i h0 state) /\
    invariant c i h0 state))
  (ensures (fun h0 _ h1 ->
    invariant c i h1 state /\
    seen c i h1 state == S.empty /\
    reveal_key c i h1 state == c.key.v i h0 key /\
    footprint c i h0 state == footprint c i h1 state /\
    B.(modifies (footprint c i h0 state) h0 h1) /\
    preserves_freeable c i state h0 h1))

inline_for_extraction noextract
val reset:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  reset_st #index c i t t')

unfold noextract
let update_pre
  #index
  (c: block index)
  (i: index)
  (s: state' c i)
  (data: B.buffer uint8)
  (len: UInt32.t)
  (h0: HS.mem)
=
  invariant c i h0 s /\
  B.live h0 data /\
  U32.v len = B.length data /\
  B.(loc_disjoint (loc_buffer data) (footprint c i h0 s))

unfold noextract
let update_post
  #index
  (c: block index)
  (i: index)
  (s: state' c i)
  (data: B.buffer uint8)
  (len: UInt32.t)
  (h0 h1: HS.mem)
=
  invariant c i h1 s /\
  B.(modifies (footprint c i h0 s) h0 h1) /\
  footprint c i h0 s == footprint c i h1 s /\
  seen c i h1 s == seen c i h0 s `S.append` B.as_seq h0 data /\
  reveal_key c i h1 s == reveal_key c i h0 s /\
  preserves_freeable c i s h0 h1

inline_for_extraction noextract
let update_st
  (#index: Type0)
  (c:block index)
  (i:index)
  (t:Type0 { t == c.state.s i })
  (t':Type0 { t' == optional_key i c.km c.key }) =
  s:state c i t t' ->
  data: B.buffer uint8 ->
  len: UInt32.t ->
  Stack Hacl.Streaming.Types.error_code
    (requires fun h0 -> update_pre c i s data len h0)
    (ensures fun h0 s' h1 ->
      let open Hacl.Streaming.Types in
      match s' with
      | Success ->
          U32.v (c.init_input_len i) + S.length (seen c i h0 s) + UInt32.v len <= U64.v (c.max_input_len i) /\
          update_post c i s data len h0 h1
      | MaximumLengthExceeded ->
          U32.v (c.init_input_len i) + S.length (seen c i h0 s) + UInt32.v len > U64.v (c.max_input_len i) /\
          h0 == h1
      | _ ->
          False)

inline_for_extraction noextract
val update:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  update_st #index c i t t')

inline_for_extraction noextract
let digest_st
  #index
  (c: block index)
  (i: index)
  (t: Type0 { t == c.state.s i })
  (t':Type0 { t' == optional_key i c.km c.key }) =
  s:state c i t t' ->
  dst:B.buffer uint8 ->
  l:c.output_length_t { B.length dst == c.output_length i l } ->
  Stack unit
    (requires fun h0 ->
      invariant c i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint c i h0 s)))
    (ensures fun h0 s' h1 ->
      invariant c i h1 s /\
      seen c i h0 s == seen c i h1 s /\
      reveal_key c i h1 s == reveal_key c i h0 s /\
      footprint c i h0 s == footprint c i h1 s /\
      B.(modifies (loc_union (loc_buffer dst) (footprint c i h0 s)) h0 h1) /\ (
      seen_bounded c i h0 s;
      S.equal (B.as_seq h1 dst) (c.spec_s i (reveal_key c i h0 s) (seen c i h0 s) l)) /\
      preserves_freeable c i s h0 h1)

/// A word of caution. Once partially applied to a type class, this function
/// will generate a stack allocation at type ``state i`` via ``c.alloca``. If
/// ``state`` is indexed over ``i``, then this function will not compile to C.
/// (In other words: there's a reason why digest does *NOT* take i ghostly.)
/// 20240328, JP: actually tried this. It's super ugly C code but it works.
///
/// To work around this, it suffices to apply ``digest`` to each possible
/// value for the index, then to abstract over ``i`` again if agility is
/// desired. See EverCrypt.Hash.Incremental for an example. Alternatively, we
/// could provide a finish that relies on a heap allocation of abstract state
/// and does not need to be specialized.
/// 20250227 JP: bit the bullet, did it, see digest_heap below
inline_for_extraction noextract
val digest:
  #index:Type0 ->
  c:block index ->
  i:index ->
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key (G.reveal i) c.km c.key } ->
  digest_st c i t t'

/// Variant of the above that performs a runtime lookup via index_of_state,
/// which in turn prevents specialization, but does not require an additional
/// runtime parameter. Useful for Blake2.
inline_for_extraction noextract
val digest_erased:
  #index:Type0 ->
  c:block index ->
  i:G.erased index ->
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key (G.reveal i) c.km c.key } ->
  digest_st c i t t'

inline_for_extraction noextract
let digest_heap_st
  #index
  (c: block index)
  (i: index)
  (t: Type0 { t == c.state.s i })
  (t':Type0 { t' == optional_key i c.km c.key }) =
  s:state c i t t' ->
  dst:B.buffer uint8 ->
  l:c.output_length_t { B.length dst == c.output_length i l } ->
  ST Hacl.Streaming.Types.error_code
    (requires fun h0 ->
      invariant c i h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (loc_buffer dst) (footprint c i h0 s)))
    (ensures fun h0 s' h1 ->
      let open Hacl.Streaming.Types in
      match s' with
      | Success ->
          invariant c i h1 s /\
          seen c i h0 s == seen c i h1 s /\
          reveal_key c i h1 s == reveal_key c i h0 s /\
          footprint c i h0 s == footprint c i h1 s /\
          B.(modifies (loc_union (loc_buffer dst) (footprint c i h0 s)) h0 h1) /\ (
          seen_bounded c i h0 s;
          S.equal (B.as_seq h1 dst) (c.spec_s i (reveal_key c i h0 s) (seen c i h0 s) l)) /\
          preserves_freeable c i s h0 h1
      | OutOfMemory ->
          B.(modifies loc_none h0 h1)
      | _ -> False)

inline_for_extraction noextract
val digest_heap:
  #index:Type0 ->
  c:block index ->
  i:index ->
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key (G.reveal i) c.km c.key } ->
  digest_heap_st c i t t'

inline_for_extraction noextract
val digest_heap_erased:
  #index:Type0 ->
  c:block index ->
  i:G.erased index ->
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key (G.reveal i) c.km c.key } ->
  digest_heap_st c i t t'

inline_for_extraction noextract
let free_st
  (#index: Type0)
  (c:block index)
  (i:index)
  (t:Type0 { t == c.state.s i })
  (t':Type0 { t' == optional_key i c.km c.key }) =
  s:state c i t t' ->
  ST unit
  (requires fun h0 ->
    invariant c i h0 s /\
    freeable c i h0 s)
  (ensures fun h0 _ h1 ->
    B.modifies (footprint c i h0 s) h0 h1)

inline_for_extraction noextract
val free:
  #index:Type0 ->
  c:block index ->
  i:G.erased index -> (
  let i = G.reveal i in
  t:Type0 { t == c.state.s i } ->
  t':Type0 { t' == optional_key i c.km c.key } ->
  free_st #index c i t t')
```

Operationally, `state_s` is abstract and `state` is a pointer. `invariant` and
`footprint` are the ownership boundary. `seen c i h s` is the ghost sequence of
all successful updates since allocation/reset; `reveal_key` is the ghost key.
After `update Success`, `seen` appends `B.as_seq h0 data`. After `digest`, the
postcondition proves
`B.as_seq h1 dst == c.spec_s i (reveal_key c i h0 s) (seen c i h0 s) l` while
preserving the state. `frame_invariant`, `frame_seen`, and `frame_key` are the
client lemmas used after unrelated disjoint memory changes. `seen_length`,
`alloca`, ghost accessors and framing lemmas are F\*-only (`noextract` or proof
level); extracted functions are the instantiated runtime operations.

## 4. HMAC and HKDF

### 4.1 HACL HMAC

Source: `code/hmac/Hacl.HMAC.fsti:22-124`.

```fstar
let key_and_data_fits (a: hash_alg): Lemma
  (ensures ((block_length a + pow2 32) `less_than_max_input_length` a))
=
  let open FStar.Mul in
  assert_norm (8 * 16 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

inline_for_extraction noextract
let compute_st (a: fixed_len_alg) =
  tag: B.buffer uint8 {B.length tag == hash_length a} ->
  key: B.buffer uint8{ keysized a (B.length key) /\ B.disjoint key tag } ->
  keylen: UInt32.t{ UInt32.v keylen = B.length key } ->
  data: B.buffer uint8{ B.length data + block_length a < pow2 32 } ->
  datalen: UInt32.t{ UInt32.v datalen = B.length data } ->
  Stack unit
  (requires fun h0 -> B.live h0 tag /\ B.live h0 key /\ B.live h0 data)
  (ensures fun h0 _ h1 ->
    key_and_data_fits a;
    LowStar.Modifies.(modifies (loc_buffer tag) h0 h1) /\
    B.as_seq h1 tag == hmac a (B.as_seq h0 key) (B.as_seq h0 data))

inline_for_extraction noextract
val mk_compute:
  i: D.fixed_len_impl ->
  hash: D.hash_st (D.get_alg i) ->
  alloca: D.alloca_st i ->
  init: D.init_st i ->
  update_multi: D.update_multi_st i ->
  update_last: D.update_last_st i ->
  finish: D.finish_st i ->
  compute_st (D.get_alg i)

[@@ Comment "Write the HMAC-MD5 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 byte.
`dst` must point to 16 bytes of memory."]
val compute_md5: compute_st MD5

[@@ Comment "Write the HMAC-SHA-1 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 byte.
`dst` must point to 20 bytes of memory."]
val compute_sha1: compute_st SHA1

[@@ Comment "Write the HMAC-SHA-2-224 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 28 bytes of memory."]
val compute_sha2_224: compute_st SHA2_224

[@@ Comment "Write the HMAC-SHA-2-256 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory."]
val compute_sha2_256: compute_st SHA2_256

[@@ Comment "Write the HMAC-SHA-2-384 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 48 bytes of memory."]
val compute_sha2_384: compute_st SHA2_384

[@@ Comment "Write the HMAC-SHA-2-512 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory."]
val compute_sha2_512: compute_st SHA2_512

[@@ Comment "Write the HMAC-SHA-3-224 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 144 bytes.
`dst` must point to 28 bytes of memory."]
val compute_sha3_224: compute_st SHA3_224

[@@ Comment "Write the HMAC-SHA-3-256 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 136 bytes.
`dst` must point to 32 bytes of memory."]
val compute_sha3_256: compute_st SHA3_256

[@@ Comment "Write the HMAC-SHA-3-384 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 104 bytes.
`dst` must point to 48 bytes of memory."]
val compute_sha3_384: compute_st SHA3_384

[@@ Comment "Write the HMAC-SHA-3-512 MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 72 bytes.
`dst` must point to 64 bytes of memory."]
val compute_sha3_512: compute_st SHA3_512

[@@ Comment "Write the HMAC-BLAKE2s MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 64 bytes.
`dst` must point to 32 bytes of memory."]
val compute_blake2s_32: compute_st Blake2S

[@@ Comment "Write the HMAC-BLAKE2b MAC of a message (`data`) by using a key (`key`) into `dst`.

The key can be any length and will be hashed if it is longer and padded if it is shorter than 128 bytes.
`dst` must point to 64 bytes of memory."]
val compute_blake2b_32: compute_st Blake2B
```

`compute_st` requires live tag/key/data, exact tag and length refinements, a
`keysized` key, and a 32-bit bounded data length. It modifies only `tag` and
proves `B.as_seq h1 tag == Spec.Agile.HMAC.hmac a key data`. `mk_compute` is
`inline_for_extraction noextract`.

### 4.2 HACL HKDF

Source: `code/hkdf/Hacl.HKDF.fsti:21-190`.

```fstar
let less_strict_than_max_input_length l a =
  match max_input_length a with
  | Some max -> l < max
  | None -> true

let key_and_data_fits (a:fixed_len_alg) :
  Lemma ((block_length a + pow2 32) `less_than_max_input_length` a)
=
  let open FStar.Mul in
  assert_norm (8 * 16 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

let hash_block_length_fits (a:fixed_len_alg) :
  Lemma ((hash_length a + pow2 32 + block_length a) `less_strict_than_max_input_length` a)
=
  let open FStar.Mul in
  assert_norm (8 * 16 + 8 * 8 + pow2 32 < pow2 61);
  assert_norm (pow2 61 < pow2 125)

inline_for_extraction noextract
let extract_st (a:fixed_len_alg) =
  prk     : B.buffer uint8 ->
  salt    : B.buffer uint8 ->
  saltlen : pub_uint32 ->
  ikm     : B.buffer uint8 ->
  ikmlen  : pub_uint32 ->
  Stack unit
  (requires fun h0 ->
    B.live h0 prk /\ B.live h0 salt /\ B.live h0 ikm /\
    B.disjoint salt prk /\ B.disjoint ikm prk /\
    B.length prk == hash_length a /\
    v saltlen == B.length salt /\
    v ikmlen == B.length ikm /\
    Spec.Agile.HMAC.keysized a (v saltlen) /\
    B.length ikm + block_length a < pow2 32)
  (ensures fun h0 _ h1 ->
    key_and_data_fits a;
    B.modifies (B.loc_buffer prk) h0 h1 /\
    B.as_seq h1 prk == extract a (B.as_seq h0 salt) (B.as_seq h0 ikm))

inline_for_extraction noextract
let expand_st (a:fixed_len_alg) =
  okm     : B.buffer uint8 ->
  prk     : B.buffer uint8 ->
  prklen  : pub_uint32 ->
  info    : B.buffer uint8 ->
  infolen : pub_uint32 ->
  len     : pub_uint32 ->
  Stack unit
  (requires fun h0 ->
    B.live h0 okm /\ B.live h0 prk /\ B.live h0 info /\
    B.disjoint okm prk /\
    v prklen == B.length prk /\
    v infolen == B.length info /\
    v len == B.length okm /\
    hash_length a <= v prklen /\
    Spec.Agile.HMAC.keysized a (v prklen) /\
    hash_length a + v infolen + 1 + block_length a < pow2 32 /\
    v len <= FStar.Mul.(255 * hash_length a))
  (ensures fun h0 _ h1 ->
    hash_block_length_fits a;
    B.modifies (B.loc_buffer okm) h0 h1 /\
    B.as_seq h1 okm == expand a (B.as_seq h0 prk) (B.as_seq h0 info) (v len))

inline_for_extraction noextract
val mk_extract:
  a: fixed_len_alg ->
  hmac: Hacl.HMAC.compute_st a ->
  extract_st a

inline_for_extraction noextract
val mk_expand:
  a: fixed_len_alg ->
  hmac: Hacl.HMAC.compute_st a ->
  expand_st a

[@@ Comment "Expand pseudorandom key to desired length.

@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from. Can be a zero-length string.
@param infolen Length of context and application specific information.
@param len Length of output keying material."]
val expand_sha2_256: expand_st SHA2_256

[@@ Comment "Extract a fixed-length pseudorandom key from input keying material.

@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material."]
val extract_sha2_256: extract_st SHA2_256

[@@ Comment "Expand pseudorandom key to desired length.

@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from. Can be a zero-length string.
@param infolen Length of context and application specific information.
@param len Length of output keying material."]
val expand_sha2_384: expand_st SHA2_384

[@@ Comment "Extract a fixed-length pseudorandom key from input keying material.

@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material."]
val extract_sha2_384: extract_st SHA2_384

[@@ Comment "Expand pseudorandom key to desired length.

@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from. Can be a zero-length string.
@param infolen Length of context and application specific information.
@param len Length of output keying material."]
val expand_sha2_512: expand_st SHA2_512

[@@ Comment "Extract a fixed-length pseudorandom key from input keying material.

@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material."]
val extract_sha2_512: extract_st SHA2_512

[@@ Comment "Expand pseudorandom key to desired length.

@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from. Can be a zero-length string.
@param infolen Length of context and application specific information.
@param len Length of output keying material."]
val expand_blake2s_32: expand_st Blake2S

[@@ Comment "Extract a fixed-length pseudorandom key from input keying material.

@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material."]
val extract_blake2s_32: extract_st Blake2S

[@@ Comment "Expand pseudorandom key to desired length.

@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from. Can be a zero-length string.
@param infolen Length of context and application specific information.
@param len Length of output keying material."]
val expand_blake2b_32: expand_st Blake2B

[@@ Comment "Extract a fixed-length pseudorandom key from input keying material.

@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material."]
val extract_blake2b_32: extract_st Blake2B
```

`extract_st` proves `prk == Spec.Agile.HKDF.extract a salt ikm`. `expand_st`
proves `okm == Spec.Agile.HKDF.expand a prk info (v len)`, with the HKDF
`255 * hash_length a` bound. Constructors are `inline_for_extraction noextract`.

### 4.3 EverCrypt HMAC/HKDF

Source: `providers/evercrypt/EverCrypt.HMAC.fsti:30-54` and
`providers/evercrypt/EverCrypt.HKDF.fsti:41-114`.

```fstar
  keylen: UInt32.t{ UInt32.v keylen = B.length key } ->
  // Can we have max_input_length a instead of pow2 32?
  data: B.buffer uint8{ B.length data + block_length a < pow2 32 } ->
  datalen: UInt32.t{ UInt32.v datalen = B.length data } ->
  Stack unit
  (requires fun h0 -> B.live h0 tag /\ B.live h0 key /\ B.live h0 data)
  (ensures  fun h0 _ h1 ->
    key_and_data_fits a;
    LowStar.Modifies.(modifies (loc_buffer tag) h0 h1) /\
    B.as_seq h1 tag == hmac a (B.as_seq h0 key) (B.as_seq h0 data))

let is_supported_alg = function
| SHA1 | SHA2_256 | SHA2_384 | SHA2_512 | Blake2S | Blake2B -> true
| _ -> false

let supported_alg = a:hash_alg{ is_supported_alg a }

/// The agile version that dynamically dispatches between the above four

//18-07-13 pick uniform names? hash{spec} vs compute{hmac}

(* The implementation of compute relies on 3 the variants of SHA2 supported by HACL*;
   Tolerates overlaps between tag and data (we used to require [disjoint data tag])
*)

```

```fstar
  (requires fun h0 ->
    B.live h0 prk /\ B.live h0 salt /\ B.live h0 ikm /\
    B.disjoint salt prk /\ B.disjoint ikm prk /\
    B.length prk == hash_length a /\
    v saltlen == B.length salt /\
    v ikmlen == B.length ikm /\
    Spec.Agile.HMAC.keysized a (v saltlen) /\
    B.length ikm + block_length a < pow2 32)
  (ensures fun h0 _ h1 ->
    key_and_data_fits a;
    B.modifies (B.loc_buffer prk) h0 h1 /\
    B.as_seq h1 prk == extract a (B.as_seq h0 salt) (B.as_seq h0 ikm))

inline_for_extraction noextract
let expand_st (a:fixed_len_alg) =
  okm     : B.buffer uint8 ->
  prk     : B.buffer uint8 ->
  prklen  : pub_uint32 ->
  info    : B.buffer uint8 ->
  infolen : pub_uint32 ->
  len     : pub_uint32 ->
  Stack unit
  (requires fun h0 ->
    B.live h0 okm /\ B.live h0 prk /\ B.live h0 info /\
    B.disjoint okm prk /\
    v prklen == B.length prk /\
    v infolen == B.length info /\
    v len == B.length okm /\
    hash_length a <= v prklen /\
    Spec.Agile.HMAC.keysized a (v prklen) /\
    hash_length a + v infolen + 1 + block_length a < pow2 32 /\
    v len <= FStar.Mul.(255 * hash_length a))
  (ensures fun h0 _ h1 ->
    hash_block_length_fits a;
    B.modifies (B.loc_buffer okm) h0 h1 /\
    B.as_seq h1 okm == expand a (B.as_seq h0 prk) (B.as_seq h0 info) (v len))




/// Agile versions that dynamically dispatch between the above four

(** @type: true
*)
[@@ Comment "Expand pseudorandom key to desired length.

@param a Hash function to use. Usually, the same as used in `EverCrypt_HKDF_extract`.
@param okm Pointer to `len` bytes of memory where output keying material is written to.
@param prk Pointer to at least `HashLen` bytes of memory where pseudorandom key is read from. Usually, this points to the output from the extract step.
@param prklen Length of pseudorandom key.
@param info Pointer to `infolen` bytes of memory where context and application specific information is read from.
@param infolen Length of context and application specific information. Can be 0.
@param len Length of output keying material."]
val expand: a:EverCrypt.HMAC.supported_alg -> expand_st a

(** @type: true
*)
[@@ Comment "Extract a fixed-length pseudorandom key from input keying material.

@param a Hash function to use. The allowed values are:
  * `Spec_Hash_Definitions_Blake2B` (`HashLen` = 64), 
  * `Spec_Hash_Definitions_Blake2S` (`HashLen` = 32), 
  * `Spec_Hash_Definitions_SHA2_256` (`HashLen` = 32), 
  * `Spec_Hash_Definitions_SHA2_384` (`HashLen` = 48), 
  * `Spec_Hash_Definitions_SHA2_512` (`HashLen` = 64), and
  * `Spec_Hash_Definitions_SHA1` (`HashLen` = 20).
@param prk Pointer to `HashLen` bytes of memory where pseudorandom key is written to.
  `HashLen` depends on the used algorithm `a`. See above.
@param salt Pointer to `saltlen` bytes of memory where salt value is read from.
@param saltlen Length of salt value.
@param ikm Pointer to `ikmlen` bytes of memory where input keying material is read from.
@param ikmlen Length of input keying material."]
val extract: a:EverCrypt.HMAC.supported_alg -> extract_st a
```

EverCrypt reexports equivalent contracts without requiring clients to depend on
HACL constructors. `supported_alg` is `SHA1`, `SHA2_256`, `SHA2_384`,
`SHA2_512`, `Blake2S`, or `Blake2B`.

### 4.4 `Hacl.Agile.Hash` and streaming HMAC

Implementation-indexed agility (`code/streaming/Hacl.Agile.Hash.fsti:48-337`):

```fstar
type impl =
  | MD5
  | SHA1
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512
  | SHA3_224
  | SHA3_256
  | SHA3_384
  | SHA3_512
  | Blake2S_32
  | Blake2S_128: squash EverCrypt.TargetConfig.hacl_can_compile_vec128 -> impl
  | Blake2B_32
  | Blake2B_256: squash EverCrypt.TargetConfig.hacl_can_compile_vec256 -> impl

inline_for_extraction noextract
val _sync_decl2: unit

let alg_of_impl (i: impl): fixed_len_alg =
  let _ = allow_inversion impl in
  match i with
  | MD5 -> Spec.Agile.Hash.MD5
  | SHA1 -> Spec.Agile.Hash.SHA1
  | SHA2_224 -> Spec.Agile.Hash.SHA2_224
```

```fstar
val state_s: (i: impl) -> Type0
let state alg = B.pointer (state_s alg)

inline_for_extraction noextract
val freeable_s: #(i: impl) -> state_s i -> Type0

inline_for_extraction noextract
let freeable (#a: impl) (h: HS.mem) (p: state a) =
  B.freeable p /\ freeable_s (B.deref h p)

val footprint_s: #a:impl -> state_s a -> GTot M.loc
let footprint (#a:impl) (s: state a) (m: HS.mem) =
  M.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

let loc_includes_union_l_footprint_s
  (l1 l2: M.loc) (#a: impl) (s: state_s a)
```

```fstar
val invariant_s: (#a:impl) -> state_s a -> HS.mem -> Type0

inline_for_extraction noextract
let invariant (#a:impl) (s: state a) (m: HS.mem) =
  B.live m s /\
  M.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s (B.get m s 0) m

val repr: #a:impl ->
  s:state a -> h:HS.mem -> GTot (words_state (alg_of_impl a))

val impl_of_state: a:e_impl -> (
  let a = G.reveal a in
  s: state a -> Stack impl
  (fun h0 -> invariant s h0)
  (fun h0 a' h1 -> h0 == h1 /\ a' == a))

val fresh_is_disjoint: l1:M.loc -> l2:M.loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (B.fresh_loc l1 h0 h1 /\ l2 `B.loc_in` h0))
  (ensures (M.loc_disjoint l1 l2))

val invariant_loc_in_footprint
  (#a: impl)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant s m))
  (ensures (B.loc_in (footprint s m) m))
  [SMTPat (invariant s m)]

val frame_invariant: #a:impl -> l:M.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    invariant s h1 /\
    repr s h0 == repr s h1))

let frame_invariant_implies_footprint_preservation
  (#a: impl)
  (l: M.loc)
  (s: state a)
```

```fstar
val alloca: a:impl -> StackInline (state a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s h1) h0 h1 /\
    M.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint s h1))))

val malloc_: a:impl -> r:HS.rid -> FStar.HyperStack.ST.ST (B.buffer (state_s a))
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    if B.g_is_null s then
      B.(modifies loc_none h0 h1)
    else
      B.length s == 1 /\
      invariant s h1 /\
      M.(modifies loc_none h0 h1) /\
      B.fresh_loc (footprint s h1) h0 h1 /\
      M.(loc_includes (loc_region_only true r) (footprint s h1)) /\
      freeable h1 s))

val create_in: a:impl -> r:HS.rid -> FStar.HyperStack.ST.ST (option (state a))
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    match s with
    | None -> B.(modifies loc_none h0 h1)
    | Some s ->
        invariant s h1 /\
        M.(modifies loc_none h0 h1) /\
        B.fresh_loc (footprint s h1) h0 h1 /\
        M.(loc_includes (loc_region_only true r) (footprint s h1)) /\
        freeable h1 s))

// TODO: expose create for potential C callers, which should return NULL for failures

val init: #a:e_impl -> (
  let a = Ghost.reveal a in
  s: state a -> Stack unit
  (requires invariant s)
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.init (alg_of_impl a) /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1))

inline_for_extraction noextract
let ev_of_uint64 a (prevlen: UInt64.t { UInt64.v prevlen % block_length a = 0 }): Spec.Hash.Definitions.extra_state a =
  (if is_blake a then UInt64.v prevlen else ())

val update_multi:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a ->
  prevlen : UInt64.t { UInt64.v prevlen % block_length (alg_of_impl a) = 0 } ->
  blocks:B.buffer Lib.IntTypes.uint8 { B.length blocks % block_length (alg_of_impl a) = 0 } ->
  len: UInt32.t { v len = B.length blocks } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 blocks /\
    Spec.Agile.Hash.update_multi_pre (alg_of_impl a) (ev_of_uint64 (alg_of_impl a) prevlen) (B.as_seq h0 blocks) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer blocks)))
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.update_multi (alg_of_impl a) (repr s h0)
      (ev_of_uint64 (alg_of_impl a) prevlen) (B.as_seq h0 blocks) /\
    preserves_freeable s h0 h1))

inline_for_extraction noextract
let prev_len_of_uint64 a (prevlen: UInt64.t { UInt64.v prevlen % block_length a = 0 }): Spec.Hash.Incremental.prev_length_t a =
  (if is_keccak a then () else UInt64.v prevlen)

val update_last:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a ->
  prev_len:UInt64.t ->
  last:B.buffer Lib.IntTypes.uint8 { B.length last <= block_length (alg_of_impl a) } ->
  last_len:UInt32.t {
    v last_len = B.length last /\
    (v prev_len + v last_len) `less_than_max_input_length` (alg_of_impl a) /\
    v prev_len % block_length (alg_of_impl a) = 0 } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 last /\
    Spec.Agile.Hash.update_multi_pre (alg_of_impl a) (ev_of_uint64 (alg_of_impl a) prev_len) (B.as_seq h0 last) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer last)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 ==
      Spec.Hash.Incremental.update_last (alg_of_impl a) (repr s h0) (prev_len_of_uint64 (alg_of_impl a) prev_len)
                                             (B.as_seq h0 last) /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1))

val finish:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a ->
  dst:B.buffer Lib.IntTypes.uint8 { B.length dst = hash_length (alg_of_impl a) } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 dst /\
    M.(loc_disjoint (footprint s h0) (loc_buffer dst)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (loc_buffer dst `loc_union` footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    B.as_seq h1 dst == Spec.Agile.Hash.finish (alg_of_impl a) (repr s h0) () /\
    preserves_freeable s h0 h1))

val free_:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a -> FStar.HyperStack.ST.ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))

// Avoids C-level collisions with the stdlib free.
// Not clear why we need to repeat the type annotation.
inline_for_extraction noextract
let free: #a:e_impl -> (
  let a = Ghost.reveal a in
  s:state a -> FStar.HyperStack.ST.ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))
 = free_

[@ Comment "Warning: this function cannot copy across implementations of the
same algorithm. Therefore, you must make sure that you do not attempt to copy,
say, a Blake2B_32 state into a Blake2B_256 or vice-versa. This typically happens
if the CPU run-time detection code on the client side executes after state
creation, leading to a non-SIMD state being created, and later on, SIMD states
appearing for the same algorithm." ]
val copy:
  #a:e_impl -> (
  let a = Ghost.reveal a in
  s_src:state a ->
  s_dst:state a ->
  Stack unit
    (requires (fun h0 ->
      invariant s_src h0 /\
      invariant s_dst h0 /\
      B.(loc_disjoint (footprint s_src h0) (footprint s_dst h0))))
    (ensures fun h0 _ h1 ->
      M.(modifies (footprint s_dst h0) h0 h1) /\
      footprint s_dst h0 == footprint s_dst h1 /\
      preserves_freeable s_dst h0 h1 /\
      invariant s_dst h1 /\
      repr s_dst h1 == repr s_src h0))

val hash: i:impl -> Hacl.Hash.Definitions.hash_st (alg_of_impl i)
```

Streaming HMAC fixes key length in the index and applies the functor
(`code/streaming/Hacl.Streaming.HMAC.Definitions.fsti:22-251`,
`code/streaming/Hacl.Streaming.HMAC.fst:126-231`):

```fstar
/// We find ourselves in the same situation as with the most recent iteration of
/// Blake2: the key here is variable length, and the copy function would be
/// really hard to write if the source and destination had possibly different
/// key lengths (what to do? reallocate?), so we fix the key length *in the
/// index* so that we can statically enforce that the lengths match. This means
/// that a client of the streaming HMAC interface cannot copy from one state to
/// another if their key lengths differ.
let key_length i = l:UInt32.t { Spec.Agile.HMAC.keysized (alg_of_impl i) (UInt32.v l) }
type index = i:impl & key_length i

// Code quality (non-inlining variants)
let hash_len a = D.hash_len a
let block_len a = D.block_len a
let max_input_len64 a = D.max_input_len64 a

//////////////////////////////////////////////////////////////////////
// Stateful key definition, used only at initialization and reset-time
//////////////////////////////////////////////////////////////////////

let state (i: index) = b:B.buffer uint8 { B.len b == dsnd i }

let footprint (#i: index) h (k: state i): GTot B.loc =
```

```fstar
val init: (i:G.erased index -> (
    let i: index = G.reveal i in
    k: state i ->
    buf_: B.buffer uint8 { B.length buf_ = UInt32.v (D.block_len (alg i)) } ->
    s: two_state i -> Stack unit
    (requires fun h0 ->
      invariant #i h0 k /\
      B.live h0 buf_ /\
      two_invariant #i h0 s /\
      B.loc_disjoint (footprint h0 k) (two_footprint h0 s) /\
      B.loc_disjoint (footprint h0 k) (B.loc_buffer buf_) /\
      B.loc_disjoint (B.loc_buffer buf_) (two_footprint h0 s))
    (ensures fun h0 _ h1 ->
      invariant h1 k /\
      (freeable h0 k ==> freeable h1 k) /\
      two_invariant h1 s /\
      two_repr i h1 s == Spec.HMAC.Incremental.init (alg i) (v i h0 k) /\
      S.equal (S.slice (B.as_seq h1 buf_) 0 (UInt32.v (D.block_len (alg i)))) (Spec.HMAC.Incremental.init_input (alg i) (v i h0 k)) /\
      B.(modifies (loc_union (two_footprint h0 s) (loc_buffer buf_)) h0 h1) /\
      two_footprint h0 s == two_footprint h1 s /\
      (two_freeable h0 s ==> two_freeable h1 s))))

val finish: (
    i: G.erased index -> (
    let i = G.reveal i in
    k: G.erased (t i) ->
    s: two_state i ->
    dst:B.buffer uint8 ->
    l: UInt32.t { B.length dst == Spec.Agile.Hash.hash_length (alg i) } ->
    Stack unit
    (requires fun h0 ->
      two_invariant h0 s /\
      B.live h0 dst /\
      B.(loc_disjoint (two_footprint h0 s) (loc_buffer dst)))
    (ensures fun h0 _ h1 ->
      two_invariant h1 s /\
      B.(modifies (loc_buffer dst `loc_union` (two_footprint h0 s)) h0 h1) /\
      two_footprint h0 s == two_footprint h1 s /\
      B.as_seq h1 dst == Spec.HMAC.Incremental.finish (alg i) k (two_repr i h0 s) /\
```

```fstar
val malloc_:
  impl:impl -> k:B.buffer uint8 -> k_len:key_length impl { k_len == B.len k } -> (
  let c = hmac in
  let i = (| impl, k_len |) in
  let t' = G.erased (t i) in
  let t = two_state (| impl, k_len |)  in
  let open F in
  r:HS.rid ->
  dst: B.pointer (F.state c i t t') ->
  ST Hacl.Streaming.Types.error_code
  (requires (fun h0 ->
    c.key.invariant #i h0 k /\
    B.live h0 dst /\
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 ret h1 ->
    let open Hacl.Streaming.Types in
    match ret with
    | OutOfMemory ->
        B.(modifies loc_none h0 h1)
    | InvalidAlgorithm ->
        not EverCrypt.TargetConfig.hacl_can_compile_vec256 && is_blake2b_256 impl ||
        not EverCrypt.TargetConfig.hacl_can_compile_vec128 && is_blake2s_128 impl
    | Success ->
        let s = B.deref h1 dst in
        invariant c i h1 s /\
        freeable c i h1 s /\
        seen c i h1 s == S.empty /\
        reveal_key c i h1 s == c.key.v i h0 k /\
        B.(modifies (loc_buffer dst) h0 h1) /\
        B.fresh_loc (footprint c i h1 s) h0 h1 /\
        B.(loc_includes (loc_region_only true r) (footprint c i h1 s))
    | _ ->
        False)))

let malloc_ impl key key_length r dst =
  let open Hacl.Streaming.Types in
  if not EverCrypt.TargetConfig.hacl_can_compile_vec256 && is_blake2b_256 impl then
    InvalidAlgorithm
  else if not EverCrypt.TargetConfig.hacl_can_compile_vec128 && is_blake2s_128 impl then
    InvalidAlgorithm
  else
    let h0 = ST.get () in
    let st = malloc_internal (| impl, key_length |) key r in
    if B.is_null st then
      OutOfMemory
    else
      let open LowStar.BufferOps in
      let h1 = ST.get () in
      assert B.(loc_disjoint (loc_buffer dst) (F.footprint hmac (| impl, key_length |) h1 st));
      dst *= st;
      let h2 = ST.get () in
      F.frame_invariant hmac (| impl, key_length |) (B.loc_buffer dst) st h1 h2;
      Success

val reset:
  i: G.erased index -> (
  let c = hmac in
  let i = G.reveal i in
  let t' = G.erased (t i) in
  let t = two_state i in
  let open F in
  state:state c i t t' ->
  k:B.buffer uint8 ->
  k_len:key_length (dfst i) { k_len == B.len k } ->
  Stack Hacl.Streaming.Types.error_code
  (requires (fun h0 ->
    invariant c i h0 state /\ (
    k_len == dsnd i ==> (
    let key = k in
    c.key.invariant #i h0 key /\
    B.loc_disjoint (c.key.footprint #i h0 key) (footprint c i h0 state)))))
  (ensures (fun h0 r h1 ->
    let open Hacl.Streaming.Types in
    match r with
    | InvalidLength -> k_len <> dsnd i
    | Success ->
        k_len == dsnd i /\ (
        let key = k in
        invariant c i h1 state /\
        seen c i h1 state == S.empty /\
        reveal_key c i h1 state == c.key.v i h0 key /\
        footprint c i h0 state == footprint c i h1 state /\
        B.(modifies (footprint c i h0 state) h0 h1) /\
        preserves_freeable c i state h0 h1)
    | _ -> False)))

let get_impl (i: G.erased index) = F.index_of_state hmac i (stateful_agile_hash_state.s i) (G.erased (t i))

private
let reset_internal (i: G.erased index) = F.reset hmac i (stateful_agile_hash_state.s i) (G.erased (t i))

let reset i state key key_length =
  let (| _, k_len |) = get_impl i state in
  if key_length <> k_len then
    Hacl.Streaming.Types.InvalidLength
  else begin
    reset_internal i state key;
    Hacl.Streaming.Types.Success
  end

let update (i: G.erased index) = F.update hmac i (stateful_agile_hash_state.s i) (G.erased (t i))
let digest (i: G.erased index) = F.digest_heap_erased hmac i (stateful_agile_hash_state.s i) (G.erased (t i))
let free (i: G.erased index) = F.free hmac i (stateful_agile_hash_state.s i) (G.erased (t i))
let copy (i: G.erased index) = F.copy hmac i (stateful_agile_hash_state.s i) (G.erased (t i))
 
```

`type index = i:impl & key_length i`, so copy/reset preserve the stored key
length. The block instance uses `km = Erased`, and its `spec_s` is
`Spec.Agile.HMAC.hmac (alg i) k input`. `malloc_` may return
`InvalidAlgorithm` if vectorized BLAKE2 was not compiled, `OutOfMemory`, or
`Success`; `reset` may return `InvalidLength`.

## 5. Poly1305

### 5.1 Low-level and one-shot

Sources: `code/poly1305/Hacl.Impl.Poly1305.Fields.fst:26-75`,
`code/poly1305/Hacl.Impl.Poly1305.fsti:18-141`.

```fstar
type field_spec =
  | M32
  | M128
  | M256

unfold noextract
let width (s:field_spec) : Vec.lanes =
  match s with
  | M32  -> 1
  | M128 -> 2
  | M256 -> 4

unfold noextract
let limb (s:field_spec) =
  match s with
  | M32  -> F32xN.uint64xN 1
  | M128 -> F32xN.uint64xN 2
  | M256 -> F32xN.uint64xN 4

unfold noextract
let limb_zero (s:field_spec) : limb s=
  match s with
  | M32  -> F32xN.zero 1
  | M128 -> F32xN.zero 2
  | M256 -> F32xN.zero 4

unfold noextract
let wide (s:field_spec) =
  match s with
  | M32  -> F32xN.uint64xN 1
  | M128 -> F32xN.uint64xN 2
  | M256 -> F32xN.uint64xN 4

unfold noextract
let nlimb (s:field_spec) : size_t =
  match s with
  | M32  -> 5ul
  | M128 -> 5ul
  | M256 -> 5ul

unfold noextract
let blocklen (s:field_spec) : r:size_t{0 < v r /\ v r == width s * S.size_block} =
  match s with
  | M32  -> 16ul
  | M128 -> 32ul
  | M256 -> 64ul

unfold noextract
let nelem (s:field_spec) : size_t =
  match s with
```

```fstar
let poly1305_ctx (s:field_spec) = lbuffer (limb s) (nlimb s +! precomplen s)


noextract
val as_get_acc: #s:field_spec -> h:mem -> ctx:poly1305_ctx s -> GTot S.felem

noextract
val as_get_r: #s:field_spec -> h:mem -> ctx:poly1305_ctx s -> GTot S.felem

noextract
val state_inv_t: #s:field_spec -> h:mem -> ctx:poly1305_ctx s -> Type0


// If the ctx is not modified, all the components and invariants are preserved
val reveal_ctx_inv': #s:field_spec -> ctx:poly1305_ctx s -> ctx':poly1305_ctx s -> h0:mem -> h1:mem ->
  Lemma
  (requires Seq.equal (as_seq h0 ctx) (as_seq h1 ctx') /\ state_inv_t h0 ctx)
  (ensures
    as_get_r h0 ctx == as_get_r h1 ctx' /\
    as_get_acc h0 ctx == as_get_acc h1 ctx' /\
    state_inv_t h1 ctx')

let reveal_ctx_inv #s ctx h0 h1: Lemma
  (requires Seq.equal (as_seq h0 ctx) (as_seq h1 ctx) /\ state_inv_t h0 ctx)
  (ensures
    as_get_r h0 ctx == as_get_r h1 ctx /\
    as_get_acc h0 ctx == as_get_acc h1 ctx /\
    state_inv_t h1 ctx)
=
  reveal_ctx_inv' #s ctx ctx h0 h1

val ctx_inv_zeros: #s:field_spec -> ctx:poly1305_ctx s -> h:mem ->
  Lemma
  (requires as_seq h ctx == Lib.Sequence.create (v (nlimb s +! precomplen s)) (limb_zero s))
  (ensures  state_inv_t #s h ctx)


inline_for_extraction noextract
let poly1305_init_st (s:field_spec) =
    ctx:poly1305_ctx s
  -> key:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h key /\ disjoint ctx key)
  (ensures  fun h0 _ h1 ->
    modifies (loc ctx) h0 h1 /\
    state_inv_t #s h1 ctx /\
    (as_get_acc h1 ctx, as_get_r h1 ctx) == S.poly1305_init (as_seq h0 key))

[@ Meta.Attribute.specialize ]
inline_for_extraction noextract
val poly1305_init: #s:field_spec -> poly1305_init_st s


inline_for_extraction noextract
let poly1305_update1_st (s:field_spec) =
    ctx:poly1305_ctx s
  -> b:lbuffer uint8 16ul ->
  Stack unit
  (requires fun h ->
    live h ctx /\ live h b /\ disjoint b ctx /\
    state_inv_t #s h ctx)
  (ensures  fun h0 _ h1 ->
    modifies (loc ctx) h0 h1 /\
    state_inv_t #s h1 ctx /\
    as_get_r h0 ctx == as_get_r h1 ctx /\
    as_get_acc h1 ctx == S.poly1305_update1 (as_get_r h0 ctx) 16 (as_seq h0 b) (as_get_acc h0 ctx))


inline_for_extraction noextract
val poly1305_update1: (#s:field_spec) -> poly1305_update1_st s


inline_for_extraction noextract
let poly1305_update_st (s:field_spec) =
    ctx:poly1305_ctx s
  -> len:size_t
  -> text:lbuffer uint8 len ->
  Stack unit
  (requires fun h ->
    live h text /\ live h ctx /\ disjoint ctx text /\
    state_inv_t #s h ctx)
  (ensures  fun h0 _ h1 ->
    modifies (loc ctx) h0 h1 /\
    state_inv_t #s h1 ctx /\
    as_get_r h0 ctx == as_get_r h1 ctx /\
    as_get_acc h1 ctx == S.poly1305_update (as_seq h0 text) (as_get_acc h0 ctx) (as_get_r h0 ctx))


inline_for_extraction noextract
[@ Meta.Attribute.specialize ]
val poly1305_update: #s:field_spec -> poly1305_update_st s


inline_for_extraction noextract
let poly1305_finish_st (s:field_spec) =
    tag:lbuffer uint8 16ul
  -> key:lbuffer uint8 32ul
  -> ctx:poly1305_ctx s ->
  Stack unit
  (requires fun h ->
    live h tag /\ live h key /\ live h ctx /\
    disjoint tag key /\ disjoint tag ctx /\ disjoint key ctx /\
    state_inv_t #s h ctx)
  (ensures  fun h0 _ h1 ->
    modifies (loc tag |+| loc ctx) h0 h1 /\
    as_seq h1 tag == S.poly1305_finish (as_seq h0 key) (as_get_acc h0 ctx))

[@ Meta.Attribute.specialize ]
noextract inline_for_extraction
val poly1305_finish: #s:field_spec -> poly1305_finish_st s


inline_for_extraction noextract
let poly1305_mac_st (s:field_spec) =
    output:lbuffer uint8 16ul
  -> input:buffer uint8
  -> input_len:size_t { length input = v input_len }
  -> key:lbuffer uint8 32ul ->
  Stack unit
  (requires fun h ->
    live h input /\ live h output /\ live h key /\
    disjoint output input /\ disjoint output key)
  (ensures  fun h0 _ h1 ->
```

`field_spec` chooses lanes (`M32`/`M128`/`M256`). Ghost accessors `as_get_acc`
and `as_get_r` relate the buffer context to `Spec.Poly1305`. `poly1305_mac_st`
requires live/disjoint output, input and 32-byte key, and proves output equals
`Spec.Poly1305.poly1305_mac`.

### 5.2 Streaming and EverCrypt

Source: `code/streaming/Hacl.Streaming.Poly1305.fst:20-118,402-452` and wrappers
`code/streaming/Hacl.Streaming.Poly1305_(32, 128, 256).fsti:13-27`.

```fstar
let uint32 = Lib.IntTypes.uint32

open Hacl.Impl.Poly1305.Fields

/// An instance of the stateful type class for poly1305 state
/// =========================================================
///
/// We use a custom view that separates r and acc, to respect abstraction boundaries established by Poly1305.

#set-options "--fuel 0 --ifuel 1 --z3rlimit 100"

inline_for_extraction noextract
let t (fs : field_spec) = b:B.buffer (limb fs) { B.length b == 25 }

inline_for_extraction noextract
let as_raw (#fs : field_spec) (x: t fs): B.buffer (limb fs) = x

inline_for_extraction noextract
let as_lib (#fs : field_spec) (x: t fs): P.poly1305_ctx fs =
  assert (Lib.IntTypes.(v (add #U32 (nlimb fs) (precomplen fs))) == 25);
  x

inline_for_extraction noextract
let poly1305_key = I.stateful_buffer uint8 32ul (Lib.IntTypes.u8 0) unit

inline_for_extraction noextract
let as_lib_k (x: B.buffer uint8 { B.length x = 32 }): Lib.Buffer.lbuffer uint8 32ul =
  x

inline_for_extraction noextract
let num_lanes (fs : field_spec) : F32xN.lanes =
  match fs with
  | M32 -> 1
  | M128 -> 2
  | M256 -> 4

inline_for_extraction noextract
let stateful_poly1305_ctx (fs : field_spec) : I.stateful unit =
  I.Stateful
    (fun () -> t fs)
    (fun #_ _ s -> B.loc_addr_of_buffer (as_raw s))
    (fun #_ _ s -> B.freeable (as_raw s))
    (fun #_ h s -> B.live h (as_raw s) /\ P.state_inv_t h (as_lib s))
    (fun () -> Spec.Poly1305.felem & Spec.Poly1305.felem)
    (fun () h s -> P.as_get_acc h (as_lib s), P.as_get_r h (as_lib s))
    (fun #_ _ _ -> ())
    (fun #_ l s h0 h1 ->
      P.reveal_ctx_inv (as_lib s) h0 h1;
      B.modifies_buffer_elim (as_raw s) l h0 h1)
    (fun #_ _ _ _ _ -> ())

    (fun () ->
      [@inline_let]
      let n = num_lanes fs in
      let r = B.alloca (F32xN.zero n) 25ul in
      let h1 = ST.get () in
      P.ctx_inv_zeros #fs r h1;
      r)
    (fun () r ->
      [@inline_let]
      let n = num_lanes fs in
      let r = I.fallible_malloc r (F32xN.zero n) 25ul in
      if B.is_null r then
        None
      else
        let h1 = ST.get () in
        P.ctx_inv_zeros #fs r h1;
        Some r)
    (fun _ s -> B.free s)
    (fun _ src dst ->
      let h0 = ST.get () in
      B.blit src 0ul dst 0ul 25ul;
      let h1 = ST.get () in
      P.reveal_ctx_inv' (as_lib src) (as_lib dst) h0 h1)

/// Interlude for spec equivalence proofs
/// =====================================
///
/// A quick explanation about this proof of equivalence. At the spec level,
/// ``poly1305_update`` needs both ``r`` and the accumulator ``acc``. This thus
/// makes poly1305 update a function of two arguments. However, the streaming
/// facility is constructed over specifications that take one single argument.
/// Not a problem! We carry the pair ``(r, acc)`` as our "streaming functor
/// accumulator", and we now have to show that a specification in terms of
/// ``update (update (r, acc) init)`` is the same as poly1305. For that, we need
/// to do a little proof of equivalence to show first that this is the same as
/// ``(update r) ((update r) acc)`` (note that the update function now becomes a
/// partial application), then use the update-multi-repeat conversion lemma to
/// get the original specification of poly1305.

inline_for_extraction noextract
let block = (block: S.seq uint8 { S.length block = Spec.Poly1305.size_block })

inline_for_extraction noextract
let update_ (acc, r) (block: block) =
  Spec.Poly1305.poly1305_update1 r Spec.Poly1305.size_block block acc, r

/// Same as [update_], but with the input not necessarily a full block (can be smaller)
inline_for_extraction noextract
```

```fstar
let poly1305 (fs : field_spec) : I.block unit =
  I.Block
    I.Runtime

    (stateful_poly1305_ctx fs) (* state *)
    poly1305_key (* key *)
    unit

    (fun () -> 0xffffffffUL) (* max_input_len *)
    (fun () () -> 16) (* output_len *)
    (fun () -> 16ul) (* block_len *)

    (* blocks_state_len *)
    (fun () ->
      match fs with
      | M32 -> 16ul // block_length
      | M128 -> 32ul // 2 * block_length
      | M256 -> 64ul) // 4 * block_length
    (fun () -> 0ul) (* init_input_len *)

    (fun () _k -> S.empty) (* init_input_s *)
    (fun () -> Spec.Poly1305.poly1305_init) (* init_s *)
    (fun () acc prevlen data -> update_multi acc data) (* update_multi_s *)
    (fun () x _ y -> update_last x y) (* update_last_s *)
    (fun () k s () -> finish_ k s) (* finish_s *)

    (fun () k s () -> spec k s) (* spec_s *)

    (* update_multi_zero *)
    (fun () acc prevlen -> Lib.UpdateMulti.update_multi_zero Spec.Poly1305.size_block update_ acc)

    (* update_multi_associative *)
    (fun () acc prevlen1 prevlen2 input1 input2 ->
      Lib.UpdateMulti.update_multi_associative Spec.Poly1305.size_block update_
                                               acc input1 input2)

    (* spec_is_incremental *)
    (fun () key input () ->
      let input1 = S.append S.empty input in
      assert (S.equal input1 input);
      poly_is_incremental_lazy key input)

    (* index_of_state *)
    (fun _ _ _ -> ())

    (* init *)
    (fun _ k _ s ->
      match fs with
      | M32 -> Hacl.Poly1305_32.poly1305_init s k
      | M128 -> Hacl.Poly1305_128.poly1305_init s k
      | M256 -> Hacl.Poly1305_256.poly1305_init s k)
```

```fstar
// Hacl.Streaming.Poly1305_32 / _128 / _256 wrappers
let state_t = F.state_s (poly1305 M32) () (t M32) (poly1305_key.I.s ())
let alloca = F.alloca (poly1305 M32) () (t M32) (poly1305_key.I.s ())
let malloc = F.malloc (poly1305 M32) () (t M32) (poly1305_key.I.s ())
let reset = F.reset (poly1305 M32) (G.hide ()) (t M32) (poly1305_key.I.s ())
let update = F.update (poly1305 M32) (G.hide ()) (t M32) (poly1305_key.I.s ())
let digest = F.digest (poly1305 M32) () (t M32) (poly1305_key.I.s ())
let free = F.free (poly1305 M32) (G.hide ()) (t M32) (poly1305_key.I.s ())
val mac: poly1305_mac_st M32
// same shape for M128 and M256
```

`poly1305` uses `I.Runtime` key management because finish needs the runtime key.
Its `spec_s` is `Spec.Poly1305.poly1305_mac`, output length 16, block length 16,
maximum input `0xffffffffUL`.

EverCrypt one-shot (`providers/evercrypt/EverCrypt.Poly1305.fsti:14-25`):

```fstar
val mac: output:B.buffer UInt8.t { B.length output = 16 } ->
  input:B.buffer UInt8.t ->
  input_len:U32.t { U32.v input_len = B.length input /\ U32.v input_len + 16 <= UInt.max_int 32 } ->
  key:B.buffer UInt8.t { B.length key = 32 } ->
  Stack unit
    (requires fun h ->
      B.live h input /\ B.live h output /\ B.live h key /\
      B.disjoint output input /\ B.disjoint output key)
    (ensures fun h0 _ h1 ->
      B.(modifies (loc_buffer output) h0 h1 /\ (
      B.as_seq h1 output ==
        BF.of_bytes (Spec.Poly1305.poly1305_mac
```

## 6. EverCrypt.Hash and Incremental

Core agile state (`providers/evercrypt/EverCrypt.Hash.fsti:73-362`):

```fstar
val state_s: alg -> Type0

// pointer to abstract implementation state
let state alg = B.pointer (state_s alg)

// abstract freeable (deep) predicate; only needed for create/free pairs
inline_for_extraction noextract
val freeable_s: #(a: alg) -> state_s a -> Type0

inline_for_extraction noextract
let freeable (#a: alg) (h: HS.mem) (p: state a) =
  B.freeable p /\ freeable_s (B.deref h p)

// NS: note that the state is the first argument to the invariant so that we can
// do partial applications in pre- and post-conditions
val footprint_s: #a:alg -> state_s a -> GTot M.loc
let footprint (#a:alg) (s: state a) (m: HS.mem) =
  M.(loc_union (loc_addr_of_buffer s) (footprint_s (B.deref m s)))

```

```fstar
val invariant_s: (#a:alg) -> state_s a -> HS.mem -> Type0

inline_for_extraction noextract
let invariant (#a:alg) (s: state a) (m: HS.mem) =
  B.live m s /\
  M.(loc_disjoint (loc_addr_of_buffer s) (footprint_s (B.deref m s))) /\
  invariant_s (B.get m s 0) m

//18-07-06 as_acc a better name? not really a representation
val repr: #a:alg ->
  s:state a -> h:HS.mem -> GTot (words_state a)

val alg_of_state: a:e_alg -> (
  let a = G.reveal a in
  s: state a -> Stack alg
  (fun h0 -> invariant s h0)
  (fun h0 a' h1 -> h0 == h1 /\ a' == a))

val fresh_is_disjoint: l1:M.loc -> l2:M.loc -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (B.fresh_loc l1 h0 h1 /\ l2 `B.loc_in` h0))
  (ensures (M.loc_disjoint l1 l2))

// TR: this lemma is necessary to prove that the footprint is disjoint
// from any fresh memory location.

val invariant_loc_in_footprint
  (#a: alg)
  (s: state a)
  (m: HS.mem)
: Lemma
  (requires (invariant s m))
  (ensures (B.loc_in (footprint s m) m))
  [SMTPat (invariant s m)]

// TR: frame_invariant, just like all lemmas eliminating `modifies`
// clauses, should have `modifies_inert` as a precondition instead of
// `modifies`, in order to use it in all cases where a modifies clause
// is produced but should not be composed with `modifies_trans` for
// pattern reasons (e.g. push_frame, pop_frame)

// 18-07-12 why not bundling the next two lemmas?
val frame_invariant: #a:alg -> l:M.loc -> s:state a -> h0:HS.mem -> h1:HS.mem -> Lemma
  (requires (
    invariant s h0 /\
    M.loc_disjoint l (footprint s h0) /\
    M.modifies l h0 h1))
  (ensures (
    invariant s h1 /\
    repr s h0 == repr s h1))

let frame_invariant_implies_footprint_preservation
  (#a: alg)
  (l: M.loc)
  (s: state a)
  (h0 h1: HS.mem): Lemma
```

```fstar
val alloca: a:alg -> StackInline (state a)
  (requires (fun _ -> True))
  (ensures (fun h0 s h1 ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s h1) h0 h1 /\
    M.(loc_includes (loc_region_only true (HS.get_tip h1)) (footprint s h1))))

(** @type: true
*)
val create_in: a:alg -> r:HS.rid -> ST (option (state a))
  (requires (fun _ ->
    HyperStack.ST.is_eternal_region r))
  (ensures (fun h0 s h1 ->
    match s with
    | None -> M.(modifies loc_none h0 h1)
    | Some s ->
    invariant s h1 /\
    M.(modifies loc_none h0 h1) /\
    B.fresh_loc (footprint s h1) h0 h1 /\
    M.(loc_includes (loc_region_only true r) (footprint s h1)) /\
    freeable h1 s))


(** @type: true
*)
val init: #a:e_alg -> (
  let a = Ghost.reveal a in
  s: state a -> Stack unit
  (requires invariant s)
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.init a /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1))

val update_multi_256: Hacl.Hash.Definitions.update_multi_st (|SHA2_256, ()|)

inline_for_extraction noextract
val update_multi_224: Hacl.Hash.Definitions.update_multi_st (|SHA2_224, ()|)

inline_for_extraction noextract
let ev_of_uint64 a (prevlen: UInt64.t { UInt64.v prevlen % block_length a = 0 }): Spec.Hash.Definitions.extra_state a =
  (if is_blake a then UInt64.v prevlen else ())

/// The ``update_multi`` method
// Note that we pass the data length in bytes (rather than blocks).
(** @type: true
*)
val update_multi:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a ->
  prevlen : uint64_t { UInt64.v prevlen % block_length a = 0 } ->
  blocks:B.buffer Lib.IntTypes.uint8 { B.length blocks % block_length a = 0 } ->
  len: UInt32.t { v len = B.length blocks } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 blocks /\
    Spec.Agile.Hash.update_multi_pre a (ev_of_uint64 a prevlen) (B.as_seq h0 blocks) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer blocks)))
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    invariant s h1 /\
    repr s h1 == Spec.Agile.Hash.update_multi a (repr s h0)
      (ev_of_uint64 a prevlen) (B.as_seq h0 blocks) /\
    preserves_freeable s h0 h1))

inline_for_extraction noextract
let prev_len_of_uint64 a (prevlen: UInt64.t { UInt64.v prevlen % block_length a = 0 }): Spec.Hash.Incremental.prev_length_t a =
  (if is_keccak a then () else UInt64.v prevlen)

/// The ``update_last`` method with support for blake2
// 18-03-05 note the *new* length-passing convention!
// 18-03-03 it is best to let the caller keep track of lengths.
// 18-03-03 the last block is *never* complete so there is room for the 1st byte of padding.
// 18-10-10 using uint64 for the length as the is the only thing that TLS needs
//   and also saves the need for a (painful) indexed type
// 18-10-15 a crucial bit is that this function reveals that last @| padding is a multiple of the
//   block size; indeed, any caller will want to know this in order to reason
//   about that sequence concatenation
(** @type: true
*)
val update_last:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a ->
  prev_len:uint64_t ->
  last:B.buffer Lib.IntTypes.uint8 { B.length last <= block_length a } ->
  last_len:uint32_t {
    v last_len = B.length last /\
    (v prev_len + v last_len) `less_than_max_input_length` a /\
    v prev_len % block_length a = 0 } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 last /\
    Spec.Agile.Hash.update_multi_pre a (ev_of_uint64 a prev_len) (B.as_seq h0 last) /\
    M.(loc_disjoint (footprint s h0) (loc_buffer last)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    repr s h1 ==
      Spec.Hash.Incremental.update_last a (repr s h0) (prev_len_of_uint64 a prev_len)
                                             (B.as_seq h0 last) /\
    M.(modifies (footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    preserves_freeable s h0 h1))

(** @type: true
*)
val finish:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a ->
  dst:B.buffer Lib.IntTypes.uint8 { B.length dst = hash_length a } ->
  Stack unit
  (requires fun h0 ->
    invariant s h0 /\
    B.live h0 dst /\
    M.(loc_disjoint (footprint s h0) (loc_buffer dst)))
  (ensures fun h0 _ h1 ->
    invariant s h1 /\
    M.(modifies (loc_buffer dst `loc_union` footprint s h0) h0 h1) /\
    footprint s h0 == footprint s h1 /\
    (* The 0UL value is dummy: it is actually useless *)
    B.as_seq h1 dst == Spec.Agile.Hash.finish a (repr s h0) () /\
    preserves_freeable s h0 h1))

(** @type: true
*)
val free_:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a -> ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))

// Avoids C-level collisions with the stdlib free.
// Not clear why we need to repeat the type annotation.
inline_for_extraction noextract
let free: #a:e_alg -> (
  let a = Ghost.reveal a in
  s:state a -> ST unit
  (requires fun h0 ->
    freeable h0 s /\
    invariant s h0)
  (ensures fun h0 _ h1 ->
    M.(modifies (footprint s h0) h0 h1)))
 = free_

(** @type: true
*)
val copy:
  #a:e_alg -> (
  let a = Ghost.reveal a in
  s_src:state a ->
  s_dst:state a ->
  Stack unit
    (requires (fun h0 ->
      invariant s_src h0 /\
      invariant s_dst h0 /\
      B.(loc_disjoint (footprint s_src h0) (footprint s_dst h0))))
    (ensures fun h0 _ h1 ->
      M.(modifies (footprint s_dst h0) h0 h1) /\
      footprint s_dst h0 == footprint s_dst h1 /\
      preserves_freeable s_dst h0 h1 /\
      invariant s_dst h1 /\
      repr s_dst h1 == repr s_src h0))
```

Incremental wrapper (`providers/evercrypt/fst/EverCrypt.Hash.Incremental.fst:100-346`):

```fstar
let evercrypt_hash : block Hash.alg =
  Block
    Erased
    agile_state
    (stateful_unused Hash.alg)

    unit
    Hacl.Hash.Definitions.max_input_len64
    (fun a () -> Spec.Hash.Definitions.hash_length a)
    block_len
    block_len // No vectorization
    (fun _ -> 0ul)

    (fun _ _ -> S.empty)
    (fun a _ -> Spec.Agile.Hash.init a)
    (fun a s prevlen input ->
      let prevlen = extra_state_of_nat a prevlen in
      Spec.Agile.Hash.update_multi a s prevlen input)
    (fun a s prevlen input ->
      let prevlen = prev_length_of_nat a prevlen in
      Spec.Hash.Incremental.update_last a s prevlen input)
    (fun a _ s () -> Spec.Agile.Hash.finish a s ())

    (fun a _ s () -> Spec.Agile.Hash.hash a s)

    (fun a s prevlen ->
      if is_blake a then
        Spec.Hash.Lemmas.update_multi_zero_blake a prevlen s
      else
        Spec.Hash.Lemmas.update_multi_zero a s)
    (* update_multi_associative *)
    (fun a s prevlen1 prevlen2 input1 input2 ->
       if is_blake a then
         Spec.Hash.Lemmas.update_multi_associative_blake a s prevlen1 prevlen2 input1 input2
       else
         Spec.Hash.Lemmas.update_multi_associative a s input1 input2)
    (* spec_is_incremental *)
    (fun a _ input () ->
        let input1 = S.append S.empty input in
        assert (S.equal input1 input);
        Spec.Hash.Incremental.hash_is_hash_incremental' a input ())

    (fun a s _ -> EverCrypt.Hash.alg_of_state a s)
    (fun i _ _ -> EverCrypt.Hash.init #i)
    (fun i s prevlen blocks len -> EverCrypt.Hash.update_multi #i s prevlen blocks len)
    (fun i s prevlen last last_len ->
       EverCrypt.Hash.update_last #i s prevlen last last_len)
    (fun i _ s dst _ -> EverCrypt.Hash.finish #i s dst)

#pop-options

let state_t =
  F.state_s evercrypt_hash SHA2_256 ((agile_state).s SHA2_256) (G.erased unit)

// Public API (streaming)
// ----------------------

[@@ Comment
"Allocate initial state for the agile hash. The argument `a` stands for the
choice of algorithm (see Hacl_Spec.h). This API will automatically pick the most
efficient implementation, provided you have called EverCrypt_AutoConfig2_init()
before. The state is to be freed by calling `free`."]
let malloc a = F.malloc evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit) ()

[@@ Comment
"Reset an existing state to the initial hash state with empty data."]
let reset (a: G.erased Hash.alg) = F.reset evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

[@@ Comment
"Feed an arbitrary amount of data into the hash. This function returns
EverCrypt_Error_Success for success, or EverCrypt_Error_MaximumLengthExceeded if
the combined length of all of the data passed to `update` (since the last call
to `init`) exceeds 2^61-1 bytes or 2^64-1 bytes, depending on the choice of
algorithm. Both limits are unlikely to be attained in practice."]
let update (i: G.erased Hash.alg)
  (state:F.state evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit))
  (chunk: B.buffer uint8)
  (chunk_len: UInt32.t):
  Stack EverCrypt.Error.error_code
    (requires fun h0 -> F.update_pre evercrypt_hash i state chunk chunk_len h0)
    (ensures fun h0 e h1 ->
      match e with
      | EverCrypt.Error.Success ->
          S.length (F.seen evercrypt_hash i h0 state) + U32.v chunk_len <= U64.v (evercrypt_hash.max_input_len i) /\
          F.update_post evercrypt_hash i state chunk chunk_len h0 h1
      | EverCrypt.Error.MaximumLengthExceeded ->
          h0 == h1 /\
          not (S.length (F.seen evercrypt_hash i h0 state) + U32.v chunk_len <= U64.v (evercrypt_hash.max_input_len i))
      | _ -> False)
=
  match F.update evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit) state chunk chunk_len with
  | Hacl.Streaming.Types.Success -> EverCrypt.Error.Success
  | Hacl.Streaming.Types.MaximumLengthExceeded -> EverCrypt.Error.MaximumLengthExceeded

inline_for_extraction noextract
let digest_st a = F.digest_st evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

/// The wrapper pattern, to ensure that the stack-allocated state is properly
/// monomorphized.
private
let digest_md5: digest_st MD5 = F.digest evercrypt_hash MD5 (EverCrypt.Hash.state MD5) (G.erased unit)
private
let digest_sha1: digest_st SHA1 = F.digest evercrypt_hash SHA1 (EverCrypt.Hash.state SHA1) (G.erased unit)
private
let digest_sha224: digest_st SHA2_224 = F.digest evercrypt_hash SHA2_224 (EverCrypt.Hash.state SHA2_224) (G.erased unit)
private
let digest_sha256: digest_st SHA2_256 = F.digest evercrypt_hash SHA2_256 (EverCrypt.Hash.state SHA2_256) (G.erased unit)
private
let digest_sha3_224: digest_st SHA3_224 = F.digest evercrypt_hash SHA3_224 (EverCrypt.Hash.state SHA3_224) (G.erased unit)
private
let digest_sha3_256: digest_st SHA3_256 = F.digest evercrypt_hash SHA3_256 (EverCrypt.Hash.state SHA3_256) (G.erased unit)
private
let digest_sha3_384: digest_st SHA3_384 = F.digest evercrypt_hash SHA3_384 (EverCrypt.Hash.state SHA3_384) (G.erased unit)
private
let digest_sha3_512: digest_st SHA3_512 = F.digest evercrypt_hash SHA3_512 (EverCrypt.Hash.state SHA3_512) (G.erased unit)
private
let digest_sha384: digest_st SHA2_384 = F.digest evercrypt_hash SHA2_384 (EverCrypt.Hash.state SHA2_384) (G.erased unit)
private
let digest_sha512: digest_st SHA2_512 = F.digest evercrypt_hash SHA2_512 (EverCrypt.Hash.state SHA2_512) (G.erased unit)
private
let digest_blake2s: digest_st Blake2S = F.digest evercrypt_hash Blake2S (EverCrypt.Hash.state Blake2S) (G.erased unit)
private
let digest_blake2b: digest_st Blake2B = F.digest evercrypt_hash Blake2B (EverCrypt.Hash.state Blake2B) (G.erased unit)

[@@ Comment
"Perform a run-time test to determine which algorithm was chosen for the given piece of state."]
let alg_of_state (a: G.erased Hash.alg) = F.index_of_state evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

[@@ Comment
"Write the resulting hash into `output`, an array whose length is
algorithm-specific. You can use the macros defined earlier in this file to
allocate a destination buffer of the right length. The state remains valid after
a call to `digest`, meaning the user may feed more data into the hash via
`update`. (The finish function operates on an internal copy of the state and
therefore does not invalidate the client-held state.)"]
val digest: a:G.erased Hash.alg -> digest_st a
let digest a state output l =
  let a = alg_of_state a state in
  match a with
  | MD5 -> digest_md5 state output l
  | SHA1 -> digest_sha1 state output l
  | SHA2_224 -> digest_sha224 state output l
  | SHA2_256 -> digest_sha256 state output l
  | SHA2_384 -> digest_sha384 state output l
  | SHA2_512 -> digest_sha512 state output l
  | SHA3_224 -> digest_sha3_224 state output l
  | SHA3_256 -> digest_sha3_256 state output l
  | SHA3_384 -> digest_sha3_384 state output l
  | SHA3_512 -> digest_sha3_512 state output l
  | Blake2S -> digest_blake2s state output l
  | Blake2B -> digest_blake2b state output l

[@@ Comment
"Free a state previously allocated with `create_in`."]
let free (i: G.erased Hash.alg) = F.free evercrypt_hash i (EverCrypt.Hash.state i) (G.erased unit)

// Private API (one-shot, multiplexing)
// ------------------------------------

private
val hash_256: Hacl.Hash.Definitions.hash_st SHA2_256

// A full one-shot hash that relies on vale at each multiplexing point
let hash_256 output input input_len =
  let open EverCrypt.Hash in
  // TODO: This function now only exists for SHA1 and MD5
  Hacl.Hash.MD.mk_hash SHA2_256 Hacl.Hash.SHA2.alloca_256 update_multi_256
    Hacl.Hash.SHA2.update_last_256 Hacl.Hash.SHA2.finish_256 output input input_len

private
val hash_224: Hacl.Hash.Definitions.hash_st SHA2_224

let hash_224 output input input_len =
  let open EverCrypt.Hash in
  Hacl.Hash.MD.mk_hash SHA2_224 Hacl.Hash.SHA2.alloca_224 update_multi_224
    Hacl.Hash.SHA2.update_last_224 Hacl.Hash.SHA2.finish_224 output input input_len

// Public API (one-shot, agile and multiplexing)
// ---------------------------------------------

// NOTE: this function goes through all the Hacl.Hash.* wrappers which export
// the correct agile low-level type, and thus does not need to be aware of the
// implementation of Spec.Agile.Hash (no friend-ing).
//
// ALSO: for some reason, this function was historically exported with an order
// of arguments different from Hacl.Hash.Definitions.hash_st a. Would be worth
// fixing at some point.

[@@ Comment
"Hash `input`, of len `input_len`, into `output`, an array whose length is determined by
your choice of algorithm `a` (see Hacl_Spec.h). You can use the macros defined
earlier in this file to allocate a destination buffer of the right length. This
API will automatically pick the most efficient implementation, provided you have
called EverCrypt_AutoConfig2_init() before. "]
val hash:
  a:Hash.alg ->
  output:B.buffer Lib.IntTypes.uint8 {B.length output = hash_length a} ->
  input:B.buffer Lib.IntTypes.uint8 ->
  input_len:FStar.UInt32.t {B.length input = FStar.UInt32.v input_len /\ FStar.UInt32.v input_len `less_than_max_input_length` a} ->
  Stack unit
  (requires fun h0 ->
    B.live h0 output /\
    B.live h0 input /\
    B.(loc_disjoint (loc_buffer input) (loc_buffer output)))
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer output) h0 h1) /\
    B.as_seq h1 output == Spec.Agile.Hash.hash a (B.as_seq h0 input))
let hash a output input input_len =
  match a with
  | MD5 -> Hacl.Hash.MD5.hash_oneshot output input input_len
  | SHA1 -> Hacl.Hash.SHA1.hash_oneshot output input input_len
  | SHA2_224 -> hash_224 output input input_len
  | SHA2_256 -> hash_256 output input input_len
  | SHA2_384 -> Hacl.Streaming.SHA2.hash_384 output input input_len
  | SHA2_512 -> Hacl.Streaming.SHA2.hash_512 output input input_len
  | SHA3_224 -> Hacl.Hash.SHA3.hash SHA3_224 output input input_len
  | SHA3_256 -> Hacl.Hash.SHA3.hash SHA3_256 output input input_len
  | SHA3_384 -> Hacl.Hash.SHA3.hash SHA3_384 output input input_len
  | SHA3_512 -> Hacl.Hash.SHA3.hash SHA3_512 output input input_len
  | Blake2S ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec128 then
        let vec128 = EverCrypt.AutoConfig2.has_vec128 () in
        if vec128 then
          Hacl.Hash.Blake2s_128.hash output input input_len
        else
          Hacl.Hash.Blake2s_32.hash output input input_len
      else
        Hacl.Hash.Blake2s_32.hash output input input_len
  | Blake2B ->
      if EverCrypt.TargetConfig.hacl_can_compile_vec256 then
        let vec256 = EverCrypt.AutoConfig2.has_vec256 () in
        if vec256 then
          Hacl.Hash.Blake2b_256.hash output input input_len
        else
          Hacl.Hash.Blake2b_32.hash output input input_len
      else
        Hacl.Hash.Blake2b_32.hash output input input_len

// Public API (verified clients)
// -----------------------------

/// Finally, a few helpers predicates to make things easier for clients...
inline_for_extraction noextract
let state (a: Hash.alg) = F.state evercrypt_hash a (EverCrypt.Hash.state a) (G.erased unit)

inline_for_extraction noextract
let hashed #a (h: HS.mem) (s: state a) =
```

`EverCrypt.Hash` uses an abstract `state_s`, `state`, `invariant`, `footprint`,
`repr`, `alg_of_state`, and frame lemmas. `alloca` is `inline_for_extraction
noextract`; `create_in` is heap `ST` and may return `None`. The incremental
module instantiates the functor with `km = Erased`, unused key, `init_input_len
= 0`, and `spec_s = Spec.Agile.Hash.hash`. `digest` dispatches to monomorphized
wrappers. BLAKE2 fast paths are guarded by static `EverCrypt.TargetConfig` flags
and runtime `EverCrypt.AutoConfig2.has_vec128/has_vec256`; call `AutoConfig2.init`
in extracted programs before relying on CPU auto-detection.

## 7. Worked verified-client sketch

Source: `providers/test/Test.Hash.fst:13-75`.

```fstar
open Spec.Hash.Definitions
open Spec.Hash.Lemmas
open Lib.IntTypes

open FStar.HyperStack.ST


#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"
let test_incremental_api (): ST unit
  (requires fun _ -> True)
  (ensures fun h0 _ h1 -> True) =
  // Note: this function cannot be in the Stack effect because it performs some
  // allocations (even though it frees them afterwards).
  let h00 = ST.get () in
  push_frame ();
  let b1 = B.alloca_of_list [ u8 0x00; u8 0x01; u8 0x02; u8 0x04 ] in
  let b2 = B.alloca_of_list [ u8 0x05; u8 0x06; u8 0x07; u8 0x08 ] in

  let st = HI.malloc SHA2_256 HyperStack.root in
  if B.is_null st then begin
    pop_frame ();
    LowStar.Failure.failwith "OUT OF MEMORY"
  end else
    HI.reset (G.hide SHA2_256) st ();
    let h0 = ST.get () in
    assert B.(loc_disjoint (S.footprint HI.evercrypt_hash SHA2_256 h0 st) (loc_buffer b1));
    assert (S.seen HI.evercrypt_hash SHA2_256 h0 st `Seq.equal` Seq.empty);

    assert_norm (4 < pow2 61);
    let EverCrypt.Error.Success = HI.update (G.hide SHA2_256) st b1 4ul in
    let h1 = ST.get () in
    assert (HI.hashed h1 st `Seq.equal` (Seq.append Seq.empty (B.as_seq h0 b1)));
    Seq.append_empty_l (B.as_seq h0 b1);
    assert (HI.hashed h1 st `Seq.equal` (B.as_seq h0 b1));

    assert (Seq.length (Ghost.reveal (Ghost.hide (B.as_seq h0 b1))) = 4);
    assert_norm (8 < pow2 61);
    let EverCrypt.Error.Success = HI.update (G.hide SHA2_256) st b2 4ul in
    let h2 = ST.get () in
    assert (HI.hashed h2 st `Seq.equal` (Seq.append (B.as_seq h0 b1) (B.as_seq h0 b2)));

    // An example of how to call the hash preservation lemma...
    let dst = B.alloca (u8 0) 32ul in
    let h3 = ST.get () in
    assert B.(fresh_loc (loc_buffer dst) h2 h3);
    B.modifies_only_not_unused_in B.loc_none h2 h3;
    assert B.(modifies (loc_none) h2 h3);
    // Auto-framing no longer works OH NOES
    S.frame_invariant HI.evercrypt_hash SHA2_256 B.loc_none st h2 h3;
    assert B.(loc_disjoint (loc_buffer dst) (S.footprint HI.evercrypt_hash SHA2_256 h3 st));
    HI.digest (G.hide SHA2_256) st dst ();

    let h4 = ST.get () in
    assert (Seq.equal (B.as_seq h4 dst)
      (Spec.Agile.Hash.hash SHA2_256 (Seq.append (B.as_seq h0 b1) (B.as_seq h0 b2))));

    HI.free (G.hide SHA2_256) st;
    pop_frame ();
    let h5 = ST.get () in
    ()

#set-options "--fuel 0 --ifuel 0"
let main (): St unit =
```

The client allocates buffers, `malloc`s and `reset`s a SHA2-256 state, proves
input/state disjointness before `update`, uses successful update postconditions
to accumulate `HI.hashed` (`F.seen`), frames the newly allocated output with
`S.frame_invariant`, calls `digest`, obtains equality with
`Spec.Agile.Hash.hash SHA2_256`, then `free`s the state.

## 8. Notes for reimplementers

Preserve: abstract state, explicit ownership/footprint, invariants, frame
preservation for disjoint memory, ghost `seen` as the concatenation of successful
updates, exact spec equality on digest/one-shot output, failure-without-state
change for length errors, key-retention mode, and CPU feature guards. F\*-specific
plumbing (`SMTPat`, `G.erased`, `inline_for_extraction noextract`, specialized
`StackInline` wrappers, separate SMT framing lemmas) may be expressed
differently, but it exists to let clients prove the same semantic facts.
