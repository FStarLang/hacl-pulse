# F* pure specifications in HACL*/EverCrypt
Cross-refs: `design/README.md`, `design/fstar-api.md`, `design/fstar-api-hashes-macs.md`, `design/fstar-api-aead-ciphers.md`, `design/fstar-api-curves-bignum.md`, `design/fstar-client-guide.md`, `design/implementation.md`, `design/surprises.md`.
## 1. Role of the spec layer
The `specs/` layer is pure, total, executable F* over `Lib.Sequence` and mathematical integers, with wrappers from `Lib.IntTypes`. It is the correctness oracle: every stateful Low*/EverCrypt postcondition ultimately refers to these functions. Proof-only artifacts are erased or specialized at extraction (`noextract`, `inline_for_extraction`, `[@must_erase_for_extraction]`). Verified clients state their own theorems in spec-level terms, so this is a **public API**, not an implementation detail.
## 2. Vocabulary for clients
### Sequences and bytes
`lib/Lib.Sequence.fsti:13-25`
```fstar
let seq (a:Type0) = Seq.seq a

(** Length of a Sequence *)
let length (#a:Type0) (s:seq a) : nat = Seq.length s

/// Fixed length Sequences

(* This is the type of bounded sequences.
   Use this as much as possible.
   It adds additional length checks that you'd have to prove in the implementation otherwise *)

(** Definition of a fixed-length Sequence *)
let lseq (a:Type0) (len:size_nat) = s:seq a{Seq.length s == len}
```
`lib/Lib.ByteSequence.fsti:9-21`
```fstar

/// Definition of byte-based sequences

unfold inline_for_extraction
type bytes_l (l:secrecy_level) = seq (uint_t U8 l)

unfold inline_for_extraction
type lbytes_l (l:secrecy_level) (len:size_nat) = lseq (uint_t U8 l) len

unfold inline_for_extraction let bytes = bytes_l SEC
unfold inline_for_extraction let lbytes (len:size_nat) = lbytes_l SEC len
unfold inline_for_extraction let pub_bytes = bytes_l PUB
unfold inline_for_extraction let pub_lbytes (len:size_nat) = lbytes_l PUB len
```
### Secret/public integers
`lib/Lib.IntTypes.fsti:14-30`
```fstar
///
/// Definition of machine integer base types
///

type inttype =
  | U1 | U8 | U16 | U32 | U64 | U128 | S8 | S16 | S32 | S64 | S128

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let unsigned = function
  | U1 | U8 | U16 | U32 | U64 | U128 -> true
  | _ -> false

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
```
`lib/Lib.IntTypes.fsti:91-151`
```fstar
type range_t (t:inttype) = x:int{range x t}

///
/// PUBLIC Machine Integers
///

inline_for_extraction
let pub_int_t = function
  | U1   -> n:UInt8.t{UInt8.v n < 2}
  | U8   -> UInt8.t
  | U16  -> UInt16.t
  | U32  -> UInt32.t
  | U64  -> UInt64.t
  | U128 -> UInt128.t
  | S8   -> Int8.t
  | S16  -> Int16.t
  | S32  -> Int32.t
  | S64  -> Int64.t
  | S128 -> Int128.t


[@(strict_on_arguments [0])]
unfold
let pub_int_v #t (x:pub_int_t t) : range_t t =
  match t with
  | U1   -> UInt8.v x
  | U8   -> UInt8.v x
  | U16  -> UInt16.v x
  | U32  -> UInt32.v x
  | U64  -> UInt64.v x
  | U128 -> UInt128.v x
  | S8   -> Int8.v x
  | S16  -> Int16.v x
  | S32  -> Int32.v x
  | S64  -> Int64.v x
  | S128 -> Int128.v x

///
/// SECRET Machine Integers
///

type secrecy_level =
  | SEC
  | PUB

inline_for_extraction
val sec_int_t: inttype -> Type0

val sec_int_v: #t:inttype -> sec_int_t t -> range_t t

///
/// GENERIC Machine Integers
///

inline_for_extraction
let int_t (t:inttype) (l:secrecy_level) =
  match l with
  | PUB -> pub_int_t t
  | SEC -> sec_int_t t

[@(strict_on_arguments [1])]
```
`lib/Lib.IntTypes.fsti:153-216`
```fstar
  match l with
  | PUB -> pub_int_v #t u
  | SEC -> sec_int_v #t u

unfold
let uint_t (t:inttype{unsigned t}) (l:secrecy_level) = int_t t l

unfold
let sint_t (t:inttype{signed t}) (l:secrecy_level) = int_t t l

unfold
let uint_v #t #l (u:uint_t t l) = v u

unfold
let sint_v #t #l (u:sint_t t l) = v u

unfold
type uint1 = uint_t U1 SEC

unfold
type uint8 = uint_t U8 SEC

unfold
type int8 = sint_t S8 SEC

unfold
type uint16 = uint_t U16 SEC

unfold
type int16 = sint_t S16 SEC

unfold
type uint32 = uint_t U32 SEC

unfold
type int32 = sint_t S32 SEC

unfold
type uint64 = uint_t U64 SEC

unfold
type int64 = sint_t S64 SEC

unfold
type uint128 = uint_t U128 SEC

unfold
type int128 = sint_t S128 SEC

unfold
type bit_t = uint_t U1 PUB

unfold
type byte_t = uint_t U8 PUB

unfold
type size_t = uint_t U32 PUB

// 2019.7.19: Used only by experimental Blake2b; remove?
unfold
type size128_t = uint_t U128 PUB

unfold
type pub_uint8 = uint_t U8 PUB
```
### Loop and update combinators
| Source | Name | Exact declaration |
|---|---|---|
| `lib/Lib.LoopCombinators.fsti:158` | `repeati:` | `val repeati: #a:Type -> n:nat -> f:(i:nat{i < n} -> a -> a) -> acc0:a -> a` |
| `lib/Lib.LoopCombinators.fsti:195` | `repeat:` | `val repeat: #a:Type -> n:nat -> f:(a -> a) -> acc0:a -> a` |
| `lib/Lib.Sequence.fsti:256` | `repeati_blocks:` | `val repeati_blocks: #a:Type0 -> #b:Type0 -> blocksize:size_pos -> inp:seq a -> f:(i:nat{i < length inp / blocksize} -> lseq a blocksize -> b -> b) -> l:(i:nat{i == length inp / blocksize} -> len:size_nat{len == length inp % blocksize} -> s:lseq a len -> b -> b) -> init:b -> Tot b` |
| `lib/Lib.Sequence.fsti:280` | `repeat_blocks:` | `val repeat_blocks: #a:Type0 -> #b:Type0 -> #c:Type0 -> blocksize:size_pos -> inp:seq a -> f:(lseq a blocksize -> b -> b) -> l:(len:nat{len < blocksize} -> s:lseq a len -> b -> c) -> init:b -> Tot c` |
| `lib/Lib.Sequence.fsti:309` | `repeat_blocks_multi:` | `val repeat_blocks_multi: #a:Type0 -> #b:Type0 -> blocksize:size_pos -> inp:seq a{length inp % blocksize = 0} -> f:(lseq a blocksize -> b -> b) -> init:b -> Tot b` |
| `lib/Lib.UpdateMulti.fst:256` | `update_t` | `let update_t a block_length =` |
| `lib/Lib.UpdateMulti.fst:259` | `rec` | `let rec mk_update_multi #a (block_length: pos) (update: update_t a block_length) (acc: a) (blocks: S.seq uint8): Pure a (requires S.length blocks % block_length = 0) (ensures fun _ -> True) (decreases (S.length blocks)) = if S.length blocks = 0 then acc else let block, rem = split_block block_length blocks 1 in let acc = update acc block in mk_update_multi block_length update acc rem` |
| `lib/Lib.UpdateMulti.fst:276` | `update_full` | `let update_full #a (block_length:pos) (update: a -> (s:S.seq uint8 { S.length s = block_length }) -> a) (update_last: a -> (s:S.seq uint8 { S.length s < block_length }) -> a) (acc: a) (input: S.seq uint8) = // let n_blocks = S.length input / block_length in // let rem = S.length input % block_length in // let blocks, rest = S.split input (n_blocks * block_length) in let blocks, rest = split_at_last block_length input in // assert (S.length rest = S.length input % block_length); // Math.Lemmas.multiple_modulo_lemma n_blocks block_length; // assert (S.length blocks % block_length = 0); // assert (S.length rest < block_length); update_last (mk_update_multi block_length update acc blocks) rest` |
| `lib/Lib.UpdateMulti.fst:297` | `update_full_lazy` | `let update_full_lazy #a (block_length:pos) (update: a -> (s:S.seq uint8 { S.length s = block_length }) -> a) (update_last: a -> (s:S.seq uint8 { S.length s <= block_length }) -> a) (acc: a) (input: S.seq uint8) = // let n_blocks = S.length input / block_length in // let rem = S.length input % block_length in // let n_blocks, rem = if rem = 0 && n_blocks > 0 then n_blocks - 1, block_length // else n_blocks, rem in // let blocks, rest = S.split input (n_blocks * block_length) in let blocks, rest = split_at_last_lazy block_length input in // assert (S.length rest % block_length = S.length input % block_length); // Math.Lemmas.multiple_modulo_lemma n_blocks block_length; // assert (S.length blocks % block_length = 0); // assert (S.length rest <= block_length); update_last (mk_update_multi block_length update acc blocks) rest` |
## 3. Agile specs in detail
These are the EverCrypt-facing spec APIs. The snippets below are verbatim source for the algorithm-index types, key/state/length functions, main functions, and refinements.
### Hash agility
`specs/Spec.Hash.Definitions.fst:28-70`
```fstar

(** Supported hash algorithms.

  NOTE: this inductive is *append-only* because the constructors generate macro
  definitions that various bindings (OCaml, Rust) have taken a dependency on.
  So, in order to keep the numbering stable, we only append new cases, which is
  why SHA3_224 comes after SHA3_256 (the former was added *after* the latter).
  *)
type hash_alg =
  | SHA2_224
  | SHA2_256
  | SHA2_384
  | SHA2_512
  | SHA1
  | MD5
  | Blake2S
  | Blake2B
  | SHA3_256
  | SHA3_224
  | SHA3_384
  | SHA3_512
  | Shake128
  | Shake256

inline_for_extraction noextract
let is_sha2 = function
  | SHA2_224 | SHA2_256 | SHA2_384 | SHA2_512 -> true
  | _ -> false

inline_for_extraction noextract
let is_keccak = function
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> true
  | _ -> false

inline_for_extraction noextract
let is_shake = function
  | Shake128 | Shake256 -> true
  | _ -> false

inline_for_extraction noextract
let is_blake = function
  | Blake2S | Blake2B -> true
  | _ -> false
```
`specs/Spec.Hash.Definitions.fst:86-100`
```fstar
  | Blake2B -> Spec.Blake2.Blake2B

inline_for_extraction
let to_hash_alg (a : Spec.Blake2.alg) =
  match a with
  | Spec.Blake2.Blake2S -> Blake2S
  | Spec.Blake2.Blake2B -> Blake2B

(** Maximum input data length. *)

(* In bytes. *)

inline_for_extraction
let max_input_length: hash_alg -> option pos = function
  | MD5 | SHA1
```
`specs/Spec.Hash.Definitions.fst:167-302`
```fstar
inline_for_extraction
let word_t: hash_alg -> Tot inttype = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> U32
  | SHA2_384 | SHA2_512 -> U64
  | Blake2S -> U32
  | Blake2B -> U64
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> U64

inline_for_extraction
let row (a:blake_alg) = lseq (uint_t (word_t a) SEC) 4

inline_for_extraction
let word (a: hash_alg) = match a with
  | Blake2S | Blake2B -> row a
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> uint_t (word_t a) SEC

(* In bytes. Should be: bytes_of_int (word_t a) *)
let word_length: hash_alg -> Tot nat = function
  | MD5 | SHA1
  | SHA2_224 | SHA2_256 -> 4
  | SHA2_384 | SHA2_512 -> 8
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> 8
  | Blake2S -> 4
  | Blake2B -> 8

let rate (a: keccak_alg): (rate: size_nat{0 < rate / 8 /\ rate / 8 <= 200}) =
  match a with
  | SHA3_224 -> 1152
  | SHA3_256 -> 1088
  | SHA3_384 -> 832
  | SHA3_512 -> 576
  | Shake128 -> 1344
  | Shake256 -> 1088

(* Number of words for a block size *)
let block_word_length (a: hash_alg) =
  match a with
  | SHA3_224 -> normalize_term (rate SHA3_224 / 8 / 8)
  | SHA3_256 -> normalize_term (rate SHA3_256 / 8 / 8)
  | SHA3_384 -> normalize_term (rate SHA3_384 / 8 / 8)
  | SHA3_512 -> normalize_term (rate SHA3_512 / 8 / 8)
  | Shake128 -> normalize_term (rate Shake128 / 8 / 8)
  | Shake256 -> normalize_term (rate Shake256 / 8 / 8)
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | Blake2S
  | Blake2B -> 16

(* Define the size block in bytes *)

let block_length a: nonzero =
  let open FStar.Mul in
  word_length a * block_word_length a

(* Number of words for intermediate hash, i.e. the working state. *)
inline_for_extraction
let state_word_length a =
  match a with
  | MD5 -> 4
  | SHA1 -> 5
  | Blake2S | Blake2B -> 4
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> 25
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512 -> 8

inline_for_extraction
let extra_state a = match a with
  | Blake2S | Blake2B -> n:nat { n % block_length a = 0 }
  | MD5 | SHA1
  | SHA2_224 | SHA2_256
  | SHA2_384 | SHA2_512
  | SHA3_224 | SHA3_256 | SHA3_384 | SHA3_512 | Shake128 | Shake256 -> unit

(* The working state *)
inline_for_extraction
let words_state a = lseq (word a) (state_word_length a)

(* Number of words for final hash *)
inline_for_extraction
let hash_word_length: a:md_alg -> Tot nat = function
  | MD5 -> 4
  | SHA1 -> 5
  | SHA2_224 -> 7
  | SHA2_256 -> 8
  | SHA2_384 -> 6
  | SHA2_512 -> 8

(* Define the final hash length in bytes *)

let hash_length (a: hash_alg { not (is_shake a) }): Lib.IntTypes.(n:size_nat { n > 0 }) =
  let open FStar.Mul in
  if is_md a then
    word_length a * hash_word_length a
  else
    match a with
    | SHA3_224 -> 28
    | SHA3_256 -> 32
    | SHA3_384 -> 48
    | SHA3_512 -> 64
    | Blake2S -> 4 * 8
    | Blake2B -> 8 * 8

(** Padding *)

(* Number of zeroes that should go into the padding *)
let pad0_length (a:md_alg) (len:nat): Tot (n:nat{(len + 1 + n + len_length a) % block_length a = 0}) =
  (block_length a - (len + len_length a + 1)) % block_length a

(* Total length for the padding, a.k.a. the suffix length. *)
let pad_length (a: md_alg) (len: nat): Tot (n:nat { (len + n) % block_length a = 0 }) =
  pad0_length a len + 1 + len_length a

(** Endian-ness *)

(* Define word based operators *)
let bytes_of_words: a:hash_alg{is_md a} -> Tot (#len:size_nat{FStar.Mul.(len * word_length a) <= max_size_t} -> s:lseq (word a) len -> Tot (lbytes FStar.Mul.(word_length a * len))) = function
  | MD5 -> Lib.ByteSequence.uints_to_bytes_le #U32 #SEC
  | SHA1 | SHA2_224 | SHA2_256 -> Lib.ByteSequence.uints_to_bytes_be #U32 #SEC
  | SHA2_384 | SHA2_512 -> Lib.ByteSequence.uints_to_bytes_be #U64 #SEC

let words_of_bytes: a:hash_alg{is_md a} -> Tot (#len:size_nat{FStar.Mul.(len * word_length a) <= max_size_t} -> b:lbytes FStar.Mul.(word_length a * len) -> Tot (lseq (word a) len)) = function
  | MD5 -> Lib.ByteSequence.uints_from_bytes_le #U32 #SEC
  | SHA1 | SHA2_224 | SHA2_256 -> Lib.ByteSequence.uints_from_bytes_be #U32 #SEC
  | SHA2_384 | SHA2_512 -> Lib.ByteSequence.uints_from_bytes_be #U64 #SEC

(** The data format taken and returned by the hash specifications. *)

(* Input data. *)
type bytes = Seq.seq uint8

(* Input data, multiple of a block length. *)
```
`specs/Spec.Agile.Hash.fsti:54-77`
```fstar
val init (a:hash_alg): init_t a

let init_extra_state (a:hash_alg) : extra_state a = match a with
  | Blake2B | Blake2S -> 0
  | _ -> ()

(* The individual update function. This is an implementation detail, and clients
should reason in terms of update_multi to be fully agile. None of the hash laws
refer to update. *)
val update (a:md_alg): update_t a

(* Because of blake2, we unfortunately have this precondition creeping up. *)
let update_multi_pre
  (a:hash_alg)
  (prev:extra_state a)
  (blocks:bytes)
=
  match a with
  | Blake2B | Blake2S ->
      (S.length blocks + prev) `less_than_max_input_length` a
  | _ -> true

(* Agile multi-block processing function shown to obey the hash laws. *)
val update_multi
```
### AEAD agility
`specs/Spec.Agile.AEAD.fsti:10-126`
```fstar
type alg =
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305
  // the algorithms below are used in TLS 1.3 but not yet supported by
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

let cipher_alg_of_supported_alg (a: supported_alg): Spec.Agile.Cipher.cipher_alg =
  let open Spec.Agile.Cipher in
  match a with
  | AES128_GCM -> AES128
  | AES256_GCM -> AES256
  | CHACHA20_POLY1305 -> CHACHA20

// naming convention: length for nats, len for uint32s
let key_length (a: alg): nat =
  match a with
  | AES128_GCM
  | AES256_GCM
  | CHACHA20_POLY1305 -> Spec.Agile.Cipher.key_length (cipher_alg_of_supported_alg a)
  | AES128_CCM        -> 16
  | AES128_CCM8       -> 16
  | AES256_CCM        -> 32
  | AES256_CCM8       -> 32

let tag_length: alg -> nat =
  function
  | AES128_CCM8       ->  8
  | AES256_CCM8       ->  8
  | AES128_GCM        -> 16
  | AES256_GCM        -> 16
  | CHACHA20_POLY1305 -> 16
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

let uint8 = Lib.IntTypes.uint8

// Proudly defining this type abbreviation for the tenth time in HACL*!
let lbytes (l:nat) = b:Seq.seq uint8 { Seq.length b = l }

// Note: using <= for maximum admissible lengths
// Note: not indexing the types over their lengths; we can use S.length in specs
let kv a = lbytes (key_length a)
let iv a = s:S.seq uint8 { iv_length a (S.length s) }
let ad a = s:S.seq uint8 { S.length s <= max_length a }
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

val correctness: #a:supported_alg -> k:kv a -> n:iv a -> aad:ad a -> p:plain a ->
  Lemma (decrypt k n aad (encrypt k n aad p) == Some p)
```
### HMAC agility
`specs/Spec.Agile.HMAC.fsti:8-31`
```fstar
let lbytes (l:nat) = b:bytes {Seq.length b = l}

let keysized (a:hash_alg) (l:nat) =
  l `less_than_max_input_length` a /\
  l + block_length a < pow2 32

val wrap
  (a: fixed_len_alg)
  (key: bytes{Seq.length key `less_than_max_input_length` a})
  : lbytes (block_length a)

let xor (x: uint8) (v: bytes) : lbytes (Seq.length v) =
  Spec.Loops.seq_map (logxor x) v

val hmac:
  a: fixed_len_alg ->
  key: bytes ->
  data: bytes ->
  Pure (lbytes (hash_length a))
    (requires keysized a (Seq.length key) /\
      (Seq.length data + block_length a) `less_than_max_input_length` a)
    (ensures fun _ -> True)
```
### HKDF agility
`specs/Spec.Agile.HKDF.fsti:5-35`
```fstar

let lbytes (l:nat) = b:bytes {Seq.length b = l}

let extract_ikm_length_pred (a:hash_alg) (ikm_length:nat) =
  (ikm_length + block_length a) `less_than_max_input_length` a

val extract:
  a: fixed_len_alg ->
  key: bytes ->
  data: bytes ->
  Pure (lbytes (hash_length a))
    (requires
      Spec.Agile.HMAC.keysized a (Seq.length key) /\
      extract_ikm_length_pred a (Seq.length data))
    (ensures fun _ -> True)

let expand_info_length_pred (a:fixed_len_alg) (info_length:nat) =
  (hash_length a + info_length + 1 + block_length a) `less_than_max_input_length` a

let expand_output_length_pred (a:fixed_len_alg) (len:nat) =
  len <= 255 * hash_length a

val expand:
  a: fixed_len_alg ->
  prk: bytes ->
  info: bytes ->
  len: nat ->
  Pure (lbytes len)
    (requires
      hash_length a <= Seq.length prk /\
      HMAC.keysized a (Seq.length prk) /\
```
### Cipher/CTR agility
`specs/Spec.Agile.Cipher.fsti:17-93`
```fstar
/// Definitions
/// -----------

type cipher_alg =
  | AES128
  | AES256
  | CHACHA20

/// The AES spec itself is agile; this is the same nested agility technique used
/// for SHA2 vs. MD.
let aes_alg_of_alg (a: cipher_alg { a = AES128 \/ a = AES256 }) =
  match a with
  | AES128 -> Spec.AES.AES128
  | AES256 -> Spec.AES.AES256

/// Trying to enforce conventions: lengths for nats (spec); len for machine
/// integers (runtime).
let key_length (a: cipher_alg): size_nat =
  match a with
  | AES128 | AES256 -> Spec.AES.key_size (aes_alg_of_alg a)
  | CHACHA20 -> Spec.Chacha20.size_key

let key (a: cipher_alg) =
  match a with
  | AES128 | AES256 -> Spec.AES.aes_key (aes_alg_of_alg a)
  | CHACHA20 -> Spec.Chacha20.key

let block_length (a:cipher_alg) =
  match a with
  | AES128 | AES256 -> 16
  | CHACHA20 -> 64

let block a = lbytes (block_length a)

/// Smaller bound than for AES-GCM; no IV reduction.
let nonce_bound (a: cipher_alg) (n_len: nat): Type0 =
  match a with
  | AES128 | AES256 -> n_len <= block_length a
  | CHACHA20 -> n_len == 12

let nonce a = b:bytes { nonce_bound a (length b) }

let ctr = size_nat


/// The stream cipher
/// -----------------

/// One block of pseudo-random bytes.
val ctr_block (a: cipher_alg) (k: key a) (iv: nonce a) (c: ctr): block a

/// A stream of pseudo-random bytes, starting from counter zero. The length is
/// artificially constrained to be < 2^32.
let ctr_stream (a: cipher_alg) (k: key a) (iv: nonce a) (len: size_nat):
  b:bytes { length b = len }
=
  // JP: useful? be overconservative and always do + 1? would necessitate a
  // little bit of reasoning on the implementation side, perhaps better to have
  // a tighter bound here
  let n_blocks: n:nat { n * block_length a >= len } =
    if len % block_length a = 0 then
      len / block_length a
    else
      len / block_length a + 1
  in
  let (), blocks = generate_blocks
    (block_length a)
    max_size_t
    n_blocks
    (fun _ -> unit) // extra cruft; no accumulator here
    (fun i _ -> (), ctr_block a k iv i )
    ()
  in
  Seq.slice blocks 0 len


/// TODO
```
### DH agility
`specs/Spec.Agile.DH.fst:10-57`
```fstar

type algorithm =
  | DH_Curve25519
  | DH_P256

inline_for_extraction
let size_key (a:algorithm) : Tot size_nat =
  match a with
  | DH_Curve25519 -> 32
  | DH_P256 -> 32

inline_for_extraction
let size_public (a:algorithm) : Tot size_nat =
  match a with
  | DH_Curve25519 -> 32
  | DH_P256 -> 64

inline_for_extraction
let prime (a:algorithm) =
  match a with
  | DH_Curve25519 -> Spec.Curve25519.prime
  | DH_P256 -> Spec.P256.prime

/// Types

type scalar (a:algorithm) = lbytes (size_key a)
type serialized_point (a:algorithm) = lbytes (size_public a)


/// Functions

val clamp: alg:algorithm{alg = DH_Curve25519} -> scalar alg -> Tot (scalar alg)
let clamp a k =
  match a with
  | DH.DH_Curve25519 -> Spec.Curve25519.decodeScalar k

#set-options "--z3rlimit 50"

val dh: a:algorithm -> s:scalar a -> p:serialized_point a -> Tot (option (serialized_point a))
let dh a s p =
  match a with
  | DH_Curve25519 ->
    let output = Spec.Curve25519.scalarmult s p in
    let is_valid = not (lbytes_eq (create (size_public a) (u8 0)) output) in
    if is_valid then Some output else None
  | DH_P256 ->
    Spec.P256.ecdh p s

```
### HPKE agility
`specs/Spec.Agile.HPKE.fsti:10-80`
```fstar
module AEAD = Spec.Agile.AEAD
module Hash = Spec.Agile.Hash
module HKDF = Spec.Agile.HKDF

#set-options "--z3rlimit 20 --fuel 0 --ifuel 1"

type mode =
  | Base
  | PSK
  | Auth
  | AuthPSK

let is_valid_kem = function
  | DH.DH_Curve25519, Hash.SHA2_256
  | DH.DH_P256,       Hash.SHA2_256 -> true
  | _,_ -> false

noeq type aead =
  | Seal: alg:AEAD.alg -> aead
  | ExportOnly

let is_valid_aead = function
  | Seal AEAD.AES128_GCM
  | Seal AEAD.AES256_GCM
  | Seal AEAD.CHACHA20_POLY1305
  | ExportOnly -> true
  | _ -> false

let is_valid_hash = function
  | Hash.SHA2_256
  | Hash.SHA2_384
  | Hash.SHA2_512 -> true
  | _ -> false

let hash_algorithm = a:Hash.hash_alg{is_valid_hash a}

let is_valid_ciphersuite (cs:DH.algorithm & hash_algorithm & aead & Hash.hash_alg) : bool =
  let kem_dh, kem_hash, aead, hash = cs in
  (is_valid_kem (kem_dh, kem_hash)) && (is_valid_aead aead) && (is_valid_hash hash)

let ciphersuite = cs:(DH.algorithm & hash_algorithm & aead & Hash.hash_alg){is_valid_ciphersuite cs}

inline_for_extraction
let kem_dh_of_cs (cs:ciphersuite) : DH.algorithm =
  let (c,_,_,_) = cs in c

inline_for_extraction
let kem_hash_of_cs (cs:ciphersuite) : hash_algorithm =
  let (_,h,_,_) = cs in h

inline_for_extraction
let aead_of_cs (cs:ciphersuite) : aead =
  let (_,_,a,_) = cs in a

inline_for_extraction
let hash_of_cs (cs:ciphersuite) : hash_algorithm =
  let (_,_,_,h) = cs in h

let is_valid_not_export_only_ciphersuite (cs:ciphersuite) : bool =
  match aead_of_cs cs with
  | ExportOnly -> false
  | Seal _ -> true

let ciphersuite_not_export_only = cs:ciphersuite{is_valid_not_export_only_ciphersuite cs}

inline_for_extraction
let aead_alg_of (cs:ciphersuite_not_export_only) = match aead_of_cs cs with
  | Seal alg -> alg


/// Constants for HPKE labels
```
`specs/Spec.Agile.HPKE.fsti:260-302`
```fstar
let size_aead_nonce (cs:ciphersuite): size_nat =
  assert_norm (8 * 12 <= pow2 64 - 1);
  match aead_of_cs cs with
  | ExportOnly -> 0
  | Seal _ -> 12

inline_for_extraction
let size_aead_key (cs:ciphersuite): size_nat =
  match aead_of_cs cs with
  | ExportOnly -> 0
  | Seal _ -> AEAD.key_length (aead_alg_of cs)

inline_for_extraction
let size_aead_tag (cs:ciphersuite): size_nat =
  match aead_of_cs cs with
  | ExportOnly -> 0
  | Seal _ -> AEAD.tag_length (aead_alg_of cs)

inline_for_extraction
let size_dh_key (cs:ciphersuite): size_nat = DH.size_key (kem_dh_of_cs cs)

inline_for_extraction
let size_dh_public (cs:ciphersuite): size_nat = match kem_dh_of_cs cs with
  | DH.DH_Curve25519 -> DH.size_public DH.DH_Curve25519
  | DH.DH_P256 -> DH.size_public DH.DH_P256 + 1 // Need the additional byte for representation

inline_for_extraction
let size_dh_serialized (cs:ciphersuite): size_nat = match kem_dh_of_cs cs with
  | DH.DH_Curve25519 -> DH.size_public DH.DH_Curve25519
  | DH.DH_P256 -> DH.size_public DH.DH_P256

inline_for_extraction
let size_kem_kdf (cs:ciphersuite): size_nat = Hash.hash_length (kem_hash_of_cs cs)

inline_for_extraction
let size_kem_key (cs:ciphersuite): size_nat = Hash.hash_length (kem_hash_of_cs cs)

inline_for_extraction
let size_kdf (cs:ciphersuite): size_nat = Hash.hash_length (hash_of_cs cs)

let max_seq (cs:ciphersuite): nat =
  match aead_of_cs cs with
  | ExportOnly -> 0
```
`specs/Spec.Agile.HPKE.fsti:348-386`
```fstar
type key_dh_public_s (cs:ciphersuite) = lbytes (size_dh_public cs)
type key_dh_secret_s (cs:ciphersuite) = lbytes (size_dh_key cs)
type key_kem_s (cs:ciphersuite) = lbytes (size_kem_key cs)
type key_aead_s (cs:ciphersuite) = lbytes (size_aead_key cs)
type nonce_aead_s (cs:ciphersuite) = lbytes (size_aead_nonce cs)
type seq_aead_s (cs:ciphersuite) = n:nat{n <= max_seq cs}
type exporter_secret_s (cs:ciphersuite) = lbytes (size_kdf cs)
type psk_s (cs:ciphersuite) = b:bytes{Seq.length b >= 32 /\ Seq.length b `maybe_lte` (max_length_psk (hash_of_cs cs))}
type psk_id_s (cs:ciphersuite) = b:bytes{Seq.length b >= 1 /\ Seq.length b `maybe_lte` (max_length_psk_id (hash_of_cs cs))}
type info_s (cs:ciphersuite) = b:bytes{Seq.length b `maybe_lte` (max_length_info (hash_of_cs cs))}
type exp_ctx_s (cs:ciphersuite) = b:bytes{Seq.length b `maybe_lte` (max_length_exp_ctx (hash_of_cs cs))}
type dkp_ikm_s (cs:ciphersuite) = b:bytes{Seq.length b `maybe_lte` (max_length_dkp_ikm (kem_hash_of_cs cs)) /\ Seq.length b >= size_dh_key cs}

// deserialize returns a serialized point, this is due to HPKE
// using a different format (the extra byte)
val deserialize_public_key:
    cs:ciphersuite
  -> pk:key_dh_public_s cs ->
  Tot (DH.serialized_point (kem_dh_of_cs cs))

val serialize_public_key:
    cs:ciphersuite
  -> pk:DH.serialized_point (kem_dh_of_cs cs) ->
  Tot (key_dh_public_s cs)

// never returns None for Curve25519.
val derive_key_pair:
    cs:ciphersuite
  -> ikm:dkp_ikm_s cs ->
  Tot (option (key_dh_secret_s cs & key_dh_public_s cs))

val encryption_context (cs:ciphersuite) : Type0

let exp_len (cs:ciphersuite) = l:size_nat{HKDF.expand_output_length_pred (hash_of_cs cs) l}

val context_export:
    cs:ciphersuite
  -> ctx:encryption_context cs
  -> exp_ctx:exp_ctx_s cs
```
`specs/Spec.Agile.HPKE.fsti:388-620`
```fstar
  Tot (lbytes l)

val context_compute_nonce:
    cs:ciphersuite_not_export_only
  -> ctx:encryption_context cs
  -> seq:seq_aead_s cs ->
  Tot (nonce_aead_s cs)

val context_increment_seq:
    cs:ciphersuite_not_export_only
  -> ctx:encryption_context cs ->
  Tot (option (encryption_context cs))

val context_seal:
    cs:ciphersuite_not_export_only
  -> ctx:encryption_context cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs) ->
  Tot (option (encryption_context cs & AEAD.cipher (aead_alg_of cs)))

val context_open:
    cs:ciphersuite_not_export_only
  -> ctx:encryption_context cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs) ->
  Tot (option (encryption_context cs & AEAD.plain (aead_alg_of cs)))

val setupBaseS:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs ->
  Tot (option (key_dh_public_s cs & encryption_context cs))

val setupBaseR:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs ->
  Tot (option (encryption_context cs))

val sealBase:
    cs:ciphersuite_not_export_only
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs) ->
  Tot (option (key_dh_public_s cs & AEAD.encrypted #(aead_alg_of cs) pt))

val openBase:
    cs:ciphersuite_not_export_only
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs) ->
  Tot (option (AEAD.decrypted #(aead_alg_of cs) ct))

val sendExportBase:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs ->
  Tot (option (key_dh_public_s cs & lbytes l))

val receiveExportBase:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs ->
  Tot (option (lbytes l))

val setupPSKS:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (key_dh_public_s cs & encryption_context cs))

val setupPSKR:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (encryption_context cs))

val sealPSK:
    cs:ciphersuite_not_export_only
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs)
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (key_dh_public_s cs & AEAD.encrypted #(aead_alg_of cs) pt))

val openPSK:
    cs:ciphersuite_not_export_only
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs)
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (AEAD.decrypted #(aead_alg_of cs) ct))

val sendExportPSK:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (key_dh_public_s cs & lbytes l))

val receiveExportPSK:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs ->
  Tot (option (lbytes l))

val setupAuthS:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & encryption_context cs))

val setupAuthR:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> pkS:DH.serialized_point (kem_dh_of_cs cs) ->
  Tot (option (encryption_context cs))

val sealAuth:
    cs:ciphersuite_not_export_only
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs)
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & AEAD.encrypted #(aead_alg_of cs) pt))

val openAuth:
    cs:ciphersuite_not_export_only
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> ct:AEAD.cipher (aead_alg_of cs)
  -> pkS:DH.serialized_point (kem_dh_of_cs cs) ->
  Tot (option (AEAD.decrypted #(aead_alg_of cs) ct))

val sendExportAuth:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & lbytes l))

val receiveExportAuth:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> exp_ctx:exp_ctx_s cs
  -> l:exp_len cs
  -> pkS:DH.serialized_point (kem_dh_of_cs cs) ->
  Tot (option (lbytes l))

val setupAuthPSKS:
    cs:ciphersuite
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & encryption_context cs))

val setupAuthPSKR:
    cs:ciphersuite
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> pkS:DH.serialized_point (kem_dh_of_cs cs) ->
  Tot (option (encryption_context cs))

val sealAuthPSK:
    cs:ciphersuite_not_export_only
  -> skE:key_dh_secret_s cs
  -> pkR:DH.serialized_point (kem_dh_of_cs cs)
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
  -> pt:AEAD.plain (aead_alg_of cs)
  -> psk:psk_s cs
  -> psk_id:psk_id_s cs
  -> skS:key_dh_secret_s cs ->
  Tot (option (key_dh_public_s cs & AEAD.encrypted #(aead_alg_of cs) pt))

val openAuthPSK:
    cs:ciphersuite_not_export_only
  -> enc:key_dh_public_s cs
  -> skR:key_dh_secret_s cs
  -> info:info_s cs
  -> aad:AEAD.ad (aead_alg_of cs)
```
## 4. Theorems and named lemmas
The statement column folds whitespace for table readability; each entry is copied from the source declaration. Classification is syntactic: `SMTPat` means SMT-pattern; otherwise call explicitly unless unfolding suffices.
### Critical facts and notable absences
```fstar
val correctness: #a:supported_alg -> k:kv a -> n:iv a -> aad:ad a -> p:plain a ->
  Lemma (decrypt k n aad (encrypt k n aad p) == Some p)
```
This proves `decrypt k n aad (encrypt k n aad p) == Some p` (`specs/Spec.Agile.AEAD.fsti:125`); explicit/no SMTPat.
- **No exposed sign-then-verify lemma found** for Ed25519, P-256, or K-256/secp256k1, despite entry points (`specs/Spec.Ed25519.fst:133,139`; `specs/Spec.P256.fst:97,116,144,158`; `specs/Spec.K256.fst:85,108,145,150,232,244`).
- **No exposed DH/ECDH commutativity lemma found** for Curve25519, agile DH, P-256/K-256 ECDH, or FFDHE (`specs/Spec.Curve25519.fst:120`; `specs/Spec.Agile.DH.fst:39,51`; `specs/Spec.P256.fst:184`; `specs/Spec.K256.fst:166`; `specs/Spec.FFDHE.fst:596`).
### Lemma catalogue
| Source | Name | Classification | Exact statement | Client conclusion |
|---|---|---|---|---|
| `specs/lemmas/Spec.Hash.Incremental.fsti:22` | `hash_is_hash_incremental'` | explicit/no SMTPat | `val hash_is_hash_incremental' (a: hash_alg) (input: bytes { S.length input `less_than_max_input_length` a }) (l: output_length a): Lemma (S.equal (hash' a input l) (hash_incremental a input l))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Hash.Lemmas.fsti:16` | `update_multi_zero` | explicit/no SMTPat | `val update_multi_zero (a: hash_alg { not (is_blake a)} ) (h: words_state a): Lemma (ensures (update_multi a h () S.empty == h))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Hash.Lemmas.fsti:19` | `update_multi_zero_blake` | explicit/no SMTPat | `val update_multi_zero_blake (a: hash_alg { is_blake a } ) (prevlen: extra_state a) (h: words_state a): Lemma (requires (update_multi_pre a prevlen S.empty)) (ensures (update_multi a h prevlen S.empty == h))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Hash.Lemmas.fsti:25` | `update_multi_update` | explicit/no SMTPat | `val update_multi_update (a: md_alg) (h: words_state a) (input: bytes_block a): Lemma (ensures (update_multi a h () input == update a h input))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Hash.Lemmas.fsti:29` | `update_multi_associative` | explicit/no SMTPat | `val update_multi_associative (a: hash_alg{not (is_blake a)}) (h: words_state a) (input1: bytes) (input2: bytes): Lemma (requires S.length input1 % block_length a == 0 /\ S.length input2 % block_length a == 0) (ensures ( let input = S.append input1 input2 in S.length input % block_length a == 0 /\ update_multi a (update_multi a h () input1) () input2 == update_multi a h () input))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Hash.Lemmas.fsti:42` | `update_multi_associative_blake` | explicit/no SMTPat | `val update_multi_associative_blake (a: blake_alg) (h: words_state a) (prevlen1: nat) (prevlen2: nat) (input1: bytes) (input2: bytes): Lemma (requires ( prevlen1 % block_length a = 0 /\ S.length input1 % block_length a == 0 /\ S.length input2 % block_length a == 0 /\ prevlen2 = prevlen1 + S.length input1 /\ update_multi_pre a prevlen1 (S.append input1 input2))) (ensures ( let input = S.append input1 input2 in S.length input % block_length a == 0 /\ update_multi_pre a prevlen1 input1 /\ update_multi_pre a prevlen2 input2 /\ update_multi a (update_multi a h prevlen1 input1) prevlen2 input2 == update_multi a h prevlen1 input))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Hash.Lemmas.fsti:62` | `block_length_smaller_than_max_input` | explicit/no SMTPat | `val block_length_smaller_than_max_input (a:hash_alg) : Lemma (block_length a `less_than_max_input_length` a)` | the proposition/ensures shown |
| `specs/lemmas/Spec.HMAC.Incremental.fsti:47` | `hmac_incremental` | explicit/no SMTPat | `let hmac_incremental (a: fixed_len_alg) (k: sized_key a) (input: bytes): Pure (lbytes (hash_length a)) (requires (Seq.length input + init_input_length a) `less_than_max_input_length` a) (ensures fun _ -> True) = let input1 = S.append (init_input a k) input in let bs, rest = Spec.Hash.Incremental.Definitions.split_blocks a input1 in (**) Math.Lemmas.modulo_lemma 0 (block_length a); let hash0, second_hash = init a k in let hash1 = Spec.Agile.Hash.update_multi a hash0 (Spec.Agile.Hash.init_extra_state a) bs in let hash2 = Spec.Hash.Incremental.Definitions.update_last a hash1 (if is_keccak a then () else S.length bs) rest in finish a k (hash2, second_hash)` | the proposition/ensures shown |
| `specs/lemmas/Spec.HMAC.Incremental.fsti:65` | `hmac_is_hmac_incremental` | explicit/no SMTPat | `val hmac_is_hmac_incremental (a: fixed_len_alg) (k: sized_key a) (data: bytes): Lemma (requires (Seq.length data + block_length a) `less_than_max_input_length` a) (ensures (S.equal (hmac a k data) (hmac_incremental a k data)))` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.Lemmas.fsti:24` | `split_at_last_lazy_nb_rem_spec` | explicit/no SMTPat | `val split_at_last_lazy_nb_rem_spec (l : pos) (d n rest: nat) : Lemma (requires ( rest <= l /\ (rest = 0 ==> d = 0) /\ d = n * l + rest)) (ensures ((n, rest) = split_at_last_lazy_nb_rem l d))` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.Lemmas.fsti:33` | `split_at_last_lazy_spec` | explicit/no SMTPat | `val split_at_last_lazy_spec (l : pos) (b blocks rest: S.seq uint8) : Lemma (requires ( S.length blocks % l = 0 /\ S.length rest <= l /\ (S.length rest = 0 ==> S.length b = 0) /\ b `Seq.equal` Seq.append blocks rest)) (ensures ( (blocks, rest) == split_at_last_lazy l b))` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.Lemmas.fsti:66` | `update_full_is_repeat_blocks:` | explicit/no SMTPat | `val update_full_is_repeat_blocks: #a:Type0 -> block_length:pos { block_length < pow2 32 } -> update: (a -> s:S.seq uint8 { S.length s = block_length } -> a) -> update_last: (a -> s:S.seq uint8 { S.length s < block_length } -> a) -> acc:a -> input:S.seq uint8 -> input':S.seq uint8 -> Lemma (requires ( S.length input % block_length == S.length input' % block_length)) (ensures ( let repeat_f = repeat_f block_length update in let repeat_l = repeat_l block_length update_last input' in` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.Lemmas.fsti:85` | `update_multi_is_repeat_blocks_multi:` | explicit/no SMTPat | `val update_multi_is_repeat_blocks_multi: #a:Type0 -> block_length:pos{ block_length < pow2 32 } -> update: (a -> s:S.seq uint8 { S.length s = block_length } -> a) -> acc:a -> input:S.seq uint8 -> Lemma (requires (S.length input % block_length == 0)) (ensures ( let repeat_f = repeat_f block_length update in Lib.Sequence.repeat_blocks_multi #uint8 block_length input repeat_f acc == Lib.UpdateMulti.mk_update_multi block_length update acc input)) (decreases (S.length input))` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:27` | `split_nb_lem` | explicit/no SMTPat | `let split_nb_lem (block_length: pos) (data_length: nat) (n: nat): Lemma (requires n <= data_length / block_length) (ensures ( 0 <= n * block_length /\ n * block_length <= data_length /\ n * block_length % block_length = 0 /\ (data_length - n * block_length) % block_length = data_length % block_length)) = let bl = n * block_length in Math.Lemmas.nat_times_nat_is_nat n block_length; Math.Lemmas.nat_over_pos_is_nat bl block_length; assert(bl >= 0); assert(bl / block_length >= 0); Math.Lemmas.multiple_modulo_lemma n block_length; assert(bl % block_length = 0); calc (<=) { bl; <= { Math.Lemmas.lemma_mult_le_right block_length n (data_length / block_length) } (data_length / block_length) * block_length; <= {} (data_length / block_length) * block_length + data_length % block_length; == { Math.Lemmas.euclidean_division_definition data_length block_length } data_length; }; let r = data_length - bl in calc (==) { r % block_length; == { Math.Lemmas.modulo_distributivity data_length (- bl) block_length } (data_length % block_length + (- bl) % block_length) % block_length; == { Math.Lemmas.paren_mul_right (-1) n block_length } (data_length % block_length + ((- n) * block_length) % block_length) % block_length; == { Math.Lemmas.multiple_modulo_lemma (-n) block_length } (data_length % block_length) % block_length; == { Math.Lemmas.lemma_mod_add_distr 0 data_length block_length } data_length % block_length; }` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:102` | `split_at_last_nb_rem` | explicit/no SMTPat | `let split_at_last_nb_rem (block_length: pos) (data_length: nat) : Pure (nat & nat) (requires True) (ensures fun (n, rem) -> 0 <= n * block_length /\ n * block_length <= data_length /\ n * block_length % block_length = 0 /\ (rem % block_length = data_length % block_length) /\ n = data_length / block_length /\ rem = data_length % block_length /\ 0 <= rem /\ rem < block_length /\ data_length = n * block_length + rem) = let n = data_length / block_length in let rem = data_length % block_length in Math.Lemmas.nat_over_pos_is_nat data_length block_length; split_nb_lem block_length data_length n; Math.Lemmas.euclidean_division_definition data_length block_length; n, rem` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:147` | `split_at_last_lazy_nb_rem` | explicit/no SMTPat | `let split_at_last_lazy_nb_rem (l: pos) (d: nat) : Pure (nat & nat) (requires True) (ensures (fun (n, rem) -> let blocks = n * l in rem <= l /\ (rem % l = d % l) /\ (rem = d % l \/ rem = l) /\ (rem = 0 <==> d == 0) /\ (rem = l <==> (blocks = (d / l - 1) * l)) /\ ((rem > 0 /\ rem < l) <==> d % l <> 0) /\ (rem = (d % l) <==> (blocks = (d / l) * l)) /\ blocks % l = 0 /\ (blocks / l) * l = blocks )) = let n, rem = split_at_last_nb_rem l d in (**) let blocks = n * l in (**) Math.Lemmas.euclidean_division_definition blocks l; (**) assert((blocks / l) * l = blocks); (**) Math.Lemmas.distributivity_sub_left (d / l) 1 l; (**) assert((d / l - 1) * l = (d / l) * l - l); if n > 0 && rem = 0 then begin let n' = n - 1 in (**) let blocks' = n' * l in let rem' = d - blocks' in (**) assert(rem = 0); (**) assert(blocks' = blocks - l); (**) assert(rem' = l); (**) Math.Lemmas.nat_times_nat_is_nat n' l; (**) assert(n' * l >= 0); (**) assert(d > 0); (**) Math.Lemmas.lemma_mod_sub_distr blocks l l; (**) assert(l % l = 0); (**) assert(blocks' % l = 0); (**) Math.Lemmas.euclidean_division_definition blocks' l; (**) assert((blocks' / l) * l = blocks'); n', rem' end else begin (* Proof interlude *) (**) begin (**) assert(d % l <> 0 \|\| n = 0); (**) if d % l <> 0 then (**) begin (**) assert(rem <> 0); (**) Math.Lemmas.nat_times_nat_is_nat n l; (**) assert(n * l >= 0)` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:231` | `split_at_last_lazy` | explicit/no SMTPat | `let split_at_last_lazy (l: pos) (b: S.seq uint8) : Pure (S.seq uint8 & S.seq uint8) (requires True) (ensures (fun (blocks, rest) -> S.length rest <= l /\ (S.length rest % l = S.length b % l) /\ (S.length rest = S.length b % l \/ S.length rest = l) /\ (S.length rest = 0 <==> S.length b == 0) /\ (S.length rest = l <==> (S.length blocks = (S.length b / l - 1) * l)) /\ ((S.length rest > 0 /\ S.length rest < l) <==> S.length b % l <> 0) /\ (S.length rest = (S.length b % l) <==> (S.length blocks = (S.length b / l) * l)) /\ S.equal (S.append blocks rest) b /\ S.length blocks % l = 0 /\ (S.length blocks / l) * l = S.length blocks)) = let n, rem = split_at_last_lazy_nb_rem l (Seq.length b) in Math.Lemmas.nat_times_nat_is_nat n l; let blocks, rest = S.split b (n * l) in blocks, rest` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:276` | `update_full` | explicit/no SMTPat | `let update_full #a (block_length:pos) (update: a -> (s:S.seq uint8 { S.length s = block_length }) -> a) (update_last: a -> (s:S.seq uint8 { S.length s < block_length }) -> a) (acc: a) (input: S.seq uint8) = // let n_blocks = S.length input / block_length in // let rem = S.length input % block_length in // let blocks, rest = S.split input (n_blocks * block_length) in let blocks, rest = split_at_last block_length input in // assert (S.length rest = S.length input % block_length); // Math.Lemmas.multiple_modulo_lemma n_blocks block_length; // assert (S.length blocks % block_length = 0); // assert (S.length rest < block_length); update_last (mk_update_multi block_length update acc blocks) rest` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:297` | `update_full_lazy` | explicit/no SMTPat | `let update_full_lazy #a (block_length:pos) (update: a -> (s:S.seq uint8 { S.length s = block_length }) -> a) (update_last: a -> (s:S.seq uint8 { S.length s <= block_length }) -> a) (acc: a) (input: S.seq uint8) = // let n_blocks = S.length input / block_length in // let rem = S.length input % block_length in // let n_blocks, rem = if rem = 0 && n_blocks > 0 then n_blocks - 1, block_length // else n_blocks, rem in // let blocks, rest = S.split input (n_blocks * block_length) in let blocks, rest = split_at_last_lazy block_length input in // assert (S.length rest % block_length = S.length input % block_length); // Math.Lemmas.multiple_modulo_lemma n_blocks block_length; // assert (S.length blocks % block_length = 0); // assert (S.length rest <= block_length); update_last (mk_update_multi block_length update acc blocks) rest` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:321` | `concat_blocks_modulo` | explicit/no SMTPat | `let concat_blocks_modulo (block_len: pos) (s1 s2: S.seq uint8): Lemma (requires S.length s1 % block_len = 0 /\ S.length s2 % block_len = 0) (ensures S.length (S.append s1 s2) % block_len = 0) = let input = S.append s1 s2 in let input1 = s1 in let input2 = s2 in calc (==) { S.length input % block_len; == { S.lemma_len_append input1 input2 } (S.length input1 + S.length input2) % block_len; == { FStar.Math.Lemmas.modulo_distributivity (S.length input1) (S.length input2) (block_len) } (S.length input1 % block_len + S.length input2 % block_len) % block_len; == { (* hyp *) } 0 % block_len; == { FStar.Math.Lemmas.small_mod 0 block_len } 0; }` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:347` | `update_multi_zero` | explicit/no SMTPat | `let update_multi_zero #a (block_length: pos) (update: update_t a block_length) (acc: a): Lemma (ensures (mk_update_multi block_length update acc S.empty == acc)) = ()` | the proposition/ensures shown |
| `lib/Lib.UpdateMulti.fst:357` | `rec` | explicit/no SMTPat | `let rec update_multi_associative #a (block_length: pos) (update: update_t a block_length) (acc: a) (input1 input2: S.seq uint8): Lemma (requires S.length input1 % block_length == 0 /\ S.length input2 % block_length == 0) (ensures ( let input = S.append input1 input2 in S.length input % block_length == 0 /\ mk_update_multi block_length update (mk_update_multi block_length update acc input1) input2 == mk_update_multi block_length update acc input)) (decreases ( S.length input1 + S.length input2)) = let input = S.append input1 input2 in concat_blocks_modulo block_length input1 input2; if S.length input1 = 0 then calc (==) { mk_update_multi block_length update (mk_update_multi block_length update acc input1) input2; == { update_multi_zero block_length update acc } mk_update_multi block_length update acc input2; == { S.lemma_eq_intro input2 (S.empty `S.append` input2) } mk_update_multi block_length update acc (S.empty `S.append` input2); == { S.lemma_eq_intro input1 S.empty } mk_update_multi block_length update acc (input1 `S.append` input2); } else let input1_hd, input1_tl = split_block block_length input1 1 in S.lemma_eq_intro input1 (input1_hd `S.append` input1_tl); update_multi_associative block_length update (update acc input1_hd) input1_tl input2; let s = input1_hd `S.append` (input1_tl `S.append` input2) in S.lemma_eq_intro (fst (S.split s (1 * block_length))) input1_hd; S.lemma_eq_intro (snd (S.split s (1 * block_length))) (input1_tl `S.append` input2); S.lemma_eq_intro (input1_hd `S.append` (input1_tl `S.append` input2)) input` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:11` | `aff_point_add_lemma:` | explicit/no SMTPat | `val aff_point_add_lemma: p:aff_point -> q:aff_point -> Lemma (requires is_on_curve p /\ is_on_curve q) (ensures is_on_curve (aff_point_add p q))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:15` | `aff_point_add_assoc_lemma:` | explicit/no SMTPat | `val aff_point_add_assoc_lemma: p:aff_point -> q:aff_point -> s:aff_point -> Lemma (aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:18` | `aff_point_at_infinity_lemma:` | explicit/no SMTPat | `val aff_point_at_infinity_lemma: p:aff_point -> Lemma (aff_point_add p aff_point_at_infinity == p)` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:21` | `aff_point_add_comm_lemma:` | explicit/no SMTPat | `val aff_point_add_comm_lemma: p:aff_point -> q:aff_point -> Lemma (aff_point_add p q == aff_point_add q p)` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:24` | `aff_point_double_lemma:` | explicit/no SMTPat | `val aff_point_double_lemma: p:aff_point{is_on_curve p} -> Lemma (aff_point_double p == aff_point_add p p)` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:27` | `aff_point_negate_lemma:` | explicit/no SMTPat | `val aff_point_negate_lemma: p:aff_point -> Lemma (requires is_on_curve p) (ensures is_on_curve (aff_point_negate p))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:32` | `to_aff_point_at_infinity_lemma:` | explicit/no SMTPat | `val to_aff_point_at_infinity_lemma: unit -> Lemma (to_aff_point point_at_infinity == aff_point_at_infinity)` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:35` | `to_aff_point_add_lemma:` | explicit/no SMTPat | `val to_aff_point_add_lemma: p:ext_point -> q:ext_point -> Lemma (requires point_inv p /\ point_inv q) (ensures (let r = point_add p q in point_inv r /\ to_aff_point r == aff_point_add (to_aff_point p) (to_aff_point q)))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:40` | `to_aff_point_double_lemma:` | explicit/no SMTPat | `val to_aff_point_double_lemma: p:ext_point -> Lemma (requires point_inv p) (ensures (let r = point_double p in point_inv r /\ to_aff_point r == aff_point_double (to_aff_point p) /\ to_aff_point r == aff_point_add (to_aff_point p) (to_aff_point p)))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:46` | `to_aff_point_negate:` | explicit/no SMTPat | `val to_aff_point_negate: p:ext_point -> Lemma (requires point_inv p) (ensures (let r = point_negate p in point_inv r /\ to_aff_point r == aff_point_negate (to_aff_point p)))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:52` | `aff_g_is_on_curve:` | explicit/no SMTPat | `val aff_g_is_on_curve: unit -> Lemma (is_on_curve aff_g)` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:53` | `g_is_on_curve:` | explicit/no SMTPat | `val g_is_on_curve: unit -> Lemma (point_inv g /\ to_aff_point g == aff_g)` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:55` | `point_decompress_lemma:` | explicit/no SMTPat | `val point_decompress_lemma: s:Lib.ByteSequence.lbytes 32 -> Lemma (let p = point_decompress s in Some? p ==> point_inv (Some?.v p))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Ed25519.Lemmas.fsti:58` | `point_equal_lemma:` | explicit/no SMTPat | `val point_equal_lemma: p:ext_point -> q:ext_point -> s:ext_point -> Lemma (requires is_ext p /\ is_ext q /\ is_ext s /\ to_aff_point p == to_aff_point q) (ensures point_equal p s == point_equal q s)` | the proposition/ensures shown |
| `specs/lemmas/Spec.P256.Lemmas.fsti:15` | `prime_lemma:` | explicit/no SMTPat | `val prime_lemma: unit -> Lemma (FStar.Math.Euclid.is_prime prime)` | the proposition/ensures shown |
| `specs/lemmas/Spec.P256.Lemmas.fsti:17` | `lemma_aff_is_point_at_inf:` | explicit/no SMTPat | `val lemma_aff_is_point_at_inf: p:proj_point -> Lemma (let px, py, pz = p in is_aff_point_at_inf (to_aff_point p) == (pz = 0 \|\| (px = 0 && py = 0)))` | the proposition/ensures shown |
| `specs/lemmas/Spec.P256.Lemmas.fsti:22` | `aff_point_at_inf_lemma` | explicit/no SMTPat | `val aff_point_at_inf_lemma (p:aff_point) : Lemma (aff_point_add p aff_point_at_inf = p)` | the proposition/ensures shown |
| `specs/lemmas/Spec.P256.Lemmas.fsti:26` | `aff_point_add_assoc_lemma` | explicit/no SMTPat | `val aff_point_add_assoc_lemma (p q s:aff_point) : Lemma (aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))` | the proposition/ensures shown |
| `specs/lemmas/Spec.P256.Lemmas.fsti:30` | `aff_point_add_comm_lemma` | explicit/no SMTPat | `val aff_point_add_comm_lemma (p q:aff_point) : Lemma (aff_point_add p q = aff_point_add q p)` | the proposition/ensures shown |
| `specs/lemmas/Spec.P256.Lemmas.fsti:34` | `to_aff_point_at_infinity_lemma:` | explicit/no SMTPat | `val to_aff_point_at_infinity_lemma: unit -> Lemma (to_aff_point point_at_inf == aff_point_at_inf)` | the proposition/ensures shown |
| `specs/lemmas/Spec.P256.Lemmas.fsti:38` | `to_aff_point_add_lemma` | explicit/no SMTPat | `val to_aff_point_add_lemma (p q:proj_point) : Lemma (to_aff_point (point_add p q) == aff_point_add (to_aff_point p) (to_aff_point q))` | the proposition/ensures shown |
| `specs/lemmas/Spec.P256.Lemmas.fsti:42` | `to_aff_point_double_lemma` | explicit/no SMTPat | `val to_aff_point_double_lemma (p:proj_point) : Lemma (to_aff_point (point_double p) == aff_point_add (to_aff_point p) (to_aff_point p))` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:10` | `lemma_aff_is_point_at_inf:` | explicit/no SMTPat | `val lemma_aff_is_point_at_inf: p:proj_point -> Lemma (let px, py, pz = p in is_aff_point_at_inf (to_aff_point p) == (pz = 0 \|\| (px = 0 && py = 0)))` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:15` | `lemma_proj_aff_id` | explicit/no SMTPat | `val lemma_proj_aff_id (p:aff_point) : Lemma (to_aff_point (to_proj_point p) == p)` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:19` | `aff_point_at_inf_lemma` | explicit/no SMTPat | `val aff_point_at_inf_lemma (p:aff_point) : Lemma (aff_point_add p aff_point_at_inf = p)` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:23` | `aff_point_add_assoc_lemma` | explicit/no SMTPat | `val aff_point_add_assoc_lemma (p q s:aff_point) : Lemma (aff_point_add (aff_point_add p q) s == aff_point_add p (aff_point_add q s))` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:27` | `aff_point_add_comm_lemma` | explicit/no SMTPat | `val aff_point_add_comm_lemma (p q:aff_point) : Lemma (aff_point_add p q = aff_point_add q p)` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:31` | `aff_point_negate_lemma` | explicit/no SMTPat | `val aff_point_negate_lemma (p:aff_point) : Lemma (aff_point_add (aff_point_negate p) p == aff_point_at_inf)` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:35` | `to_aff_point_at_infinity_lemma:` | explicit/no SMTPat | `val to_aff_point_at_infinity_lemma: unit -> Lemma (to_aff_point point_at_inf == aff_point_at_inf)` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:39` | `to_aff_point_add_lemma` | explicit/no SMTPat | `val to_aff_point_add_lemma (p q:proj_point) : Lemma (to_aff_point (point_add p q) == aff_point_add (to_aff_point p) (to_aff_point q))` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:43` | `to_aff_point_double_lemma` | explicit/no SMTPat | `val to_aff_point_double_lemma (p:proj_point) : Lemma (to_aff_point (point_double p) == aff_point_add (to_aff_point p) (to_aff_point p))` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:47` | `to_aff_point_negate_lemma` | explicit/no SMTPat | `val to_aff_point_negate_lemma (p:proj_point) : Lemma (to_aff_point (point_negate p) == aff_point_negate (to_aff_point p))` | the proposition/ensures shown |
| `specs/lemmas/Spec.K256.Lemmas.fsti:52` | `ecdsa_verify_avoid_finv:` | explicit/no SMTPat | `val ecdsa_verify_avoid_finv: p:proj_point{not (is_proj_point_at_inf p)} -> r:nat{0 < r /\ r < q} -> Lemma (let _X, _Y, _Z = p in (_X /% _Z % q = r) <==> ((r *% _Z = _X) \|\| (r + q < prime && (r + q) *% _Z = _X)))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Curve25519.Lemmas.fst:3` | `lemma_prime_value:` | SMT-pattern | `val lemma_prime_value: n:nat -> Lemma (requires (n = 255)) (ensures (pow2 n - 19 = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed)) [SMTPat (pow2 n - 19)]` | the proposition/ensures shown |
| `specs/lemmas/Spec.Curve25519.Lemmas.fst:9` | `lemma_div_n:` | SMT-pattern | `val lemma_div_n: n:nat -> Lemma (requires (n > 1)) (ensures (n / 2 < n /\ n / 2 > 0)) [SMTPat (n / 2)]` | the proposition/ensures shown |
| `specs/lemmas/Spec.Curve25519.Lemmas.fst:15` | `lemma_pow2_256:` | SMT-pattern | `val lemma_pow2_256: n:nat -> Lemma (requires (n = 256)) (ensures (pow2 n = 0x10000000000000000000000000000000000000000000000000000000000000000)) [SMTPat (pow2 n)]` | the proposition/ensures shown |
| `specs/Spec.FFDHE.fst:509` | `ffdhe_g2_lemma:` | explicit/no SMTPat | `val ffdhe_g2_lemma: unit -> Lemma (nat_from_bytes_be (of_list list_ffdhe_g2) = 2)` | the proposition/ensures shown |
| `specs/Spec.FFDHE.fst:516` | `ffdhe_p_lemma0:` | explicit/no SMTPat | `val ffdhe_p_lemma0: a:ffdhe_alg -> Lemma (let ffdhe_p = get_ffdhe_params a in let len = ffdhe_len a in let p = Mk_ffdhe_params?.ffdhe_p ffdhe_p in Seq.index p (len - 1) == 0xffuy)` | the proposition/ensures shown |
| `specs/Spec.FFDHE.fst:551` | `ffdhe_p_lemma:` | explicit/no SMTPat | `val ffdhe_p_lemma: a:ffdhe_alg -> Lemma (let ffdhe_p = get_ffdhe_params a in let p = Mk_ffdhe_params?.ffdhe_p ffdhe_p in let p_n = nat_from_bytes_be p in p_n % 2 = 1 /\ 255 <= p_n) // 2 < p_n <==> g_n < p_n` | the proposition/ensures shown |
| `specs/Spec.RSAPSS.fst:215` | `os2ip_lemma:` | explicit/no SMTPat | `val os2ip_lemma: emBits:size_pos -> em:lbytes (blocks emBits 8) -> Lemma (requires (if emBits % 8 > 0 then v em.[0] < pow2 (emBits % 8) else v em.[0] < pow2 8)) (ensures os2ip #(blocks emBits 8) em < pow2 emBits)` | the proposition/ensures shown |
| `specs/Spec.Hash.Definitions.fst:109` | `sha2_alg_is_maxed` | SMT-pattern | `let sha2_alg_is_maxed (a: hash_alg): Lemma (requires (is_sha2 a)) (ensures (Some? (max_input_length a))) [ SMTPat (is_sha2 a) ] = ()` | the proposition/ensures shown |
| `specs/Spec.Hash.Definitions.fst:110` | `md_alg_is_maxed` | SMT-pattern | `let md_alg_is_maxed (a: hash_alg): Lemma (requires (is_md a)) (ensures (Some? (max_input_length a))) [ SMTPat (is_md a) ] = ()` | the proposition/ensures shown |
| `specs/Spec.Hash.Definitions.fst:111` | `blake_alg_is_maxed` | SMT-pattern | `let blake_alg_is_maxed (a: hash_alg): Lemma (requires (is_blake a)) (ensures (Some? (max_input_length a))) [ SMTPat (is_blake a) ] = ()` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:96` | `exp_rl_lemma:` | explicit/no SMTPat | `val exp_rl_lemma: #t:Type -> k:concrete_ops t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> Lemma (k.to.refl (exp_rl k a bBits b) == S.exp_rl k.to.comm_monoid (k.to.refl a) bBits b)` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:117` | `exp_mont_ladder_swap_lemma:` | explicit/no SMTPat | `val exp_mont_ladder_swap_lemma: #t:Type -> k:concrete_ops t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> Lemma (k.to.refl (exp_mont_ladder_swap k a bBits b) == S.exp_mont_ladder_swap k.to.comm_monoid (k.to.refl a) bBits b)` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:125` | `exp_pow2_lemma:` | explicit/no SMTPat | `val exp_pow2_lemma: #t:Type -> k:concrete_ops t -> a:t -> b:nat -> Lemma (k.to.refl (exp_pow2 k a b) == S.exp_pow2 k.to.comm_monoid (k.to.refl a) b)` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:135` | `pow_eq0:` | explicit/no SMTPat | `val pow_eq0: #t:Type -> k:concrete_ops t -> a:t -> Lemma (pow k a 0 == k.one ())` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:138` | `pow_unfold:` | explicit/no SMTPat | `val pow_unfold: #t:Type -> k:concrete_ops t -> a:t -> i:pos -> Lemma (pow k a i == k.mul a (pow k a (i - 1)))` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:141` | `pow_lemma:` | explicit/no SMTPat | `val pow_lemma: #t:Type -> k:concrete_ops t -> a:t -> b:nat -> Lemma (k.to.refl (pow k a b) == S.pow k.to.comm_monoid (k.to.refl a) b)` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:172` | `exp_fw_lemma:` | explicit/no SMTPat | `val exp_fw_lemma: #t:Type -> k:concrete_ops t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos -> Lemma (k.to.refl (exp_fw k a bBits b l) == S.exp_fw k.to.comm_monoid (k.to.refl a) bBits b l)` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:211` | `exp_double_fw_lemma:` | explicit/no SMTPat | `val exp_double_fw_lemma: #t:Type -> k:concrete_ops t -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits} -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos -> Lemma (k.to.refl (exp_double_fw k a1 bBits b1 a2 b2 l) == S.exp_double_fw k.to.comm_monoid (k.to.refl a1) bBits b1 (k.to.refl a2) b2 l)` | the proposition/ensures shown |
| `specs/Spec.Exponentiation.fsti:261` | `exp_four_fw_lemma:` | explicit/no SMTPat | `val exp_four_fw_lemma: #t:Type -> k:concrete_ops t -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits} -> a2:t -> b2:nat{b2 < pow2 bBits} -> a3:t -> b3:nat{b3 < pow2 bBits} -> a4:t -> b4:nat{b4 < pow2 bBits} -> l:pos -> Lemma (k.to.refl (exp_four_fw k a1 bBits b1 a2 b2 a3 b3 a4 b4 l) == S.exp_four_fw k.to.comm_monoid (k.to.refl a1) bBits b1 (k.to.refl a2) b2 (k.to.refl a3) b3 (k.to.refl a4) b4 l)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:41` | `lemma_inverse_one:` | explicit/no SMTPat | `val lemma_inverse_one: #t:Type -> k:abelian_group t -> Lemma (inverse k.cm.one == k.cm.one)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:44` | `lemma_inverse_id:` | explicit/no SMTPat | `val lemma_inverse_id: #t:Type -> k:abelian_group t -> a:t -> Lemma (inverse (inverse a) == a)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:47` | `lemma_inverse_mul:` | explicit/no SMTPat | `val lemma_inverse_mul: #t:Type -> k:abelian_group t -> a:t -> b:t -> Lemma (inverse (cm.mul a b) == cm.mul (inverse a) (inverse b))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:53` | `lemma_pow0:` | explicit/no SMTPat | `val lemma_pow0: #t:Type -> k:comm_monoid t -> x:t -> Lemma (pow k x 0 == one)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:55` | `lemma_pow1:` | explicit/no SMTPat | `val lemma_pow1: #t:Type -> k:comm_monoid t -> x:t -> Lemma (pow k x 1 == x)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:57` | `lemma_pow_unfold:` | explicit/no SMTPat | `val lemma_pow_unfold: #t:Type -> k:comm_monoid t -> x:t -> n:pos -> Lemma (mul x (pow k x (n - 1)) == pow k x n)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:61` | `lemma_pow_one:` | explicit/no SMTPat | `val lemma_pow_one: #t:Type -> k:comm_monoid t -> n:nat -> Lemma (pow k one n == one)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:63` | `lemma_pow_add:` | explicit/no SMTPat | `val lemma_pow_add: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat -> Lemma (mul (pow k x n) (pow k x m) == pow k x (n + m))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:66` | `lemma_pow_mul:` | explicit/no SMTPat | `val lemma_pow_mul: #t:Type -> k:comm_monoid t -> x:t -> n:nat -> m:nat -> Lemma (pow k (pow k x n) m == pow k x (n * m))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:69` | `lemma_pow_mul_base:` | explicit/no SMTPat | `val lemma_pow_mul_base: #t:Type -> k:comm_monoid t -> a:t -> b:t -> n:nat -> Lemma (mul (pow k a n) (pow k b n) == pow k (mul a b) n)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:72` | `lemma_pow_double:` | explicit/no SMTPat | `val lemma_pow_double: #t:Type -> k:comm_monoid t -> x:t -> b:nat -> Lemma (pow k (mul x x) b == pow k x (b + b))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:76` | `lemma_inverse_pow:` | explicit/no SMTPat | `val lemma_inverse_pow: #t:Type -> k:abelian_group t -> x:t -> n:nat -> Lemma (inverse (pow cm x n) == pow cm (inverse x) n)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:79` | `lemma_pow_neg_one:` | explicit/no SMTPat | `val lemma_pow_neg_one: #t:Type -> k:abelian_group t -> n:int -> Lemma (pow_neg k cm.one n == cm.one)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:82` | `lemma_pow_neg_add:` | explicit/no SMTPat | `val lemma_pow_neg_add: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma (cm.mul (pow_neg k x n) (pow_neg k x m) == pow_neg k x (n + m))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:85` | `lemma_pow_neg_mul:` | explicit/no SMTPat | `val lemma_pow_neg_mul: #t:Type -> k:abelian_group t -> x:t -> n:int -> m:int -> Lemma (pow_neg k (pow_neg k x n) m == pow_neg k x (n * m))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:88` | `lemma_pow_neg_mul_base:` | explicit/no SMTPat | `val lemma_pow_neg_mul_base: #t:Type -> k:abelian_group t -> a:t -> b:t -> n:int -> Lemma (cm.mul (pow_neg k a n) (pow_neg k b n) == pow_neg k (cm.mul a b) n)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.Definition.fsti:91` | `lemma_pow_neg_double:` | explicit/no SMTPat | `val lemma_pow_neg_double: #t:Type -> k:abelian_group t -> x:t -> b:int -> Lemma (pow_neg k (cm.mul x x) b == pow_neg k x (b + b))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:23` | `exp_rl_lemma:` | explicit/no SMTPat | `val exp_rl_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> Lemma (exp_rl k a bBits b == pow k a b)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:36` | `exp_lr_lemma:` | explicit/no SMTPat | `val exp_lr_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> Lemma (exp_lr k a bBits b == pow k a b)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:51` | `exp_mont_ladder_lemma:` | explicit/no SMTPat | `val exp_mont_ladder_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> Lemma (exp_mont_ladder k a bBits b == pow k a b)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:71` | `exp_mont_ladder_swap2_lemma:` | explicit/no SMTPat | `val exp_mont_ladder_swap2_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> Lemma (exp_mont_ladder_swap2 k a bBits b == exp_mont_ladder k a bBits b)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:88` | `exp_mont_ladder_swap_lemma:` | explicit/no SMTPat | `val exp_mont_ladder_swap_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> Lemma (exp_mont_ladder_swap k a bBits b == exp_mont_ladder k a bBits b)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:96` | `exp_pow2_lemma:` | explicit/no SMTPat | `val exp_pow2_lemma: #t:Type -> k:comm_monoid t -> a:t -> b:nat -> Lemma (exp_pow2 k a b == pow k a (pow2 b))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:126` | `exp_fw_lemma:` | explicit/no SMTPat | `val exp_fw_lemma: #t:Type -> k:comm_monoid t -> a:t -> bBits:nat -> b:nat{b < pow2 bBits} -> l:pos -> Lemma (exp_fw k a bBits b l == pow k a b)` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:158` | `exp_double_fw_lemma:` | explicit/no SMTPat | `val exp_double_fw_lemma: #t:Type -> k:comm_monoid t -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits} -> a2:t -> b2:nat{b2 < pow2 bBits} -> l:pos -> Lemma (exp_double_fw k a1 bBits b1 a2 b2 l == mul (pow k a1 b1) (pow k a2 b2))` | the proposition/ensures shown |
| `lib/Lib.Exponentiation.fsti:202` | `exp_four_fw_lemma:` | explicit/no SMTPat | `val exp_four_fw_lemma: #t:Type -> k:comm_monoid t -> a1:t -> bBits:nat -> b1:nat{b1 < pow2 bBits} -> a2:t -> b2:nat{b2 < pow2 bBits} -> a3:t -> b3:nat{b3 < pow2 bBits} -> a4:t -> b4:nat{b4 < pow2 bBits} -> l:pos -> Lemma (exp_four_fw k a1 bBits b1 a2 b2 a3 b3 a4 b4 l == mul (mul (mul (pow k a1 b1) (pow k a2 b2)) (pow k a3 b3)) (pow k a4 b4))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:24` | `lemma_pow0:` | explicit/no SMTPat | `val lemma_pow0: a:int -> Lemma (pow a 0 = 1)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:25` | `lemma_pow1:` | explicit/no SMTPat | `val lemma_pow1: a:int -> Lemma (pow a 1 = a)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:26` | `lemma_pow_unfold:` | explicit/no SMTPat | `val lemma_pow_unfold: a:int -> b:pos -> Lemma (a * pow a (b - 1) == pow a b)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:28` | `lemma_pow_gt_zero:` | SMT-pattern | `val lemma_pow_gt_zero: a:pos -> b:nat -> Lemma (pow a b > 0) [SMTPat (pow a b)]` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:29` | `lemma_pow_ge_zero:` | SMT-pattern | `val lemma_pow_ge_zero: a:nat -> b:nat -> Lemma (pow a b >= 0) [SMTPat (pow a b)]` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:31` | `lemma_pow_nat_is_pow:` | explicit/no SMTPat | `val lemma_pow_nat_is_pow: a:int -> b:nat -> Lemma (pow a b == LE.pow mk_nat_comm_monoid a b)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:34` | `lemma_pow_zero:` | explicit/no SMTPat | `val lemma_pow_zero: b:pos -> Lemma (pow 0 b = 0)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:36` | `lemma_pow_one:` | explicit/no SMTPat | `val lemma_pow_one: b:nat -> Lemma (pow 1 b = 1)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:38` | `lemma_pow_add:` | explicit/no SMTPat | `val lemma_pow_add: x:int -> n:nat -> m:nat -> Lemma (pow x n * pow x m = pow x (n + m))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:40` | `lemma_pow_mul:` | explicit/no SMTPat | `val lemma_pow_mul: x:int -> n:nat -> m:nat -> Lemma (pow (pow x n) m = pow x (n * m))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:42` | `lemma_pow_double:` | explicit/no SMTPat | `val lemma_pow_double: a:int -> b:nat -> Lemma (pow (a * a) b == pow a (b + b))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:44` | `lemma_pow_mul_base:` | explicit/no SMTPat | `val lemma_pow_mul_base: a:int -> b:int -> n:nat -> Lemma (pow a n * pow b n == pow (a * b) n)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:46` | `lemma_pow_mod_base:` | explicit/no SMTPat | `val lemma_pow_mod_base: a:int -> b:nat -> n:pos -> Lemma (pow a b % n == pow (a % n) b % n)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:57` | `lemma_mul_mod_one:` | explicit/no SMTPat | `val lemma_mul_mod_one: #m:pos -> a:nat_mod m -> Lemma (mul_mod a one_mod == a)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:59` | `lemma_mul_mod_assoc:` | explicit/no SMTPat | `val lemma_mul_mod_assoc: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m -> Lemma (mul_mod (mul_mod a b) c == mul_mod a (mul_mod b c))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:62` | `lemma_mul_mod_comm:` | explicit/no SMTPat | `val lemma_mul_mod_comm: #m:pos -> a:nat_mod m -> b:nat_mod m -> Lemma (mul_mod a b == mul_mod b a)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:82` | `pow_mod_def:` | explicit/no SMTPat | `val pow_mod_def: #m:pos{1 < m} -> a:nat_mod m -> b:nat -> Lemma (pow_mod a b == pow_mod_ a b)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:84` | `lemma_pow_mod:` | explicit/no SMTPat | `val lemma_pow_mod: #m:pos{1 < m} -> a:nat_mod m -> b:nat -> Lemma (pow a b % m == pow_mod #m a b)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:86` | `lemma_pow_nat_mod_is_pow:` | explicit/no SMTPat | `val lemma_pow_nat_mod_is_pow: #n:pos{1 < n} -> a:nat_mod n -> b:nat -> Lemma (pow a b % n == LE.pow (mk_nat_mod_comm_monoid n) a b)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:90` | `lemma_add_mod_one:` | explicit/no SMTPat | `val lemma_add_mod_one: #m:pos -> a:nat_mod m -> Lemma (add_mod a 0 == a)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:92` | `lemma_add_mod_assoc:` | explicit/no SMTPat | `val lemma_add_mod_assoc: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m -> Lemma (add_mod (add_mod a b) c == add_mod a (add_mod b c))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:95` | `lemma_add_mod_comm:` | explicit/no SMTPat | `val lemma_add_mod_comm: #m:pos -> a:nat_mod m -> b:nat_mod m -> Lemma (add_mod a b == add_mod b a)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:99` | `lemma_mod_distributivity_add_right:` | explicit/no SMTPat | `val lemma_mod_distributivity_add_right: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m -> Lemma (mul_mod a (add_mod b c) == add_mod (mul_mod a b) (mul_mod a c))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:102` | `lemma_mod_distributivity_add_left:` | explicit/no SMTPat | `val lemma_mod_distributivity_add_left: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m -> Lemma (mul_mod (add_mod a b) c == add_mod (mul_mod a c) (mul_mod b c))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:105` | `lemma_mod_distributivity_sub_right:` | explicit/no SMTPat | `val lemma_mod_distributivity_sub_right: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m -> Lemma (mul_mod a (sub_mod b c) == sub_mod (mul_mod a b) (mul_mod a c))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:108` | `lemma_mod_distributivity_sub_left:` | explicit/no SMTPat | `val lemma_mod_distributivity_sub_left: #m:pos -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m -> Lemma (mul_mod (sub_mod a b) c == sub_mod (mul_mod a c) (mul_mod b c))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:116` | `lemma_inv_mod_both:` | explicit/no SMTPat | `val lemma_inv_mod_both: #m:pos{1 < m} -> a:nat_mod m -> b:nat_mod m -> Lemma (inv_mod (mul_mod a b) == mul_mod (inv_mod a) (inv_mod b))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:119` | `lemma_div_mod_prime:` | explicit/no SMTPat | `val lemma_div_mod_prime: #m:prime -> a:nat_mod m{a <> 0} -> Lemma (div_mod a a == 1)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:120` | `lemma_div_mod_prime_one:` | explicit/no SMTPat | `val lemma_div_mod_prime_one: #m:pos{1 < m} -> a:nat_mod m -> Lemma (div_mod a 1 == a)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:122` | `lemma_div_mod_prime_cancel:` | explicit/no SMTPat | `val lemma_div_mod_prime_cancel: #m:prime -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m{c <> 0} -> Lemma (div_mod (mul_mod a c) (mul_mod c b) == div_mod a b)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:125` | `lemma_div_mod_prime_to_one_denominator:` | explicit/no SMTPat | `val lemma_div_mod_prime_to_one_denominator: #m:pos{1 < m} -> a:nat_mod m -> b:nat_mod m -> c:nat_mod m{c <> 0} -> d:nat_mod m{d <> 0} -> Lemma (mul_mod (div_mod a c) (div_mod b d) == div_mod (mul_mod a b) (mul_mod c d))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:129` | `lemma_div_mod_eq_mul_mod:` | explicit/no SMTPat | `val lemma_div_mod_eq_mul_mod: #m:prime -> a:nat_mod m -> b:nat_mod m{b <> 0} -> c:nat_mod m -> Lemma ((div_mod a b = c) == (a = mul_mod c b))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:132` | `lemma_mul_mod_prime_zero:` | explicit/no SMTPat | `val lemma_mul_mod_prime_zero: #m:prime -> a:nat_mod m -> b:nat_mod m -> Lemma (a * b % m == 0 <==> (a % m == 0 \/ b % m == 0))` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:135` | `lemma_pow_mod_prime_zero:` | explicit/no SMTPat | `val lemma_pow_mod_prime_zero: #m:prime -> a:nat_mod m -> b:pos -> Lemma (pow_mod #m a b = 0 <==> a = 0)` | the proposition/ensures shown |
| `lib/Lib.NatMod.fsti:138` | `lemma_div_mod_prime_is_zero:` | explicit/no SMTPat | `val lemma_div_mod_prime_is_zero: #m:prime{2 < m} -> a:nat_mod m -> b:nat_mod m -> Lemma ((div_mod a b = 0) <==> (a = 0 \|\| b = 0))` | the proposition/ensures shown |
| `specs/lemmas/Spec.Blake2.Alternative.fsti:20` | `lemma_spec_equivalence_update:` | explicit/no SMTPat | `val lemma_spec_equivalence_update: a:alg -> last_node:bool -> kk:size_nat{kk <= max_key a} -> k:lbytes kk -> d:bytes{if kk = 0 then length d <= max_limb a else length d + (size_block a) <= max_limb a} -> s:state a -> Lemma (blake2_update a last_node kk k d s `Seq.equal` blake2_update' a last_node kk k d s)` | the proposition/ensures shown |
| `specs/lemmas/Spec.Blake2.Incremental.fsti:9` | `blake2_is_hash_incremental` | explicit/no SMTPat | `val blake2_is_hash_incremental (a : blake_alg) (input : bytes {S.length input `less_than_max_input_length` a}) : Lemma ( S.equal (Spec.Blake2.blake2 (to_blake_alg a) false input (Spec.Blake2.blake2_default_params (to_blake_alg a)) Seq.empty) (hash_incremental a input ()))` | the proposition/ensures shown |
| `specs/lemmas/Spec.MD.Incremental.fsti:13` | `md_is_hash_incremental` | explicit/no SMTPat | `val md_is_hash_incremental (a:hash_alg{is_md a}) (input: bytes { S.length input `less_than_max_input_length` a }) (s:words_state a) : Lemma ( let blocks, rest = split_blocks a input in update_multi a s () (input `S.append` (pad a (S.length input))) == update_last a (update_multi a s () blocks) (S.length blocks) rest)` | the proposition/ensures shown |
| `specs/lemmas/Spec.SHA2.Lemmas.fsti:7` | `update_224_256:` | explicit/no SMTPat | `val update_224_256: st:words_state SHA2_256 -> block:bytes{Seq.length block = block_length SHA2_256} -> Lemma (ensures (Spec.Agile.Hash.(update SHA2_256 st block == update SHA2_224 st block)))` | the proposition/ensures shown |
| `specs/lemmas/Spec.SHA2.Lemmas.fsti:12` | `update_multi_224_256:` | explicit/no SMTPat | `val update_multi_224_256: hash:words_state SHA2_256 -> blocks:bytes_blocks SHA2_256 -> Lemma (ensures (Spec.Agile.Hash.update_multi SHA2_256 hash () blocks == Spec.Agile.Hash.update_multi SHA2_224 hash () blocks)) (decreases (Seq.length blocks))` | the proposition/ensures shown |
| `specs/lemmas/Spec.SHA2.Lemmas.fsti:18` | `update_last_224_256:` | explicit/no SMTPat | `val update_last_224_256: hash:words_state SHA2_256 -> prevlen:Spec.Hash.Incremental.Definitions.prev_length_t SHA2_256 -> input:bytes{ (Seq.length input + prevlen) `less_than_max_input_length` SHA2_256 /\ Seq.length input <= block_length SHA2_256 } -> Lemma (ensures Spec.Hash.Incremental.Definitions.update_last SHA2_256 hash prevlen input == Spec.Hash.Incremental.Definitions.update_last SHA2_224 hash prevlen input)` | the proposition/ensures shown |
| `specs/lemmas/Spec.SHA2.Lemmas.fsti:28` | `update_384_512:` | explicit/no SMTPat | `val update_384_512: st:words_state SHA2_512 -> block:bytes{Seq.length block = block_length SHA2_512} -> Lemma (ensures (Spec.Agile.Hash.(update SHA2_512 st block == update SHA2_384 st block)))` | the proposition/ensures shown |
| `specs/lemmas/Spec.SHA2.Lemmas.fsti:33` | `update_multi_384_512:` | explicit/no SMTPat | `val update_multi_384_512: hash:words_state SHA2_512 -> blocks:bytes_blocks SHA2_512 -> Lemma (ensures (Spec.Agile.Hash.update_multi SHA2_512 hash () blocks == Spec.Agile.Hash.update_multi SHA2_384 hash () blocks)) (decreases (Seq.length blocks))` | the proposition/ensures shown |
| `specs/lemmas/Spec.SHA2.Lemmas.fsti:39` | `update_last_384_512:` | explicit/no SMTPat | `val update_last_384_512: hash:words_state SHA2_512 -> prevlen:Spec.Hash.Incremental.Definitions.prev_length_t SHA2_512 -> input:bytes{ (Seq.length input + prevlen) `less_than_max_input_length` SHA2_512 /\ Seq.length input <= block_length SHA2_512 } -> Lemma (ensures Spec.Hash.Incremental.Definitions.update_last SHA2_512 hash prevlen input == Spec.Hash.Incremental.Definitions.update_last SHA2_384 hash prevlen input)` | the proposition/ensures shown |
| `specs/lemmas/Spec.SHA3.Incremental.fsti:9` | `sha3_is_incremental` | explicit/no SMTPat | `val sha3_is_incremental (a: keccak_alg) (input: bytes) (l: output_length a): Lemma (hash_incremental a input l `S.equal` hash' a input l)` | the proposition/ensures shown |
## 5. Per-algorithm spec entry points
| Algorithm/family | Module | Main spec functions | References |
|---|---|---|---|
| Agile hash | `Spec.Agile.Hash` | `hash`, `hash'`, `init`, `update_multi`, `finish` | `specs/Spec.Agile.Hash.fsti:54-77` |
| Agile AEAD | `Spec.Agile.AEAD` | `encrypt`, `decrypt`, `correctness` | `specs/Spec.Agile.AEAD.fsti:122-126` |
| HMAC/HKDF | `Spec.Agile.HMAC`, `Spec.Agile.HKDF` | `hmac`, `extract`, `expand` | `specs/Spec.Agile.HMAC.fsti:22-31`, `specs/Spec.Agile.HKDF.fsti:8-35` |
| Cipher/DH/HPKE | `Spec.Agile.Cipher`, `Spec.Agile.DH`, `Spec.Agile.HPKE` | `ctr_block`, `ctr_stream`, `dh`, `secret_to_public`, `seal*`, `open*` | section 3 |
| Monomorphic algorithms | `Spec.SHA2`, `Spec.SHA3`, `Spec.Blake2`, `Spec.Chacha20`, `Spec.Poly1305`, curves, RSA, FFDHE, boxes | algorithm-specific functions | below |

### Exact monomorphic signatures
| Source | Name | Exact declaration |
|---|---|---|
| `specs/Spec.SHA2.fsti:5` | `init:` | `val init: a:sha2_alg -> init_t a` |
| `specs/Spec.SHA2.fsti:7` | `update:` | `val update: a:sha2_alg -> update_t a` |
| `specs/Spec.SHA3.fst:187` | `keccak:` | `val keccak: rate:size_nat{rate % 8 == 0 /\ rate / 8 > 0 /\ rate <= 1600} -> capacity:size_nat{capacity + rate == 1600} -> inputByteLen:nat -> input:bytes{length input == inputByteLen} -> delimitedSuffix:byte_t -> outputByteLen:size_nat -> Tot (lbytes outputByteLen)` |
| `specs/Spec.SHA3.fst:202` | `shake128` | `let shake128 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) (outputByteLen:size_nat) : Tot (lbytes outputByteLen) =` |
| `specs/Spec.SHA3.fst:210` | `shake256` | `let shake256 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) (outputByteLen:size_nat) : Tot (lbytes outputByteLen) =` |
| `specs/Spec.SHA3.fst:218` | `sha3_224` | `let sha3_224 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) : lbytes 28 =` |
| `specs/Spec.SHA3.fst:221` | `sha3_256` | `let sha3_256 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) : lbytes 32 =` |
| `specs/Spec.SHA3.fst:224` | `sha3_384` | `let sha3_384 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) : lbytes 48 =` |
| `specs/Spec.SHA3.fst:227` | `sha3_512` | `let sha3_512 (inputByteLen:nat) (input:bytes{length input == inputByteLen}) : lbytes 64 =` |
| `specs/Spec.Blake2.fst:456` | `blake2:` | `val blake2: a:alg -> last_node: bool -> d:bytes -> p:blake2_params a { let kk = p.key_length in if kk = 0uy then length d <= max_limb a else length d + (size_block a) <= max_limb a } -> k:lbytes (UInt8.v p.key_length) -> Tot (lbytes (UInt8.v p.digest_length))` |
| `specs/Spec.Blake2.fst:475` | `blake2s:` | `val blake2s: d:bytes -> kk:size_nat{kk <= 32 /\ (if kk = 0 then length d < pow2 64 else length d + 64 < pow2 64)} -> k:lbytes kk -> nn:size_nat{1 <= nn /\ nn <= 32} -> Tot (lbytes nn)` |
| `specs/Spec.Blake2.fst:484` | `blake2b:` | `val blake2b: d:bytes -> kk:size_nat{kk <= 64 /\ (if kk = 0 then length d < pow2 128 else length d + 128 < pow2 128)} -> k:lbytes kk -> nn:size_nat{1 <= nn /\ nn <= 64} -> Tot (lbytes nn)` |
| `specs/Spec.Chacha20.fst:158` | `chacha20_update:` | `val chacha20_update: ctx: state -> msg: bytes{length msg / size_block <= max_size_t} -> cipher: bytes{length cipher == length msg}` |
| `specs/Spec.Chacha20.fst:170` | `chacha20_encrypt_bytes:` | `val chacha20_encrypt_bytes: k: key -> n: nonce -> c: counter -> msg: bytes{length msg / size_block <= max_size_t} -> cipher: bytes{length cipher == length msg}` |
| `specs/Spec.Poly1305.fst:74` | `poly1305_mac` | `let poly1305_mac (msg:bytes) (k:key) : Tot tag =` |
| `specs/Spec.Chacha20Poly1305.fst:62` | `aead_encrypt:` | `val aead_encrypt: k:key -> n:nonce -> m:bytes{length m <= max_size_t} -> aad:bytes{length aad <= maxint U64} -> Tot (res:bytes{length res == length m + Poly.size_block})` |
| `specs/Spec.Chacha20Poly1305.fst:75` | `aead_decrypt:` | `val aead_decrypt: k:key -> n:nonce -> c:bytes{length c <= max_size_t} -> mac:tag -> aad:bytes{length aad <= maxint U64} -> Tot (option (lbytes (length c)))` |
| `specs/Spec.Curve25519.fst:120` | `scalarmult` | `let scalarmult (k:scalar) (u:serialized_point) : Tot serialized_point =` |
| `specs/Spec.Curve25519.fst:139` | `secret_to_public:` | `val secret_to_public: lbytes 32 -> lbytes 32` |
| `specs/Spec.Ed25519.fst:111` | `secret_to_public` | `let secret_to_public (secret:lbytes 32) : lbytes 32 =` |
| `specs/Spec.Ed25519.fst:133` | `sign:` | `val sign: secret:lbytes 32 -> msg:bytes{length msg <= max_size_t} -> lbytes 64` |
| `specs/Spec.Ed25519.fst:139` | `verify:` | `val verify: public:lbytes 32 -> msg:bytes{length msg <= max_size_t} -> signature:lbytes 64 -> bool` |
| `specs/Spec.P256.fst:144` | `ecdsa_signature_agile:` | `val ecdsa_signature_agile: alg:hash_alg_ecdsa -> msg_len:size_nat{msg_len >= min_input_length alg} -> msg:lbytes msg_len -> private_key:lbytes 32 -> nonce:lbytes 32 -> option (lbytes 64)` |
| `specs/Spec.P256.fst:158` | `ecdsa_verification_agile:` | `val ecdsa_verification_agile: alg:hash_alg_ecdsa -> msg_len:size_nat{msg_len >= min_input_length alg} -> msg:lbytes msg_len -> public_key:lbytes 64 -> signature_r:lbytes 32 -> signature_s:lbytes 32 -> bool` |
| `specs/Spec.P256.fst:175` | `secret_to_public` | `let secret_to_public (private_key:lbytes 32) : option (lbytes 64) =` |
| `specs/Spec.P256.fst:184` | `ecdh` | `let ecdh (their_public_key:lbytes 64) (private_key:lbytes 32) : option (lbytes 64) =` |
| `specs/Spec.K256.fst:85` | `ecdsa_sign_hashed_msg` | `let ecdsa_sign_hashed_msg (msgHash private_key nonce:lbytes 32) : option (lbytes 64) =` |
| `specs/Spec.K256.fst:108` | `ecdsa_verify_hashed_msg` | `let ecdsa_verify_hashed_msg (msgHash:lbytes 32) (public_key signature:lbytes 64) : bool =` |
| `specs/Spec.K256.fst:145` | `ecdsa_sign_sha256` | `let ecdsa_sign_sha256 (msg_len:size_nat) (msg:lbytes msg_len) (private_key nonce:lbytes 32) : option (lbytes 64) =` |
| `specs/Spec.K256.fst:150` | `ecdsa_verify_sha256` | `let ecdsa_verify_sha256 (msg_len:size_nat) (msg:lbytes msg_len) (public_key signature:lbytes 64) : bool =` |
| `specs/Spec.K256.fst:157` | `secret_to_public` | `let secret_to_public (private_key:lbytes 32) : option (lbytes 64) =` |
| `specs/Spec.K256.fst:166` | `ecdh` | `let ecdh (their_public_key:lbytes 64) (private_key:lbytes 32) : option (lbytes 64) =` |
| `specs/Spec.RSAPSS.fst:283` | `rsapss_sign:` | `val rsapss_sign: a:Hash.hash_alg{hash_is_supported a} -> modBits:modBits_t -> skey:rsapss_skey modBits -> sLen:size_nat -> salt:lbytes sLen -> msgLen:nat -> msg:bytes{length msg == msgLen} -> option (lbytes (blocks modBits 8))` |
| `specs/Spec.RSAPSS.fst:338` | `rsapss_verify:` | `val rsapss_verify: a:Hash.hash_alg{hash_is_supported a} -> modBits:modBits_t -> pkey:rsapss_pkey modBits -> sLen:size_nat -> k:size_nat -> sgnt:lbytes k -> msgLen:nat -> msg:bytes{length msg == msgLen} -> Tot bool` |
| `specs/Spec.FFDHE.fst:575` | `ffdhe_secret_to_public:` | `val ffdhe_secret_to_public: a:ffdhe_alg -> sk:ffdhe_sk_t a -> lseq uint8 (ffdhe_len a)` |
| `specs/Spec.FFDHE.fst:596` | `ffdhe_shared_secret:` | `val ffdhe_shared_secret: a:ffdhe_alg -> sk:ffdhe_sk_t a -> pk:lseq uint8 (ffdhe_len a) -> option (lseq uint8 (ffdhe_len a))` |
| `specs/Spec.SecretBox.fst:75` | `secretbox_easy` | `let secretbox_easy (k:key) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : c:bytes{length c = size_tag + length m} =` |
| `specs/Spec.SecretBox.fst:79` | `secretbox_open_easy` | `let secretbox_open_easy (k:key) (n:nonce) (c:bytes{length c >= size_tag /\ (length c - size_tag) / size_block <= max_size_t}) : option (m:bytes{length m = length c - size_tag}) =` |
| `specs/Spec.Box.fst:61` | `box_easy` | `let box_easy (sk:secretkey) (pk:publickey) (n:nonce) (m:bytes{length m / size_block <= max_size_t}) : option (c:bytes{length c = size_tag + length m}) =` |
| `specs/Spec.Box.fst:74` | `box_open_easy` | `let box_open_easy (pk:secretkey) (sk:publickey) (n:nonce) (c:bytes{length c >= size_tag /\ (length c - size_tag) / size_block <= max_size_t}) : option (m:bytes{length m = length c - size_tag}) =` |
## 6. Notes for reimplementers
- Specs are executable/testable: main definitions are `Tot` or `Pure` over sequences and integers.
- Preserve `noextract`/`inline_for_extraction` discipline.
- Preserve agile vs monomorphic boundaries and all length/key/nonce/tag/refinement types.
- Treat assumed curve lemmas as proof obligations.
- Do not invent missing theorems; sign/verify correctness and DH/ECDH commutativity are absent as exposed top-level lemmas in this snapshot.
