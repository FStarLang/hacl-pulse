(*
   Copyright 2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

(** AES-128 and AES-256, as specified in FIPS 197.

    {2 What is and is not here}

    Only the {i cipher} is specified: [InvSubBytes], [InvShiftRows],
    [InvMixColumns] and the inverse cipher are absent.  Nothing this library
    builds on AES needs them.  AES-GCM, like every other modern mode, uses AES
    only to produce a keystream, so both encryption and decryption call the
    forward cipher; the inverse cipher is needed only by ECB and CBC, which
    this library does not offer and should not.

    AES-192 is absent for a different reason: no protocol asks for it, HACL*
    and EverCrypt do not expose it, and its key schedule is the one case where
    the expansion step does not line up with the block boundary.  Adding it
    later is a matter of admitting [nk = 6]; nothing here is specialized to
    the two sizes beyond the [variant] type.

    {2 Bytes as numbers}

    AES is specified here on sequences of {i numbers} below 256 rather than on
    secret bytes, for the reasons [Spec.Byte] gives; [Spec.Byte.vals] is the
    view that connects the two.

    {2 The S-box}

    [sbox] is the table from FIPS 197 figure 7, and [sbox_is_algebraic] proves
    that it is the composition of inversion in GF(2^8) with the affine map of
    5.1.1 -- 256 cases, discharged by normalization.  That makes the table
    auditable without trusting a transcription: an error in any of the 256
    entries fails the lemma.  The implementation uses neither the table nor
    the algebraic definition -- a table lookup on a secret index is exactly
    the cache-timing attack AES is famous for -- but it has to be proved equal
    to one of them, and the table is the cheaper target.

    {2 How this file was checked}

    Running the specification inside F* is not practical: it is written on
    [FStar.Seq], and the normalizer unfolds sequence operations far too slowly
    to push a block through fourteen rounds.  So the specification was checked
    the way [Spec.HMAC_DRBG] was -- transliterated line by line into Python
    and run against FIPS 197 appendices B and C (AES-128 and AES-256 block
    encryption), A.1 (the key schedule) and SP 800-38A F.5.1 (counter mode).
    The C tests close the loop from the other end, since the implementation
    carries a proof that it computes what is written here. *)
module Spec.AES

module Seq = FStar.Seq
module UInt = FStar.UInt
module U8 = FStar.UInt8
module UInt32 = FStar.UInt32
module List = FStar.List.Tot
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module SZ = FStar.SizeT

open Spec.Byte

(** {2 GF(2^8)}

    The field is F2[x] / (x^8 + x^4 + x^3 + x + 1); an element is the eight
    coefficients read as a binary number, so [0x1b] is the low part of the
    reduction polynomial. *)

(** Multiplication by [x].  The shift can leave the field, and then the
    modulus is subtracted -- which, the characteristic being two, is the same
    xor as everywhere else. *)
let xtime (a: elem) : elem =
  let s : elem = (2 * a) % 256 in
  if a < 128 then s else s ^^ 0x1b

(** [fmul a b], by the schoolbook method: [b]'s bits select shifted copies
    of [a].  The recursion is on a step count rather than on [b] so that it is
    structurally obvious that there are eight steps and no more. *)
let rec fmul_aux (a b: elem) (n: nat { n <= 8 }) : Tot elem (decreases n) =
  if n = 0 then 0
  else
    let r = fmul_aux (xtime a) (b / 2) (n - 1) in
    if b % 2 = 1 then a ^^ r else r

let fmul (a b: elem) : elem = fmul_aux a b 8

(** Exponentiation by squaring, used only to state what the S-box is. *)
let rec fexp (a: elem) (n: nat) : Tot elem (decreases n) =
  if n = 0 then 1
  else
    let h = fexp a (n / 2) in
    let s = fmul h h in
    if n % 2 = 1 then fmul s a else s

(** The multiplicative inverse, with zero mapped to zero as FIPS 197 asks.
    The group has order 255, so [a^254] is [a^-1]. *)
let ginv (a: elem) : elem = if a = 0 then 0 else fexp a 254

(** FIPS 197 5.1.1's affine transformation:
    [b_i' = b_i ^ b_(i+4) ^ b_(i+5) ^ b_(i+6) ^ b_(i+7) ^ c_i] with
    [c = 0x63], which is five rotations and a constant. *)
let affine (b: elem) : elem =
  b ^^ rotl8 b 1 ^^ rotl8 b 2 ^^ rotl8 b 3 ^^ rotl8 b 4 ^^ 0x63

(** {2 The S-box} *)

(* Opaque to the solver: a 256-element literal in the SMT context makes every
   query that so much as mentions the S-box enormous, including ones that have
   nothing to say about it.  Nothing outside this file needs to see it -- the
   two lemmas below say all there is to say. *)
[@@ "opaque_to_smt"]
let sbox_list : list elem = [
  0x63; 0x7c; 0x77; 0x7b; 0xf2; 0x6b; 0x6f; 0xc5;
  0x30; 0x01; 0x67; 0x2b; 0xfe; 0xd7; 0xab; 0x76;
  0xca; 0x82; 0xc9; 0x7d; 0xfa; 0x59; 0x47; 0xf0;
  0xad; 0xd4; 0xa2; 0xaf; 0x9c; 0xa4; 0x72; 0xc0;
  0xb7; 0xfd; 0x93; 0x26; 0x36; 0x3f; 0xf7; 0xcc;
  0x34; 0xa5; 0xe5; 0xf1; 0x71; 0xd8; 0x31; 0x15;
  0x04; 0xc7; 0x23; 0xc3; 0x18; 0x96; 0x05; 0x9a;
  0x07; 0x12; 0x80; 0xe2; 0xeb; 0x27; 0xb2; 0x75;
  0x09; 0x83; 0x2c; 0x1a; 0x1b; 0x6e; 0x5a; 0xa0;
  0x52; 0x3b; 0xd6; 0xb3; 0x29; 0xe3; 0x2f; 0x84;
  0x53; 0xd1; 0x00; 0xed; 0x20; 0xfc; 0xb1; 0x5b;
  0x6a; 0xcb; 0xbe; 0x39; 0x4a; 0x4c; 0x58; 0xcf;
  0xd0; 0xef; 0xaa; 0xfb; 0x43; 0x4d; 0x33; 0x85;
  0x45; 0xf9; 0x02; 0x7f; 0x50; 0x3c; 0x9f; 0xa8;
  0x51; 0xa3; 0x40; 0x8f; 0x92; 0x9d; 0x38; 0xf5;
  0xbc; 0xb6; 0xda; 0x21; 0x10; 0xff; 0xf3; 0xd2;
  0xcd; 0x0c; 0x13; 0xec; 0x5f; 0x97; 0x44; 0x17;
  0xc4; 0xa7; 0x7e; 0x3d; 0x64; 0x5d; 0x19; 0x73;
  0x60; 0x81; 0x4f; 0xdc; 0x22; 0x2a; 0x90; 0x88;
  0x46; 0xee; 0xb8; 0x14; 0xde; 0x5e; 0x0b; 0xdb;
  0xe0; 0x32; 0x3a; 0x0a; 0x49; 0x06; 0x24; 0x5c;
  0xc2; 0xd3; 0xac; 0x62; 0x91; 0x95; 0xe4; 0x79;
  0xe7; 0xc8; 0x37; 0x6d; 0x8d; 0xd5; 0x4e; 0xa9;
  0x6c; 0x56; 0xf4; 0xea; 0x65; 0x7a; 0xae; 0x08;
  0xba; 0x78; 0x25; 0x2e; 0x1c; 0xa6; 0xb4; 0xc6;
  0xe8; 0xdd; 0x74; 0x1f; 0x4b; 0xbd; 0x8b; 0x8a;
  0x70; 0x3e; 0xb5; 0x66; 0x48; 0x03; 0xf6; 0x0e;
  0x61; 0x35; 0x57; 0xb9; 0x86; 0xc1; 0x1d; 0x9e;
  0xe1; 0xf8; 0x98; 0x11; 0x69; 0xd9; 0x8e; 0x94;
  0x9b; 0x1e; 0x87; 0xe9; 0xce; 0x55; 0x28; 0xdf;
  0x8c; 0xa1; 0x89; 0x0d; 0xbf; 0xe6; 0x42; 0x68;
  0x41; 0x99; 0x2d; 0x0f; 0xb0; 0x54; 0xbb; 0x16
]

let sbox_len () : Lemma (List.length sbox_list == 256) =
  assert_norm (List.length sbox_list == 256)

let sbox_seq : Seq.lseq elem 256 =
  sbox_len ();
  Seq.seq_of_list sbox_list

let sbox (x: elem) : elem =
  assert_norm (pow2 8 == 256);
  Seq.index sbox_seq x

(** {3 The table is the algebraic definition}

    Checking all 256 entries is a job for the normalizer, but it will not
    enumerate a [forall] over a refinement of [int], so the check is phrased
    as a recursion down the literal list -- which the normalizer {i will}
    unfold -- and then transported to an indexed statement by an induction of
    the same shape.  [assert_norm] then has 256 evaluations of [affine (ginv
    x)] to do and no quantifier to reason about. *)

(** [affine (ginv i)], total in [i], so that the recursion below can carry a
    plain [nat] index and still walk off the end of the table. *)
let gsbox (i: nat) : elem = if i < 256 then affine (ginv i) else 0

let rec sbox_ok (l: list elem) (i: nat) : Tot bool (decreases l) =
  match l with
  | [] -> true
  | h :: t -> (h = gsbox i) && sbox_ok t (i + 1)

let rec sbox_ok_index (l: list elem) (i: nat) (j: nat { j < List.length l })
  : Lemma (requires sbox_ok l i)
          (ensures List.index l j == gsbox (i + j))
          (decreases l)
  = match l with
    | h :: t -> if j = 0 then () else sbox_ok_index t (i + 1) (j - 1)

let sbox_is_algebraic (x: elem)
  : Lemma (sbox x == affine (ginv x))
  = assert_norm (sbox_ok sbox_list 0);
    sbox_len ();
    assert_norm (pow2 8 == 256);
    sbox_ok_index sbox_list 0 x;
    Seq.lemma_seq_of_list_index sbox_list x

(** {2 The state}

    FIPS 197's state is a four-by-four matrix of bytes filled column by
    column, so byte [4c + r] of the input is row [r] of column [c].  Only
    ShiftRows cares, and it is easier to read as an index permutation on the
    flat sixteen bytes than as a matrix. *)

unfold let blocklen = 16

type block = Seq.lseq elem blocklen

let xor_block (a b: block) : block =
  Seq.init blocklen (fun i -> Seq.index a i ^^ Seq.index b i)

let add_round_key (st: block) (k: block) : block = xor_block st k

let sub_bytes (st: block) : block =
  Seq.init blocklen (fun i -> sbox (Seq.index st i))

(** Row [r] moves left by [r] columns: the byte at row [r] of column [c]
    comes from row [r] of column [c + r]. *)
let shift_rows (st: block) : block =
  Seq.init blocklen (fun i ->
    let r = i % 4 in
    let c = i / 4 in
    Seq.index st (4 * ((c + r) % 4) + r))

(** The MixColumns matrix, one output byte at a time.  Row [r] of the matrix
    is [(2 3 1 1)] rotated right by [r], so the coefficient multiplying input
    row [j] of the column is entry [(j - r) mod 4] of [(2 3 1 1)]. *)
let mix_coeff (k: nat { k < 4 }) : elem =
  if k = 0 then 2 else if k = 1 then 3 else 1

let mix_columns (st: block) : block =
  Seq.init blocklen (fun i ->
    let r = i % 4 in
    let c = i / 4 in
    let term (j: nat { j < 4 }) : elem =
      fmul (mix_coeff ((j + 4 - r) % 4)) (Seq.index st (4 * c + j)) in
    term 0 ^^ term 1 ^^ term 2 ^^ term 3)

(** {2 The key schedule} *)

type variant = | AES128 | AES256

let nk (v: variant) : n: pos { n == 4 \/ n == 8 } =
  match v with | AES128 -> 4 | AES256 -> 8

let nr (v: variant) : n: pos { n == 10 \/ n == 14 } =
  match v with | AES128 -> 10 | AES256 -> 14

let keylen (v: variant) : n: pos { n == 16 \/ n == 32 } = 4 * nk v

let xkeylen (v: variant) : pos = 16 * (nr v + 1)

(** The implementation is specialized to one variant at a time, and follows
    the house style of [Spec.SHA2]: a record of [SizeT.t] fields, passed as a
    monomorphized argument, so that no [Prims.int] survives into the code and
    Custard produces one C function per variant.  The refinements carry the
    connection back to the definitions above, so nothing has to be re-proved
    at the call sites. *)
noeq type params = {
  pv: variant;
  pnk: (n: SZ.t { SZ.v n == nk pv });
  pnr: (n: SZ.t { SZ.v n == nr pv });
  pkeylen: (n: SZ.t { SZ.v n == keylen pv });
  pxkeylen: (n: SZ.t { SZ.v n == xkeylen pv });
}

let params128 : params =
  { pv = AES128; pnk = 4sz; pnr = 10sz; pkeylen = 16sz; pxkeylen = 176sz }

let params256 : params =
  { pv = AES256; pnk = 8sz; pnr = 14sz; pkeylen = 32sz; pxkeylen = 240sz }

type word = Seq.lseq elem 4

let xor_word (a b: word) : word =
  Seq.init 4 (fun i -> Seq.index a i ^^ Seq.index b i)

let rot_word (a: word) : word =
  Seq.init 4 (fun i -> Seq.index a ((i + 1) % 4))

let sub_word (a: word) : word =
  Seq.init 4 (fun i -> sbox (Seq.index a i))

(** The round constants are [x^(j-1)] in GF(2^8), in the first byte. *)
let rec rcon (j: pos) : Tot elem (decreases j) =
  if j = 1 then 1 else xtime (rcon (j - 1))

let rcon_word (j: pos) : word =
  Seq.init 4 (fun i -> (if i = 0 then rcon j else 0) <: elem)

(** Word [i] of the expanded key.  Below [nk] it is the key itself; above, it
    is the word [nk] back xored with a transform of the word just before --
    with a rotation, a substitution and a round constant at each multiple of
    [nk], and, for AES-256 only, a bare substitution halfway between. *)
let rec ks_word (v: variant) (key: Seq.lseq elem (keylen v)) (i: nat)
  : Tot word (decreases i) =
  if i < nk v then Seq.slice key (4 * i) (4 * i + 4)
  else
    let prev = ks_word v key (i - 1) in
    let temp =
      if i % nk v = 0 then xor_word (sub_word (rot_word prev)) (rcon_word (i / nk v))
      else if nk v > 6 && i % nk v = 4 then sub_word prev
      else prev in
    xor_word (ks_word v key (i - nk v)) temp

(** Opaque to the solver: unfolded, this is a [Seq.init] whose body divides
    the index, so any hypothesis quantified over indices would spawn a fresh
    [ks_word] term for each of them and drown an implementation's query.
    [key_expansion_index] is the only way in. *)
[@@ "opaque_to_smt"]
let key_expansion (v: variant) (key: Seq.lseq elem (keylen v))
  : Seq.lseq elem (xkeylen v) =
  Seq.init (xkeylen v) (fun j -> Seq.index (ks_word v key (j / 4)) (j % 4))

let key_expansion_index (v: variant) (key: Seq.lseq elem (keylen v))
                        (j: nat { j < xkeylen v })
  : Lemma (Seq.index (key_expansion v key) j ==
           Seq.index (ks_word v key (j / 4)) (j % 4))
  = reveal_opaque (`%key_expansion) key_expansion

(** {2 The cipher} *)

let round_key (v: variant) (w: Seq.lseq elem (xkeylen v)) (i: nat { i <= nr v })
  : block = Seq.slice w (16 * i) (16 * i + 16)

let round (k: block) (st: block) : block =
  add_round_key (mix_columns (shift_rows (sub_bytes st))) k

(** The last round omits MixColumns, which is what makes the cipher and its
    inverse the same shape. *)
let last_round (k: block) (st: block) : block =
  add_round_key (shift_rows (sub_bytes st)) k

let rec rounds (v: variant) (w: Seq.lseq elem (xkeylen v)) (st: block)
               (i: nat { 1 <= i /\ i <= nr v })
  : Tot block (decreases (nr v - i)) =
  if i = nr v then last_round (round_key v w i) st
  else rounds v w (round (round_key v w i) st) (i + 1)

let cipher (v: variant) (w: Seq.lseq elem (xkeylen v)) (input: block) : block =
  rounds v w (add_round_key input (round_key v w 0)) 1

(** The whole of AES, from a raw key. *)
let aes_encrypt_block (v: variant) (key: Seq.lseq elem (keylen v)) (input: block)
  : block = cipher v (key_expansion v key) input

(** {2 Counter mode}

    [inc32] increments the last four bytes of a block as a big-endian number,
    wrapping at 2^32 and leaving the first twelve alone.  This is GCM's
    [inc_32] and also the counter step of AES-CTR as NIST SP 800-38A's
    standard incrementing function uses it. *)

let be32 (b: block) : n: nat { n < pow2 32 } =
  let x = ((Seq.index b 12 * 256 + Seq.index b 13) * 256 + Seq.index b 14) * 256
          + Seq.index b 15 in
  assert_norm (256 * 256 * 256 * 256 == pow2 32);
  x

let inc32 (b: block) : block =
  let n = (be32 b + 1) % pow2 32 in
  Seq.init blocklen (fun i ->
    (if i < 12 then Seq.index b i else byte_at n (8 * (15 - i))) <: elem)

(** [counter_block b j] is [inc32] applied [j] times. *)
let rec counter_block (b: block) (j: nat) : Tot block (decreases j) =
  if j = 0 then b else inc32 (counter_block b (j - 1))

(** The keystream of counter mode, as a function of the byte index: byte [i]
    comes from block [i / 16] of the counter sequence.  Stating it pointwise
    rather than as a fold over blocks is what lets an implementation's loop
    invariant be an equation about [Seq.init], and it makes the definition
    insensitive to whether the message is a whole number of blocks. *)
let ctr_keystream (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                  (n: nat) (i: nat { i < n })
  : elem = Seq.index (cipher v w (counter_block b (i / 16))) (i % 16)

let ctr_encrypt (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                (msg: Seq.seq elem)
  : Seq.seq elem =
  Seq.init (Seq.length msg)
    (fun i -> Seq.index msg i ^^ ctr_keystream v w b (Seq.length msg) i)
