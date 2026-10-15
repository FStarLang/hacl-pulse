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

(** What an incremental BLAKE2 remembers.

    BLAKE2 differs from SHA-2 in the one way that matters to a streaming
    interface: the *last* compression is not like the others.  It is flagged,
    and its counter is the message length rather than a multiple of the block
    length.  So a block that has just been filled cannot be compressed -- it
    might turn out to be the last one.  The buffer therefore holds between one
    and [block_len] bytes, not between zero and [block_len - 1], and it is
    emptied only when the next call proves that more data is coming.

    The second difference is the key.  A keyed BLAKE2 prepends the key,
    zero-padded to one block, to the message, and shifts the final counter by
    a block to match.  Rather than carry the key around, the state carries the
    *combined* stream

      [stream key seen  =  pad_block key ++ seen]   (or just [seen], unkeyed)

    of which the buffer holds the trailing partial block and [tot] holds the
    length.  Then a keyed hash is just an unkeyed one whose buffer starts full
    and whose counter starts at one block, [last_counter] is [tot] on the
    nose, and every lemma below is stated once.

    [sabsorb] is the fold an implementation can run -- one step per block,
    reading blocks straight out of the stream -- and [blake2_stream] is the
    proof that it computes [Spec.Blake2.blake2]. *)
module Spec.Blake2.Streaming

open Hacl.Secret.Word
open Hacl.Spec.Loops
open Hacl.Spec.Bytes
open Spec.Blake2

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost
module Classical = FStar.Classical

(** {2 The combined stream} *)

let stream (#t: Type0) {| word t |} (key seen: Seq.seq S8.t) : Seq.seq S8.t =
  if Seq.length key = 0 then seen else Seq.append (pad_block #t key 0) seen

let stream_len (#t: Type0) {| word t |} (key seen: Seq.seq S8.t)
  : Lemma (Seq.length (stream #t key seen) ==
           koff #t key * block_len #t + Seq.length seen)
  = if Seq.length key = 0 then () else Seq.lemma_len_append (pad_block #t key 0) seen

(** Feeding more data extends the stream on the right, which is what makes the
    generic chunk lemmas of [Hacl.Spec.Chunks] apply unchanged. *)
let stream_append (#t: Type0) {| word t |} (key seen data: Seq.seq S8.t)
  : Lemma (stream #t key (Seq.append seen data) ==
           Seq.append (stream #t key seen) data)
  = if Seq.length key = 0 then ()
    else Seq.append_assoc (pad_block #t key 0) seen data

(** The number of blocks that may be compressed without the final flag: all of
    them but the last.  Zero for an empty stream, which still compresses one
    (all-zero) block at the end. *)
let nlast_of (#t: Type0) {| word t |} (len: nat) : nat =
  if len = 0 then 0 else (len - 1) / block_len #t

(** How many bytes the buffer holds: between one and [block_len], and zero
    only for an empty stream. *)
let brem_of (#t: Type0) {| word t |} (len: nat) : r: nat { r <= block_len #t } =
  if len > 0 then begin
    Math.lemma_div_mod (len - 1) (block_len #t);
    Math.lemma_mod_lt (len - 1) (block_len #t)
  end;
  len - nlast_of #t len * block_len #t

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"

let brem_bounds (#t: Type0) {| word t |} (len: nat)
  : Lemma (nlast_of #t len * block_len #t <= len /\
           brem_of #t len <= block_len #t /\
           (len == 0 <==> brem_of #t len == 0) /\
           len == nlast_of #t len * block_len #t + brem_of #t len)
  = let bl = block_len #t in
    if len = 0 then ()
    else begin
      Math.lemma_div_mod (len - 1) bl;
      Math.lemma_mod_lt (len - 1) bl
    end

(** The buffer is full exactly when the length is a positive multiple of the
    block length. *)
let nlast_of_step (#t: Type0) {| word t |} (n: nat) (r: nat)
  : Lemma (requires 0 < r /\ r <= block_len #t)
          (ensures nlast_of #t (n * block_len #t + r) == n /\
                   brem_of #t (n * block_len #t + r) == r)
  = let bl = block_len #t in
    Math.lemma_div_plus (r - 1) n bl;
    Math.small_div (r - 1) bl

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"

(** The same, allowing the empty stream: a zero remainder can only happen at
    length zero, and then the block index is zero too. *)
let nlast_of_step0 (#t: Type0) {| word t |} (n: nat) (r: nat)
  : Lemma (requires r <= block_len #t /\ (r == 0 ==> n == 0))
          (ensures nlast_of #t (n * block_len #t + r) == n /\
                   brem_of #t (n * block_len #t + r) == r)
  = if r = 0 then () else nlast_of_step #t n r

#pop-options

(** {2 The fold}

    One step per block: read the block out of the stream, compress it at the
    counter "bytes absorbed including this block", not flagged.  [pad_block]
    is total, so no bound is needed for the step to typecheck; the bounds
    appear only in the lemmas. *)

let sstep (#t: Type0) {| word t |} (p: params t)
          (s: Seq.seq S8.t) (i: nat) (h: Seq.lseq t 8)
  : GTot (Seq.lseq t 8)
  = compress p h (words_from_le block_words (pad_block #t s (i * block_len #t)))
               ((i + 1) * block_len #t) false

(** The fold starts from a state, not from a key length: an implementation
    computes [init p klen] once, at [init], and never looks at the key
    again. *)
let sabsorb (#t: Type0) {| word t |} (p: params t) (h0: Seq.lseq t 8)
            (s: Seq.seq S8.t) (n: nat)
  : GTot (Seq.lseq t 8)
  = repeati_g n (sstep p s) h0

let sabsorb_zero (#t: Type0) {| word t |} (p: params t) (h0: Seq.lseq t 8)
                 (s: Seq.seq S8.t)
  : Lemma (sabsorb p h0 s 0 == h0)
  = ()

unfold let agree_upto (s1 s2: Seq.seq S8.t) (n: nat) =
  n <= Seq.length s1 /\ n <= Seq.length s2 /\
  (forall (k: nat). k < n ==> Seq.index s1 k == Seq.index s2 k)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** A block that lies wholly inside both sequences is the same block. *)
let pad_block_congr (#t: Type0) {| word t |} (s1 s2: Seq.seq S8.t) (off: nat)
  : Lemma (requires agree_upto s1 s2 (off + block_len #t))
          (ensures pad_block #t s1 off == pad_block #t s2 off)
  = Seq.lemma_eq_intro (pad_block #t s1 off) (pad_block #t s2 off);
    Seq.lemma_eq_elim (pad_block #t s1 off) (pad_block #t s2 off)

(** The fold over [n] blocks depends only on those [n] blocks. *)
let sabsorb_congr (#t: Type0) {| word t |} (p: params t) (h0: Seq.lseq t 8)
                  (s1 s2: Seq.seq S8.t) (n: nat)
  : Lemma (requires agree_upto s1 s2 (n * block_len #t))
          (ensures sabsorb p h0 s1 n == sabsorb p h0 s2 n)
  = let bl = block_len #t in
    let aux (i: nat) (h: Seq.lseq t 8)
      : Lemma (i < n ==> sstep p s1 i h == sstep p s2 i h)
      = if i < n then begin
          Math.lemma_mult_le_right bl (i + 1) n;
          Math.distributivity_add_left i 1 bl;
          pad_block_congr #t s1 s2 (i * bl)
        end
    in
    Classical.forall_intro_2 aux;
    repeati_g_ext n (sstep p s1) (sstep p s2) h0

(** Appending data does not disturb the blocks already folded. *)
let sabsorb_prefix (#t: Type0) {| word t |} (p: params t) (h0: Seq.lseq t 8)
                   (a b: Seq.seq S8.t) (n: nat)
  : Lemma (requires n * block_len #t <= Seq.length a)
          (ensures sabsorb p h0 (Seq.append a b) n == sabsorb p h0 a n)
  = let ab = Seq.append a b in
    Seq.lemma_len_append a b;
    let aux (k: nat { k < n * block_len #t }) : Lemma (Seq.index ab k == Seq.index a k)
      = Seq.lemma_index_app1 a b k
    in
    Classical.forall_intro aux;
    sabsorb_congr p h0 ab a n

(** Two blocks read at different offsets of different sequences, byte for
    byte the same.  This is what an implementation compressing straight out of
    the caller's buffer needs. *)
let pad_block_shift (#t: Type0) {| word t |} (a b: Seq.seq S8.t) (oa ob: nat)
  : Lemma (requires oa + block_len #t <= Seq.length a /\
                    ob + block_len #t <= Seq.length b /\
                    (forall (k: nat). k < block_len #t ==>
                       Seq.index a (oa + k) == Seq.index b (ob + k)))
          (ensures pad_block #t a oa == pad_block #t b ob)
  = Seq.lemma_eq_intro (pad_block #t a oa) (pad_block #t b ob);
    Seq.lemma_eq_elim (pad_block #t a oa) (pad_block #t b ob)

(** The [j]th block of a run of [nblk] blocks that agree byte for byte.  All
    the index arithmetic an absorbing loop needs, done once, here, away from
    any separation-logic context. *)
let pad_block_run (#t: Type0) {| word t |} (a b: Seq.seq S8.t)
                  (base n0 j nblk: nat)
  : Lemma (requires j < nblk /\
                    base + nblk * block_len #t <= Seq.length a /\
                    (n0 + nblk) * block_len #t <= Seq.length b /\
                    (forall (k: nat). k < nblk * block_len #t ==>
                       Seq.index a (base + k) ==
                         Seq.index b (n0 * block_len #t + k)))
          (ensures pad_block #t a (base + j * block_len #t) ==
                   pad_block #t b ((n0 + j) * block_len #t))
  = let bl = block_len #t in
    Math.lemma_mult_le_right bl (j + 1) nblk;
    Math.distributivity_add_left j 1 bl;
    Math.distributivity_add_left n0 j bl;
    Math.lemma_mult_le_right bl (n0 + j + 1) (n0 + nblk);
    let aux (k: nat { k < bl })
      : Lemma (Seq.index a (base + j * bl + k) == Seq.index b ((n0 + j) * bl + k))
      = assert (j * bl + k < nblk * bl);
        assert (base + j * bl + k == base + (j * bl + k));
        assert ((n0 + j) * bl + k == n0 * bl + (j * bl + k))
    in
    Classical.forall_intro aux;
    pad_block_shift #t a b (base + j * bl) ((n0 + j) * bl)

(** {2 An update that fits in the buffer}

    Nothing is compressed: the block index does not move, the remainder grows
    by the length of the data, and the buffer is still the last block.
    Everything the implementation's easy branch has to know, proved once. *)
let update_small (#t: Type0) {| word t |} (p: params t) (h0: Seq.lseq t 8)
                 (s vdata vbuf': Seq.seq S8.t) (nlast blen: nat)
  : Lemma (requires nlast == nlast_of #t (Seq.length s) /\
                    blen == brem_of #t (Seq.length s) /\
                    blen + Seq.length vdata <= block_len #t /\
                    Seq.length vbuf' == block_len #t /\
                    (forall (k: nat). k < blen + Seq.length vdata ==>
                       Seq.index vbuf' k ==
                         Seq.index (Seq.append s vdata) (nlast * block_len #t + k)))
          (ensures (let s1 = Seq.append s vdata in
                    nlast_of #t (Seq.length s1) == nlast /\
                    brem_of #t (Seq.length s1) == blen + Seq.length vdata /\
                    sabsorb p h0 s1 (nlast_of #t (Seq.length s1)) ==
                      sabsorb p h0 s nlast /\
                    (forall (k: nat). k < brem_of #t (Seq.length s1) ==>
                       Seq.index vbuf' k ==
                         Seq.index s1 (nlast_of #t (Seq.length s1) * block_len #t + k))))
  = brem_bounds #t (Seq.length s);
    Seq.lemma_len_append s vdata;
    nlast_of_step0 #t nlast (blen + Seq.length vdata);
    sabsorb_prefix p h0 s vdata nlast

(** {2 The arithmetic of an overflowing update}

    A buffer holding [blen] bytes receives [dlen] more, and together they are
    more than a block.  The buffer is filled with [fill] bytes and compressed;
    of the remaining [rest] bytes, all but the last one to [block_len] are
    compressed straight out of the caller's data.  Everything an
    implementation has to know about the resulting offsets, in one place. *)
let update_split (#t: Type0) {| word t |} (nlast blen dlen: nat)
  : Lemma (requires blen <= block_len #t /\ block_len #t < blen + dlen)
          (ensures (let bl = block_len #t in
                    let fill = bl - blen in
                    let rest = dlen - fill in
                    let nblk = (rest - 1) / bl in
                    let tl = rest - nblk * bl in
                    0 <= fill /\ fill <= dlen /\ 0 < rest /\
                    fill + nblk * bl <= dlen /\
                    0 < tl /\ tl <= bl /\
                    dlen - tl == fill + nblk * bl /\
                    (nlast + 1 + nblk) * bl == nlast * bl + blen + (dlen - tl) /\
                    (nlast + 1 + nblk) * bl + tl == nlast * bl + blen + dlen))
  = let bl = block_len #t in
    let fill = bl - blen in
    let rest = dlen - fill in
    let nblk = (rest - 1) / bl in
    Math.lemma_div_mod (rest - 1) bl;
    Math.lemma_mod_lt (rest - 1) bl;
    assert (nblk * bl == bl * nblk);
    assert (nblk * bl <= rest - 1);
    Math.distributivity_add_left nlast 1 bl;
    Math.distributivity_add_left (nlast + 1) nblk bl

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"


let last_block_is_buf (#t: Type0) {| word t |} (s vsub: Seq.seq S8.t) (n blen: nat)
  : Lemma (requires Seq.length s == n * block_len #t + blen /\
                    blen <= block_len #t /\ Seq.length vsub == blen /\
                    (forall (k: nat). k < blen ==>
                       Seq.index vsub k == Seq.index s (n * block_len #t + k)))
          (ensures pad_block #t vsub 0 == pad_block #t s (n * block_len #t))
  = Seq.lemma_eq_intro (pad_block #t vsub 0) (pad_block #t s (n * block_len #t));
    Seq.lemma_eq_elim (pad_block #t vsub 0) (pad_block #t s (n * block_len #t))

#pop-options

(** {2 The state relation} *)

(** [acc] has absorbed all but the last block of the stream, and [buf] holds
    the rest. *)
unfold let acc_ok (#t: Type0) {| word t |} (p: params t)
                  (key: Seq.seq S8.t) (seen: Seq.seq S8.t)
                  (vacc: Seq.seq t) (vbuf: Seq.seq S8.t) =
  Seq.length key <= max_key_len #t /\
  Seq.length vacc == 8 /\ Seq.length vbuf == block_len #t /\
  (let s = stream #t key seen in
   let n = nlast_of #t (Seq.length s) in
   vacc == sabsorb p (init p (Seq.length key)) s n /\
   (forall (k: nat). k < brem_of #t (Seq.length s) ==>
      Seq.index vbuf k == Seq.index s (n * block_len #t + k)))

unfold let stream_ok (#t: Type0) {| word t |} (p: params t)
                     (key: Seq.seq S8.t) (seen: Seq.seq S8.t)
                     (vacc: Seq.seq t) (vbuf: Seq.seq S8.t) (vtot: Seq.seq FStar.SizeT.t) =
  Seq.length vtot == 1 /\
  FStar.SizeT.v (Seq.index vtot 0) == Seq.length (stream #t key seen) /\
  Seq.length (stream #t key seen) + 2 * block_len #t < pow2 64 /\
  acc_ok p key seen vacc vbuf

(** {2 The digest}

    Everything above is about the blocks that are not the last.  This is the
    last one: the counter is the stream length -- which is
    [Spec.Blake2.last_counter], keyed or not -- and the block is the buffer
    padded with zeros. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 100"

(** [Spec.Blake2.block_of] is a window on the combined stream. *)
let block_of_stream (#t: Type0) {| word t |} (key seen: Seq.seq S8.t) (i: nat)
  : Lemma (requires Seq.length key <= max_key_len #t)
          (ensures block_of #t key seen i ==
                   pad_block #t (stream #t key seen) (i * block_len #t))
  = let bl = block_len #t in
    let s = stream #t key seen in
    if Seq.length key = 0 then ()
    else begin
      let kb = pad_block #t key 0 in
      Seq.lemma_len_append kb seen;
      if i = 0 then begin
        let aux (j: nat { j < bl }) : Lemma (Seq.index kb j == Seq.index (pad_block #t s 0) j)
          = Seq.lemma_index_app1 kb seen j
        in
        Classical.forall_intro aux;
        Seq.lemma_eq_intro kb (pad_block #t s 0);
        Seq.lemma_eq_elim kb (pad_block #t s 0)
      end else begin
        Math.distributivity_sub_left i 1 bl;
        let l = pad_block #t seen ((i - 1) * bl) in
        let r = pad_block #t s (i * bl) in
        let aux (j: nat { j < bl }) : Lemma (Seq.index l j == Seq.index r j)
          = if i * bl + j < Seq.length s
            then Seq.lemma_index_app2 kb seen (i * bl + j)
        in
        Classical.forall_intro aux;
        Seq.lemma_eq_intro l r;
        Seq.lemma_eq_elim l r
      end
    end

(** The stream length is the counter of the final compression, and its number
    of whole blocks is [Spec.Blake2.nblocks] less one. *)
let stream_shape (#t: Type0) {| word t |} (key seen: Seq.seq S8.t)
  : Lemma (requires Seq.length key <= max_key_len #t)
          (ensures (let s = stream #t key seen in
                    Seq.length s == last_counter #t key seen /\
                    nlast_of #t (Seq.length s) + 1 == nblocks #t key seen))
  = let bl = block_len #t in
    let n = Seq.length seen in
    stream_len #t key seen;
    nblocks_eq #t key seen;
    Math.euclidean_division_definition n bl;
    if n = 0 then (if Seq.length key = 0 then () else Math.small_div (bl - 1) bl)
    else begin
      Math.lemma_div_plus (n - 1) (koff #t key) bl;
      Math.lemma_mod_lt n bl;
      if n % bl = 0 then begin
        Math.lemma_div_exact n bl;
        Math.lemma_div_plus (bl - 1) (n / bl - 1) bl;
        Math.small_div (bl - 1) bl
      end else begin
        Math.lemma_div_mod n bl;
        Math.small_div (n % bl - 1) bl;
        Math.lemma_div_plus (n % bl - 1) (n / bl) bl
      end
    end

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 150"

(** The whole point: the streaming fold, plus one flagged compression of the
    buffered tail, is [Spec.Blake2.blake2]. *)
let blake2_stream (#t: Type0) {| word t |} (p: params t) (key seen: Seq.seq S8.t)
  : Lemma (requires Seq.length key <= max_key_len #t)
          (ensures (let s = stream #t key seen in
                    let n = nlast_of #t (Seq.length s) in
                    blake2 p key seen ==
                    final p (compress p (sabsorb p (init p (Seq.length key)) s n)
                              (words_from_le block_words (pad_block #t s (n * block_len #t)))
                              (Seq.length s) true)))
  = let bl = block_len #t in
    let s = stream #t key seen in
    let d = data #t key seen in
    let nb = nblocks #t key seen in
    let n = nlast_of #t (Seq.length s) in
    stream_shape #t key seen;
    nblocks_pos #t key seen;
    let aux (i: nat) (h: Seq.lseq t 8)
      : Lemma (i < n ==> compress_at p d i h == sstep p s i h)
      = if i < n then begin
          block_at_data #t key seen i;
          block_of_stream #t key seen i;
          nblocks_bound #t key seen i
        end
    in
    Classical.forall_intro_2 aux;
    repeati_g_ext n (compress_at p d) (sstep p s) (init p (Seq.length key));
    block_at_data #t key seen n;
    block_of_stream #t key seen n

#pop-options
