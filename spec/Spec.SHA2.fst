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

(** The SHA-2 family, FIPS 180-4, specified once.

    SHA-224/256 and SHA-384/512 are the same algorithm at two widths with
    different constants, so this module is generic in a word type and takes a
    [params] record holding everything the four members differ in.  There is no
    [alg] index and no dependent [word_t a]: an algorithm is simply a
    [params t] value, and the four of them live in [Spec.SHA2.Constants].
    Custard specializes on that record -- it is a monomorphized binder in the
    implementation -- so the generated C has four independent, fully unfolded
    functions with the rotation amounts as literals.

    Every definition here is shaped like the loop that implements it:
    [Hacl.Spec.Loops.repeati] unfolds on the right, and [set8] is eight
    [Seq.upd]s in the order the machine performs them, so the implementation's
    proof obligations are equalities between identical terms rather than
    reasoning about the algorithm. *)
module Spec.SHA2

open Hacl.Secret.Word
open Hacl.Spec.Loops
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module G = FStar.Ghost

(** {2 Shift and rotation amounts} *)

let rotv (t: Type0) {| word t |} = s: U32.t { 0 < U32.v s /\ U32.v s < bits #t }
let shftv (t: Type0) {| word t |} = s: U32.t { U32.v s < bits #t }

(** {2 What the four members of the family differ in} *)

noeq
type params (t: Type0) {| word t |} = {
  (** Number of rounds.  A machine value, not a [nat]: every field of this
      record either is a machine value or is erased, so the record itself has
      a C representation and Custard never has to invent one for a [nat]. *)
  nrounds: n: SZ.t { 16 < SZ.v n };

  (** Round constants and initial state.  These are read only by
      specifications -- the implementation fills a table of its own and proves
      it equal -- so they are [erased] and cannot reach the generated code. *)
  k: G.erased (Seq.lseq t (SZ.v nrounds));
  iv: G.erased (Seq.lseq t 8);

  (** Digest length in bytes, a prefix of the eight-word state. *)
  nhash_bytes: n: SZ.t { 0 < SZ.v n /\ SZ.v n <= 8 * bytes #t };

  (** [Sigma0], [Sigma1]: three rotations each. *)
  cs0_a: rotv t; cs0_b: rotv t; cs0_c: rotv t;
  cs1_a: rotv t; cs1_b: rotv t; cs1_c: rotv t;

  (** [sigma0], [sigma1]: two rotations and a shift each. *)
  s0_a: rotv t; s0_b: rotv t; s0_c: shftv t;
  s1_a: rotv t; s1_b: rotv t; s1_c: shftv t;
}

(** The two byte counts above, as [nat]s, for use in specifications. *)
unfold let rounds (#t: Type0) {| word t |} (p: params t) : n: pos { 16 < n } = SZ.v p.nrounds
unfold let hash_bytes (#t: Type0) {| word t |} (p: params t) : pos = SZ.v p.nhash_bytes

(** A block is sixteen words; the length field is two. *)
unfold let block_words : pos = 16
unfold let block_len (#t: Type0) {| word t |} : pos = block_words * bytes #t
unfold let len_len (#t: Type0) {| word t |} : pos = 2 * bytes #t

(** {2 The round functions} *)

let _Sigma0 (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t) (x: t) : t =
  logxor #t (logxor #t (rotate_right x p.cs0_a) (rotate_right x p.cs0_b)) (rotate_right x p.cs0_c)

let _Sigma1 (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t) (x: t) : t =
  logxor #t (logxor #t (rotate_right x p.cs1_a) (rotate_right x p.cs1_b)) (rotate_right x p.cs1_c)

let _sigma0 (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t) (x: t) : t =
  logxor #t (logxor #t (rotate_right x p.s0_a) (rotate_right x p.s0_b)) (shift_right x p.s0_c)

let _sigma1 (#t: Type0) {| word t |} ([@@@FStar.Attributes.monomorphize] p: params t) (x: t) : t =
  logxor #t (logxor #t (rotate_right x p.s1_a) (rotate_right x p.s1_b)) (shift_right x p.s1_c)

let _Ch (#t: Type0) {| word t |} (x y z: t) : t =
  logxor #t (logand #t x y) (logand #t (lognot x) z)

let _Maj (#t: Type0) {| word t |} (x y z: t) : t =
  logxor #t (logxor #t (logand #t x y) (logand #t x z)) (logand #t y z)

(** {2 Message schedule} *)

(** The schedule, defined slotwise rather than as a fold over an array: slot
    [i] below sixteen is the block, and above it is
    [sigma1 w.[i-2] + w.[i-7] + sigma0 w.[i-15] + w.[i-16]], summed in the
    order the implementation accumulates them.

    Writing it this way -- rather than as a sequence being filled in -- is what
    makes the implementation's loop invariant ("slots below [i] are final")
    hold by unfolding a definition, with no argument that earlier slots are
    never overwritten. *)
let rec ws_at (#t: Type0) {| word t |} (p: params t) (b: Seq.lseq t 16) (i: nat)
  : Tot t (decreases i)
  = if i < 16 then Seq.index b i
    else
      add_mod #t
        (add_mod #t
          (add_mod #t (_sigma1 p (ws_at p b (i - 2))) (ws_at p b (i - 7)))
          (_sigma0 p (ws_at p b (i - 15))))
        (ws_at p b (i - 16))

let ws (#t: Type0) {| word t |} (p: params t) (b: Seq.lseq t 16) : Seq.lseq t (rounds p) =
  Seq.init (rounds p) (ws_at p b)

(** {2 Shuffle} *)

(** Eight updates in index order -- exactly what the implementation writes. *)
let set8 (#t: Type0) (h: Seq.lseq t 8) (x0 x1 x2 x3 x4 x5 x6 x7: t) : Seq.lseq t 8 =
  Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd h
    0 x0) 1 x1) 2 x2) 3 x3) 4 x4) 5 x5) 6 x6) 7 x7

(** [set8] overwrites all eight slots, so what it is applied to does not
    matter -- which is how the implementation may add the saved state into the
    shuffled state rather than the other way round. *)
let set8_irrelevant (#t: Type0) (h1 h2: Seq.lseq t 8) (x0 x1 x2 x3 x4 x5 x6 x7: t)
  : Lemma (set8 h1 x0 x1 x2 x3 x4 x5 x6 x7 == set8 h2 x0 x1 x2 x3 x4 x5 x6 x7)
  = Seq.lemma_eq_intro (set8 h1 x0 x1 x2 x3 x4 x5 x6 x7) (set8 h2 x0 x1 x2 x3 x4 x5 x6 x7)

let shuffle_core
      (#t: Type0) {| word t |} (p: params t) (w: Seq.lseq t (rounds p))
      (i: nat) (h: Seq.lseq t 8)
  : GTot (Seq.lseq t 8)
  = if i >= (rounds p) then h else begin
      let a = Seq.index h 0 in let b = Seq.index h 1 in
      let c = Seq.index h 2 in let d = Seq.index h 3 in
      let e = Seq.index h 4 in let f = Seq.index h 5 in
      let g = Seq.index h 6 in let hh = Seq.index h 7 in
      let t1 =
        add_mod #t
          (add_mod #t
            (add_mod #t (add_mod #t hh (_Sigma1 p e)) (_Ch e f g))
            (Seq.index (G.reveal p.k) i))
          (Seq.index w i)
      in
      let t2 = add_mod #t (_Sigma0 p a) (_Maj a b c) in
      set8 h (add_mod #t t1 t2) a b c (add_mod #t d t1) e f g
    end

let shuffle (#t: Type0) {| word t |} (p: params t) (w: Seq.lseq t (rounds p)) (h: Seq.lseq t 8)
  : GTot (Seq.lseq t 8)
  = repeati_g (rounds p) (shuffle_core p w) h

(** {2 One block} *)

let add_state (#t: Type0) {| word t |} (h h': Seq.lseq t 8) : Seq.lseq t 8 =
  set8 h
    (add_mod #t (Seq.index h 0) (Seq.index h' 0)) (add_mod #t (Seq.index h 1) (Seq.index h' 1))
    (add_mod #t (Seq.index h 2) (Seq.index h' 2)) (add_mod #t (Seq.index h 3) (Seq.index h' 3))
    (add_mod #t (Seq.index h 4) (Seq.index h' 4)) (add_mod #t (Seq.index h 5) (Seq.index h' 5))
    (add_mod #t (Seq.index h 6) (Seq.index h' 6)) (add_mod #t (Seq.index h 7) (Seq.index h' 7))

let update_block (#t: Type0) {| word t |} (p: params t) (block: Seq.lseq S8.t (block_len #t)) (h: Seq.lseq t 8)
  : GTot (Seq.lseq t 8)
  = let b = words_from_be block_words block in
    add_state h (shuffle p (ws p b) h)

(** {2 Padding} *)

(** The number of zero bytes between the [0x80] and the length field. *)
let pad_zeros (#t: Type0) {| word t |} (len: nat) : n: nat { (len + 1 + n + len_len #t) % block_len #t == 0 } =
  let bl = block_len #t in
  let n = (bl - (len + 1 + len_len #t) % bl) % bl in
  Math.lemma_mod_add_distr (bl - (len + 1 + len_len #t) % bl) (len + 1 + len_len #t) bl;
  Math.lemma_mod_add_distr 0 (bl - (len + 1 + len_len #t) % bl + (len + 1 + len_len #t)) bl;
  n

(** The largest message the length field can describe, in bytes. *)
unfold let max_input (#t: Type0) {| word t |} : pos = pow2 (8 * len_len #t - 3)

let padding (#t: Type0) {| word t |} (len: nat { len < max_input #t }) : Seq.seq S8.t =
  Seq.append
    (Seq.append (Seq.create 1 (S8.classify 0x80uy)) (Seq.create (pad_zeros #t len) (S8.classify 0uy)))
    (nat_to_be (len_len #t) (8 * len))

let padded (#t: Type0) {| word t |} (msg: Seq.seq S8.t { Seq.length msg < max_input #t }) : Seq.seq S8.t =
  Seq.append msg (padding #t (Seq.length msg))

let padded_len (#t: Type0) {| word t |} (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : Lemma (Seq.length (padded #t msg) == Seq.length msg + 1 + pad_zeros #t (Seq.length msg) + len_len #t /\
           Seq.length (padded #t msg) % block_len #t == 0)
  = ()

(** {2 The hash} *)

(** The block at a byte offset.  Total, so that it may appear in a separation
    logic assertion without dragging a bounds proof along; out of range it is
    an arbitrary constant that nothing depends on. *)
let block_at (#t: Type0) {| word t |} (s: Seq.seq S8.t) (off: nat) : Seq.lseq S8.t (block_len #t) =
  if off + block_len #t <= Seq.length s
  then Seq.slice s off (off + block_len #t)
  else Seq.create (block_len #t) (S8.classify 0uy)

let block_at_shift (#t: Type0) {| word t |} (s: Seq.seq S8.t) (a: nat) (b: nat) (off: nat)
  : Lemma (requires a + b <= Seq.length s /\ off + block_len #t <= b)
          (ensures block_at #t (Seq.slice s a (a + b)) off == block_at #t s (a + off))
  = Seq.slice_slice s a (a + b) off (off + block_len #t)

let update_step (#t: Type0) {| word t |} (p: params t) (s: Seq.seq S8.t)
                (i: nat) (h: Seq.lseq t 8)
  : GTot (Seq.lseq t 8)
  = if (i + 1) * block_len #t <= Seq.length s then update_block p (block_at #t s (i * block_len #t)) h else h

let update_all (#t: Type0) {| word t |} (p: params t) (s: Seq.seq S8.t)
               (h: Seq.lseq t 8)
  : GTot (Seq.lseq t 8)
  = repeati_g (Seq.length s / block_len #t) (update_step p s) h

let finish (#t: Type0) {| word t |} (p: params t) (h: Seq.lseq t 8) : GTot (Seq.lseq S8.t (hash_bytes p)) =
  Seq.slice (words_to_be 8 h) 0 (hash_bytes p)

let hash (#t: Type0) {| word t |} (p: params t) (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : GTot (Seq.lseq S8.t (hash_bytes p))
  = finish p (update_all p (padded #t msg) (G.reveal p.iv))
