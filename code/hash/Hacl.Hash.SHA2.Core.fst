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

(** SHA-2, written once for the whole family.

    Every function takes the [Spec.SHA2.params] record as a monomorphized
    binder, so Custard emits one copy per algorithm with the rotation amounts,
    the round count and the digest length all folded to literals.  Nothing here
    branches on which algorithm is running.

    The round constants and the initial state arrive as slices rather than as
    fields of [p], which is erased: a record field would have to be
    materialized in C.  The caller passes the tables and proves them equal to
    [p.k] and [p.iv]; see [Hacl.Hash.SHA2].  The permission is fractional, so
    a caller may hand over the [static const] array itself. *)
module Hacl.Hash.SHA2.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Spec.SHA2
open Spec.SHA2.Lemmas
open Hacl.Spec.Loops

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module Mem = Hacl.Mem

(** {2 Byte counts as machine values} *)

let block_len_sz (#t: Type0) {| w: word t |} : n: SZ.t { SZ.v n == block_len #t } =
  SZ.mul 16sz (nbytes #t #w)

let len_len_sz (#t: Type0) {| w: word t |} : n: SZ.t { SZ.v n == len_len #t } =
  SZ.mul 2sz (nbytes #t #w)

(** A message short enough to hash has a bit length that fits in eight bytes. *)
let len_fits (n: nat) : Lemma (requires n < pow2 61) (ensures 8 * n < pow2 64)
  = Math.pow2_plus 61 3;
    assert_norm (pow2 3 == 8)

(** Every byte count in this file is at most two blocks, and a block is at most
    two hundred and fifty-six bytes, so [SizeT] arithmetic never overflows. *)
let small_fits (n: nat) : Lemma (requires n <= 512) (ensures SZ.fits n)
  = assert_norm (512 < pow2 16)

(** How much of the two-block scratch buffer the padding actually occupies: one
    block if the [0x80] byte and the length still fit beside the remainder, two
    otherwise. *)
inline_for_extraction
let tail_len (#t: Type0) {| w: word t |} (rem: (r: SZ.t { SZ.v r < block_len #t }))
  : n: SZ.t { 8 <= SZ.v n /\ SZ.v n <= 2 * block_len #t /\
              SZ.v n == (if SZ.v rem + 1 + len_len #t <= block_len #t
                         then block_len #t else 2 * block_len #t) } =
  let bl = block_len_sz #t #w in
  let ll = len_len_sz #t #w in
  if SZ.lte (SZ.add rem (SZ.add 1sz ll)) bl then bl else SZ.mul 2sz bl

(** {2 Message schedule} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 0"

fn ws_expand (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (wsb: A.array t) (block: A.array S8.t) (off: SZ.t)
             (#vw0: erased (Seq.seq t)) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to wsb vw0 ** A.pts_to block #pb vb **
         pure (Seq.length vw0 == (rounds p) /\ SZ.v off + block_len #t <= Seq.length vb)
ensures A.pts_to wsb (ws p (words_from_be block_words (block_at #t vb (SZ.v off)))) **
        A.pts_to block #pb vb
{
  A.pts_to_len wsb;
  A.pts_to_len block;
  let nb = nbytes #t #w;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vw: Seq.seq t).
    pts_to i vi ** A.pts_to wsb vw ** A.pts_to block #pb vb **
    pure (SZ.v vi <= 16 /\ Seq.length vw == (rounds p) /\ SZ.v off + block_len #t <= Seq.length vb /\
          (forall (j: nat). j < SZ.v vi ==>
             Seq.index vw j == ws_at p (words_from_be block_words (block_at #t vb (SZ.v off))) j))
  decreases (16 - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vi + 1) 16;
    Seq.slice_slice vb (SZ.v off) (SZ.v off + block_len #t)
                    (SZ.v vi * bytes #t) (SZ.v vi * bytes #t + bytes #t);
    let x = load_be #t block (SZ.add off (SZ.mul vi nb));
    w.v_extensional x (ws_at p (words_from_be block_words (block_at #t vb (SZ.v off))) (SZ.v vi));
    A.((wsb.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  let mut j = 16sz;
  while (let vj = !j; SZ.lt vj p.nrounds)
  invariant exists* (vj: SZ.t) (vw: Seq.seq t).
    pts_to j vj ** A.pts_to wsb vw ** A.pts_to block #pb vb **
    pure (16 <= SZ.v vj /\ SZ.v vj <= (rounds p) /\ Seq.length vw == (rounds p) /\
          SZ.v off + block_len #t <= Seq.length vb /\
          (forall (k: nat). k < SZ.v vj ==>
             Seq.index vw k == ws_at p (words_from_be block_words (block_at #t vb (SZ.v off))) k))
  decreases (rounds p - SZ.v (!j))
  {
    let vj = !j;
    let a2 = A.(wsb.(SZ.sub vj 2sz));
    let a7 = A.(wsb.(SZ.sub vj 7sz));
    let a15 = A.(wsb.(SZ.sub vj 15sz));
    let a16 = A.(wsb.(SZ.sub vj 16sz));
    let x = add_mod #t (add_mod #t (add_mod #t (_sigma1 p a2) a7) (_sigma0 p a15)) a16;
    A.((wsb.(vj) <- x));
    j := SZ.add vj 1sz;
  };
  with vw. assert (A.pts_to wsb vw);
  Seq.lemma_eq_intro vw (ws p (words_from_be block_words (block_at #t vb (SZ.v off))));
  Seq.lemma_eq_elim vw (ws p (words_from_be block_words (block_at #t vb (SZ.v off))));
}

(** {2 One block}

    Eight registers, read at the top of the round and written back at the
    bottom, exactly as [Spec.SHA2.set8] describes.  Keeping the working state
    in a slice rather than in eight local variables is what lets the round be a
    loop at all; a C compiler keeps them in registers regardless. *)

(** The final step of [update_block_impl]: adding the saved registers into the
    shuffled state is [update_block]. *)
let update_block_final (#t: Type0) {| w: word t |} (p: params t)
      (block: Seq.lseq S8.t (block_len #t)) (vst0 vsh: Seq.lseq t 8)
      (a0 b0 c0 d0 e0 f0 g0 h0 a1 b1 c1 d1 e1 f1 g1 h1: t)
  : Lemma (requires vsh == repeati_g (rounds p) (shuffle_core p (ws p (words_from_be block_words block))) vst0 /\
                    a0 == Seq.index vst0 0 /\ b0 == Seq.index vst0 1 /\ c0 == Seq.index vst0 2 /\
                    d0 == Seq.index vst0 3 /\ e0 == Seq.index vst0 4 /\ f0 == Seq.index vst0 5 /\
                    g0 == Seq.index vst0 6 /\ h0 == Seq.index vst0 7 /\
                    a1 == Seq.index vsh 0 /\ b1 == Seq.index vsh 1 /\ c1 == Seq.index vsh 2 /\
                    d1 == Seq.index vsh 3 /\ e1 == Seq.index vsh 4 /\ f1 == Seq.index vsh 5 /\
                    g1 == Seq.index vsh 6 /\ h1 == Seq.index vsh 7)
          (ensures update_block p block vst0 ==
                   Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd (Seq.upd vsh
                     0 (add_mod #t a0 a1)) 1 (add_mod #t b0 b1)) 2 (add_mod #t c0 c1))
                     3 (add_mod #t d0 d1)) 4 (add_mod #t e0 e1)) 5 (add_mod #t f0 f1))
                     6 (add_mod #t g0 g1)) 7 (add_mod #t h0 h1))
  = set8_irrelevant #t vsh vst0
      (add_mod #t a0 a1) (add_mod #t b0 b1) (add_mod #t c0 c1) (add_mod #t d0 d1)
      (add_mod #t e0 e1) (add_mod #t f0 f1) (add_mod #t g0 g1) (add_mod #t h0 h1)

fn update_block_impl (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (kt: A.array t) (wsb: A.array t) (st: A.array t) (block: A.array S8.t) (off: SZ.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#vw0: erased (Seq.seq t)) (#vst0: erased (Seq.lseq t 8))
             (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to block #pb vb **
         pure (Seq.length vw0 == (rounds p) /\ reveal vk == (reveal p.k <: Seq.seq t) /\
               SZ.v off + block_len #t <= Seq.length vb)
ensures exists* vw.
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st (update_block p (block_at #t vb (SZ.v off)) vst0) **
  A.pts_to block #pb vb ** pure (Seq.length vw == (rounds p))
{
  A.pts_to_len kt;
  A.pts_to_len st;
  ws_expand p wsb block off;
  let a0 = A.(st.(0sz));
  let b0 = A.(st.(1sz));
  let c0 = A.(st.(2sz));
  let d0 = A.(st.(3sz));
  let e0 = A.(st.(4sz));
  let f0 = A.(st.(5sz));
  let g0 = A.(st.(6sz));
  let h0 = A.(st.(7sz));
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi p.nrounds)
  invariant exists* (vi: SZ.t) (vst: Seq.seq t).
    pts_to i vi ** A.pts_to kt #pk vk ** A.pts_to wsb (ws p (words_from_be block_words (block_at #t vb (SZ.v off)))) **
    A.pts_to st vst ** A.pts_to block #pb vb **
    pure (SZ.v vi <= (rounds p) /\ Seq.length vst == 8 /\
          vst == repeati_g (SZ.v vi) (shuffle_core p (ws p (words_from_be block_words (block_at #t vb (SZ.v off))))) vst0)
  decreases (rounds p - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(st.(0sz));
    let b = A.(st.(1sz));
    let c = A.(st.(2sz));
    let d = A.(st.(3sz));
    let e = A.(st.(4sz));
    let f = A.(st.(5sz));
    let g = A.(st.(6sz));
    let hh = A.(st.(7sz));
    let ki = A.(kt.(vi));
    let wi = A.(wsb.(vi));
    let t1 = add_mod #t (add_mod #t (add_mod #t (add_mod #t hh (_Sigma1 p e)) (_Ch e f g)) ki) wi;
    let t2 = add_mod #t (_Sigma0 p a) (_Maj a b c);
    A.((st.(0sz) <- add_mod #t t1 t2));
    A.((st.(1sz) <- a));
    A.((st.(2sz) <- b));
    A.((st.(3sz) <- c));
    A.((st.(4sz) <- add_mod #t d t1));
    A.((st.(5sz) <- e));
    A.((st.(6sz) <- f));
    A.((st.(7sz) <- g));
    i := SZ.add vi 1sz;
  };
  let a1 = A.(st.(0sz));
  let b1 = A.(st.(1sz));
  let c1 = A.(st.(2sz));
  let d1 = A.(st.(3sz));
  let e1 = A.(st.(4sz));
  let f1 = A.(st.(5sz));
  let g1 = A.(st.(6sz));
  let h1 = A.(st.(7sz));
  with vi vsh. assert (pts_to i vi ** A.pts_to st vsh);
  assert (pure (SZ.v vi == rounds p));
  update_block_final #t p (block_at #t vb (SZ.v off)) vst0 vsh
    a0 b0 c0 d0 e0 f0 g0 h0 a1 b1 c1 d1 e1 f1 g1 h1;
  A.((st.(0sz) <- add_mod #t a0 a1));
  A.((st.(1sz) <- add_mod #t b0 b1));
  A.((st.(2sz) <- add_mod #t c0 c1));
  A.((st.(3sz) <- add_mod #t d0 d1));
  A.((st.(4sz) <- add_mod #t e0 e1));
  A.((st.(5sz) <- add_mod #t f0 f1));
  A.((st.(6sz) <- add_mod #t g0 g1));
  A.((st.(7sz) <- add_mod #t h0 h1));
}

(** {2 The last block or two}

    A scratch buffer of two blocks, zero-initialized so the zero padding costs
    nothing, receives the remainder of the message, the [0x80] byte and the
    eight low bytes of the bit length.  Everything else is already zero, which
    is what [Spec.SHA2.Lemmas.tail_bytes] checks against the specification. *)

(** The message length in bits, big-endian, in the last eight bytes of the
    padding.  Only eight: a message long enough to need more than [2^64] bits
    of length cannot be addressed, and the higher bytes of the length field are
    left at the zero the buffer was allocated with. *)

(** The loop invariant of [write_len_be], kept opaque so that its quantifiers
    stay out of the Pulse verification conditions. *)
[@@"opaque_to_smt"]
let write_len_be_inv (off len vd: nat) (vb vb': Seq.seq S8.t) : prop =
  vd <= 8 /\ off + 8 <= Seq.length vb /\ Seq.length vb' == Seq.length vb /\
  (forall (j: nat). j < vd ==>
     Seq.index vb' (off + 7 - j) ==
       S8.classify (U8.uint_to_t ((8 * len / pow2 (8 * j)) % 256))) /\
  (forall (k: nat). k < Seq.length vb ==>
     k < off + 8 - vd \/ k >= off + 8 ==>
     Seq.index vb' k == Seq.index vb k)

let write_len_be_inv_init (off len: nat) (vb: Seq.seq S8.t)
  : Lemma (requires off + 8 <= Seq.length vb)
          (ensures write_len_be_inv off len 0 vb vb)
  = reveal_opaque (`%write_len_be_inv) write_len_be_inv

(** The byte the loop writes at step [vd]. *)
let write_len_be_byte (len: SZ.t) (bits8: U64.t) (vd: nat) (vsh: U32.t)
  : Lemma (requires 8 * SZ.v len < pow2 64 /\ vd < 8 /\ U32.v vsh == 8 * vd /\
                    bits8 == U64.mul 8uL (SZ.sizet_to_uint64 len))
          (ensures Cast.uint64_to_uint8 (U64.shift_right bits8 vsh) ==
                   U8.uint_to_t ((8 * SZ.v len / pow2 (8 * vd)) % 256))
  = let c = Cast.uint64_to_uint8 (U64.shift_right bits8 vsh) in
    assert (U64.v bits8 == 8 * SZ.v len);
    assert (U64.v (U64.shift_right bits8 vsh) == 8 * SZ.v len / pow2 (8 * vd));
    assert_norm (pow2 8 == 256);
    assert (U8.v c == (8 * SZ.v len / pow2 (8 * vd)) % 256);
    U8.uv_inv c

let write_len_be_inv_step (off len vd: nat) (vb vb': Seq.seq S8.t) (bs: S8.t)
  : Lemma (requires vd < 8 /\ write_len_be_inv off len vd vb vb' /\
                    bs == S8.classify (U8.uint_to_t ((8 * len / pow2 (8 * vd)) % 256)))
          (ensures off + 7 - vd < Seq.length vb' /\
                   write_len_be_inv off len (vd + 1) vb (Seq.upd vb' (off + 7 - vd) bs))
  = reveal_opaque (`%write_len_be_inv) write_len_be_inv

let write_len_be_inv_final (off len: nat) (vb vb': Seq.seq S8.t)
  : Lemma (requires write_len_be_inv off len 8 vb vb')
          (ensures Seq.length vb' == Seq.length vb /\ off + 8 <= Seq.length vb' /\
                   (forall (j: nat). {:pattern (Seq.index vb' (off + 7 - j))} j < 8 ==>
                      Seq.index vb' (off + 7 - j) ==
                        S8.classify (U8.uint_to_t ((8 * len / pow2 (8 * j)) % 256))) /\
                   (forall (k: nat). {:pattern (Seq.index vb' k)}
                      k < Seq.length vb ==> k < off \/ k >= off + 8 ==>
                      Seq.index vb' k == Seq.index vb k))
  = reveal_opaque (`%write_len_be_inv) write_len_be_inv

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"

fn write_len_be (b: A.array S8.t) (off: SZ.t) (len: SZ.t)
                (#vb: erased (Seq.seq S8.t))
requires A.pts_to b vb ** pure (SZ.v off + 8 <= Seq.length vb /\ 8 * SZ.v len < pow2 64)
ensures exists* vb'. A.pts_to b vb' **
  pure (Seq.length vb' == Seq.length vb /\ SZ.v off + 8 <= Seq.length vb' /\
        (forall (j: nat). j < 8 ==>
           Seq.index vb' (SZ.v off + 7 - j) ==
             S8.classify (U8.uint_to_t ((8 * SZ.v len / pow2 (8 * j)) % 256))) /\
        (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + 8 ==>
           Seq.index vb' k == Seq.index vb k))
{
  A.pts_to_len b;
  let bits8 = U64.mul 8uL (SZ.sizet_to_uint64 len);
  write_len_be_inv_init (SZ.v off) (SZ.v len) vb;
  let mut d = 0sz;
  let mut sh = 0ul;
  while (let vd = !d; SZ.lt vd 8sz)
  invariant exists* (vd: SZ.t) (vsh: U32.t) (vb': Seq.seq S8.t).
    pts_to d vd ** pts_to sh vsh ** A.pts_to b vb' **
    pure (SZ.v vd <= 8 /\ U32.v vsh == 8 * SZ.v vd /\
          write_len_be_inv (SZ.v off) (SZ.v len) (SZ.v vd) vb vb')
  decreases (8 - SZ.v (!d))
  {
    let vd = !d;
    let vsh = !sh;
    with vb'. assert (A.pts_to b vb');
    write_len_be_byte len bits8 (SZ.v vd) vsh;
    let c = Cast.uint64_to_uint8 (U64.shift_right bits8 vsh);
    let bs = S8.classify c;
    write_len_be_inv_step (SZ.v off) (SZ.v len) (SZ.v vd) vb vb' bs;
    A.((b.(SZ.add off (SZ.sub 7sz vd)) <- bs));
    Math.distributivity_add_right 8 (SZ.v vd) 1;
    d := SZ.add vd 1sz;
    sh := U32.add vsh 8ul;
  };
  with vd vb'. assert (pts_to d vd ** A.pts_to b vb');
  assert (pure (SZ.v vd == 8));
  write_len_be_inv_final (SZ.v off) (SZ.v len) vb vb';
  ()
}

#pop-options

(** {2 The last block or two}

    A scratch buffer of two blocks, zero-initialized so the zero padding costs
    nothing, receives the remainder of the message, the [0x80] byte and the
    bit length.  Everything else is already zero, which is what
    [Spec.SHA2.Lemmas.tail_bytes] checks against the specification. *)

#push-options "--z3rlimit 200"

fn build_tail (#t: Type0) {| w: word t |}
              (tl: A.array S8.t) (input: A.array S8.t) (len: SZ.t) (base: SZ.t)
              (rem: (r: SZ.t { SZ.v r < block_len #t }))
              (ntail: (n: SZ.t { 8 <= SZ.v n /\ SZ.v n <= 2 * block_len #t }))
              (#vt0: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to tl vt0 ** A.pts_to input #pin vin **
         pure (Seq.length vt0 == 2 * block_len #t /\
               (forall (k: nat). k < 2 * block_len #t ==> Seq.index vt0 k == S8.classify 0uy) /\
               Seq.length vin == SZ.v base + SZ.v rem /\ 8 * SZ.v len < pow2 64 /\
               SZ.v rem + 1 + len_len #t <= SZ.v ntail)
ensures exists* vt.
  A.pts_to tl vt ** A.pts_to input #pin vin **
  pure (Seq.length vt == 2 * block_len #t /\ SZ.v base + SZ.v rem == Seq.length vin /\
        (forall (k: nat). k < SZ.v rem ==> Seq.index vt k == Seq.index vin (SZ.v base + k)) /\
        Seq.index vt (SZ.v rem) == S8.classify 0x80uy /\
        (forall (k: nat). SZ.v rem < k /\ k < SZ.v ntail - 8 ==> Seq.index vt k == S8.classify 0uy) /\
        (forall (j: nat). j < 8 ==>
           Seq.index vt (SZ.v ntail - 1 - j) ==
             S8.classify (U8.uint_to_t ((8 * SZ.v len / pow2 (8 * j)) % 256))))
{
  A.pts_to_len tl;
  A.pts_to_len input;
  let z8 = S8.classify 0uy;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc rem)
  invariant exists* (vc: SZ.t) (vt: Seq.seq S8.t).
    pts_to c vc ** A.pts_to tl vt ** A.pts_to input #pin vin **
    pure (SZ.v vc <= SZ.v rem /\ Seq.length vt == 2 * block_len #t /\
          (forall (k: nat). k < SZ.v vc ==> Seq.index vt k == Seq.index vin (SZ.v base + k)) /\
          (forall (k: nat). SZ.v vc <= k /\ k < 2 * block_len #t ==> Seq.index vt k == z8))
  decreases (SZ.v rem - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(input.(SZ.add base vc));
    A.((tl.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  let x80 = S8.classify 0x80uy;
  A.((tl.(rem) <- x80));
  write_len_be tl (SZ.sub ntail 8sz) len;
}

(** {2 The digest}

    The state is written out big-endian into a scratch buffer of eight whole
    words and the first [hash_bytes] of it are handed to the caller; SHA-224
    and SHA-384 stop in the middle of a word, which is why the truncation is a
    byte copy rather than a shorter loop. *)

(** The machine width in bytes is [bytes]. *)
let nbytes_v (#t: Type0) {| w: word t |} : Lemma (SZ.v (nbytes #t #w) == bytes #t) = ()

(** The offset of word [j], computed by [SZ.mul]. *)
let digest_off (#t: Type0) {| w: word t |} (j: SZ.t)
  : Lemma (requires SZ.v j < 8)
          (ensures SZ.fits (SZ.v j * SZ.v (nbytes #t #w)) /\
                   SZ.v (SZ.mul j (nbytes #t #w)) == SZ.v j * bytes #t)
  = nbytes_v #t #w;
    Math.lemma_mult_le_right (bytes #t) (SZ.v j) 8

(** The invariant of [write_digest]'s first loop, kept opaque so that its
    quantifier stays out of the Pulse verification conditions. *)
[@@"opaque_to_smt"]
let digest_inv (#t: Type0) {| w: word t |} (vst: Seq.lseq t 8) (vj: nat) (vd: Seq.seq S8.t) : prop =
  vj <= 8 /\ Seq.length vd == 8 * bytes #t /\
  (forall (i: nat). i < vj * bytes #t ==> Seq.index vd i == Seq.index (words_to_be 8 vst) i)

let digest_inv_init (#t: Type0) {| w: word t |} (vst: Seq.lseq t 8) (vd: Seq.seq S8.t)
  : Lemma (requires Seq.length vd == 8 * bytes #t) (ensures digest_inv vst 0 vd)
  = reveal_opaque (`%digest_inv) (digest_inv #t #w)

let digest_inv_len (#t: Type0) {| w: word t |} (vst: Seq.lseq t 8) (vj: nat) (vd: Seq.seq S8.t)
  : Lemma (requires digest_inv vst vj vd) (ensures Seq.length vd == 8 * bytes #t)
  = reveal_opaque (`%digest_inv) (digest_inv #t #w)

let digest_inv_step (#t: Type0) {| w: word t |} (vst: Seq.lseq t 8) (vj o: nat) (x: t)
                    (vd0 vd: Seq.seq S8.t)
  : Lemma (requires vj < 8 /\ digest_inv vst vj vd0 /\ o == vj * bytes #t /\
                    x == Seq.index vst vj /\
                    Seq.length vd == Seq.length vd0 /\ o + bytes #t <= Seq.length vd /\
                    (forall (k: nat). k < bytes #t ==>
                       S8.v (Seq.index vd (o + k)) == (v x / pow2 (8 * (bytes #t - 1 - k))) % 256) /\
                    (forall (k: nat). k < Seq.length vd0 ==> k < o \/ k >= o + bytes #t ==>
                       Seq.index vd k == Seq.index vd0 k))
          (ensures digest_inv vst (vj + 1) vd)
  = reveal_opaque (`%digest_inv) (digest_inv #t #w);
    assert (forall (i: nat). i < o ==> Seq.index vd i == Seq.index vd0 i);
    digest_step #t 8 vst vj o vd;
    Math.distributivity_add_left vj 1 (bytes #t)

let digest_inv_final (#t: Type0) {| w: word t |} (vst: Seq.lseq t 8) (vd: Seq.seq S8.t)
  : Lemma (requires digest_inv vst 8 vd) (ensures vd == words_to_be 8 vst)
  = reveal_opaque (`%digest_inv) (digest_inv #t #w);
    Seq.lemma_eq_intro vd (words_to_be 8 vst)

fn write_digest (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                (out: A.array S8.t) (st: A.array t)
                (#vout: erased (Seq.seq S8.t)) (#pst: perm) (#vst: erased (Seq.lseq t 8))
requires A.pts_to out vout ** A.pts_to st #pst vst **
         pure (Seq.length vout == (hash_bytes p))
ensures A.pts_to out (finish p vst) ** A.pts_to st #pst vst
{
  A.pts_to_len out;
  A.pts_to_len st;
  let nb = nbytes #t #w;
  let z8 = S8.classify 0uy;
  let dlen = SZ.mul 8sz nb;
  let mut darr = [| z8; dlen |];
  Mem.track darr;
  A.pts_to_len darr;
  A.pts_to_len darr;

  nbytes_v #t #w;
  with vd0. assert (A.pts_to darr vd0);
  digest_inv_init #t #w vst vd0;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj 8sz)
  invariant exists* (vj: SZ.t) (vd: Seq.seq S8.t).
    pts_to j vj ** A.pts_to darr vd ** A.pts_to st #pst vst **
    pure (SZ.v vj <= 8 /\ digest_inv #t #w vst (SZ.v vj) vd)
  decreases (8 - SZ.v (!j))
  {
    let vj = !j;
    Math.lemma_mult_le_right (bytes #t) (SZ.v vj + 1) 8;
    Math.distributivity_add_left (SZ.v vj) 1 (bytes #t);
    let x = A.(st.(vj));
    digest_off #t #w vj;
    with vd0. assert (A.pts_to darr vd0);
    digest_inv_len #t #w vst (SZ.v vj) vd0;
    store_be #t darr (SZ.mul vj nb) x;
    with vd. assert (A.pts_to darr vd);
    digest_inv_step #t #w vst (SZ.v vj) (SZ.v (SZ.mul vj nb)) x vd0 vd;
    j := SZ.add vj 1sz;
  };
  with vj vd. assert (pts_to j vj ** A.pts_to darr vd);
  assert (pure (SZ.v vj == 8));
  digest_inv_final #t #w vst vd;

  let hb = p.nhash_bytes;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi hb)
  invariant exists* (vi: SZ.t) (vo: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out vo ** A.pts_to darr vd ** A.pts_to st #pst vst **
    pure (SZ.v vi <= (hash_bytes p) /\ Seq.length vo == (hash_bytes p) /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vo k == Seq.index vd k))
  decreases (hash_bytes p - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(darr.(vi));
    A.((out.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with vo. assert (A.pts_to out vo);
  Seq.lemma_eq_intro vo (finish p vst);
  Seq.lemma_eq_elim vo (finish p vst);
  Mem.wipe darr dlen;
  ()
}

(** {2 The whole hash}

    One loop over the whole blocks of the message, then a two-block scratch
    buffer holding the last partial block together with the padding, then one
    or two more blocks from that.  The specification is a single fold over the
    padded message; [Hacl.Spec.Loops.repeati_g_split] is what lets it be run as
    two loops, and [Spec.SHA2.Lemmas.padded_index] is what identifies the bytes
    the second one sees. *)

#pop-options

#push-options "--z3rlimit 400"

(** The padding blocks and the digest.  Separated from [hash_impl] only so that
    each proof obligation sees a small context. *)

(** The offset of the [vj]-th padding block stays well inside [SizeT]. *)
let tail_block_off (#t: Type0) {| w: word t |} (vj ntb ntail: nat)
  : Lemma (requires vj < ntb /\ ntb * block_len #t <= ntail /\ ntail <= 2 * block_len #t)
          (ensures 0 <= vj * block_len #t /\ vj * block_len #t + block_len #t <= ntail /\
                   vj * block_len #t <= 512)
  = Math.lemma_mult_le_right (block_len #t) (vj + 1) ntb;
    Math.distributivity_add_left vj 1 (block_len #t);
    Math.nat_times_nat_is_nat vj (block_len #t)

(** The padding is a whole number of blocks: one or two. *)
let tail_blocks (#t: Type0) {| w: word t |} (ntail: nat)
  : Lemma (requires ntail == block_len #t \/ ntail == 2 * block_len #t)
          (ensures (ntail / block_len #t) * block_len #t == ntail)
  = if ntail = block_len #t then Math.multiple_division_lemma 1 (block_len #t)
    else Math.multiple_division_lemma 2 (block_len #t)

fn tail_and_finish (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                   (kt: A.array t) (wsb: A.array t) (st: A.array t)
                   (out: A.array S8.t) (input: A.array S8.t)
                   (len: SZ.t) (nblocks: SZ.t) (base_in: SZ.t)
                   (rem: (r: SZ.t { SZ.v r < block_len #t }))
                   (pre: erased (Seq.seq S8.t))
                   (#pk: perm) (#vk: erased (Seq.seq t))
                   (#vw0: erased (Seq.seq t)) (#vst0: erased (Seq.lseq t 8))
                   (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 **
         A.pts_to out vout ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length pre + Seq.length vin == SZ.v len /\
               Seq.length vin == SZ.v base_in + SZ.v rem /\
               SZ.v len < pow2 61 /\ SZ.v len < max_input #t /\
               SZ.v rem == SZ.v len % block_len #t /\
               SZ.v len - SZ.v rem == SZ.v nblocks * block_len #t /\
               reveal vst0 == repeati_g (SZ.v nblocks)
                                (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq t) (vst: Seq.lseq t 8) (vout': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst **
  A.pts_to out vout' ** A.pts_to input #pin vin **
  pure (Seq.length vw == (rounds p) /\
        Seq.length pre + Seq.length vin < max_input #t /\
        vout' == hash p (Seq.append pre vin))
{
  A.pts_to_len input;
  A.pts_to_len out;
  A.pts_to_len st;
  A.pts_to_len wsb;
  let bl = block_len_sz #t #w;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape #t (Seq.append pre vin);
  let ntail = tail_len #t #w rem;
  let bl2 = SZ.mul 2sz bl;
  let base = SZ.sub len rem;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; bl2 |];
  Mem.track tarr;
  A.pts_to_len tarr;
  A.pts_to_len tarr;
  len_fits (SZ.v len);
  Math.euclidean_division_definition (SZ.v len) (block_len #t);
  build_tail #t tarr input len base_in rem ntail;
  with vt. assert (A.pts_to tarr vt);
  pad_zeros_alt #t (SZ.v len);
  append_index_at (reveal pre) (reveal vin) (SZ.v base) (SZ.v base_in) (SZ.v rem);
  tail_bytes #t (Seq.append pre vin) vt (SZ.v ntail) (SZ.v base);
  Math.multiple_division_lemma (SZ.v ntail / block_len #t) (block_len #t);
  Math.multiply_fractions (SZ.v ntail) (block_len #t);
  let ntb = SZ.div ntail bl;

  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj ntb)
  invariant exists* (vj: SZ.t) (vw: Seq.seq t) (vst: Seq.lseq t 8).
    pts_to j vj ** A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst **
    A.pts_to tarr vt **
    pure (SZ.v vj <= SZ.v ntb /\ Seq.length vw == (rounds p) /\
          SZ.v ntb * block_len #t <= SZ.v ntail /\
          SZ.v base == SZ.v nblocks * block_len #t /\
          Seq.length (padded #t (Seq.append pre vin)) == SZ.v base + SZ.v ntail /\
          (forall (o: nat). o + block_len #t <= SZ.v ntail ==>
             block_at #t (padded #t (Seq.append pre vin)) (SZ.v base + o) == block_at #t vt o) /\
          vst == repeati_g (SZ.v nblocks + SZ.v vj)
                   (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
  decreases (SZ.v ntb - SZ.v (!j))
  {
    let vj = !j;
    tail_block_off #t #w (SZ.v vj) (SZ.v ntb) (SZ.v ntail);
    Math.lemma_mult_le_right (block_len #t) (SZ.v vj) (SZ.v ntb);
    small_fits (SZ.v vj * block_len #t);
    Math.lemma_mult_le_right (block_len #t) (SZ.v vj + 1) (SZ.v ntb);
    Math.distributivity_add_left (SZ.v vj) 1 (block_len #t);
    Math.distributivity_add_left (SZ.v nblocks) (SZ.v vj) (block_len #t);
    Math.distributivity_add_left (SZ.v nblocks + SZ.v vj) 1 (block_len #t);
    unfold_repeati_g (SZ.v nblocks + SZ.v vj)
      (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv);
    assert (pure (block_at #t (padded #t (Seq.append pre vin))
                    ((SZ.v nblocks + SZ.v vj) * block_len #t) ==
                  block_at #t vt (SZ.v vj * block_len #t)));
    assert (pure ((SZ.v nblocks + SZ.v vj + 1) * block_len #t <=
                  Seq.length (padded #t (Seq.append pre vin))));
    update_block_impl p kt wsb st tarr (SZ.mul vj bl);
    j := SZ.add vj 1sz;
  };
  Math.multiple_modulo_lemma 1 (block_len #t);
  Math.multiple_modulo_lemma 2 (block_len #t);
  Math.euclidean_division_definition (SZ.v ntail) (block_len #t);
  tail_blocks #t #w (SZ.v ntail);
  assert (pure (SZ.v ntb * block_len #t == SZ.v ntail));
  Math.distributivity_add_left (SZ.v nblocks) (SZ.v ntb) (block_len #t);
  Math.multiple_division_lemma (SZ.v nblocks + SZ.v ntb) (block_len #t);
  assert (pure (Seq.length (padded #t (Seq.append pre vin)) / block_len #t ==
                SZ.v nblocks + SZ.v ntb));
  assert (pure (update_all p (padded #t (Seq.append pre vin)) (reveal p.iv) ==
                repeati_g (SZ.v nblocks + SZ.v ntb)
                  (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv)));
  write_digest p out st;
  Mem.wipe tarr bl2;
  ()
}

#pop-options

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"

(** The full blocks of the message, in place.  Split out of [hash_impl] so
    that the loop's proof obligation sees only the loop. *)

(** One step of [hash_blocks]: the [vi2]-th whole block of [vin] is the
    [nprev + vi2]-th block of the padded message. *)
let hash_blocks_step (#t: Type0) {| w: word t |} (p: params t) (pre vin: Seq.seq S8.t)
                     (nprev vi2 nfull: nat) (h: Seq.lseq t 8)
  : Lemma (requires Seq.length pre == nprev * block_len #t /\
                    Seq.length pre + Seq.length vin < max_input #t /\
                    nfull == Seq.length vin / block_len #t /\ vi2 < nfull)
          (ensures 0 <= vi2 * block_len #t /\
                   vi2 * block_len #t + block_len #t <= Seq.length vin /\
                   update_step p (padded #t (Seq.append pre vin)) (nprev + vi2) h ==
                   update_block p (block_at #t vin (vi2 * block_len #t)) h)
  = let bl = block_len #t in
    let m = Seq.append pre vin in
    Seq.lemma_len_append pre vin;
    padded_shape #t m;
    Math.nat_times_nat_is_nat vi2 bl;
    Math.lemma_mult_le_right bl (vi2 + 1) nfull;
    Math.lemma_div_mod (Seq.length vin) bl;
    Math.distributivity_add_left vi2 1 bl;
    padded_index_block_shift #t pre vin (vi2 * bl);
    Math.distributivity_add_left nprev vi2 bl;
    Math.distributivity_add_left (nprev + vi2) 1 bl;
    assert ((nprev + vi2 + 1) * bl <= Seq.length (padded #t m))

fn hash_blocks (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: A.array t) (wsb: A.array t) (st: A.array t) (input: A.array S8.t)
               (bl: (b: SZ.t { SZ.v b == block_len #t })) (nprev: SZ.t) (nfull: SZ.t)
               (pre: erased (Seq.seq S8.t))
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#vw0: erased (Seq.seq t)) (#vst0: erased (Seq.lseq t 8))
               (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #t /\
               Seq.length pre + Seq.length vin < max_input #t /\
               SZ.v nfull == Seq.length vin / block_len #t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq t) (vst: Seq.lseq t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #t /\ Seq.length vw == (rounds p) /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
{
  A.pts_to_len input;
  Seq.lemma_len_append (reveal pre) (reveal vin);
  padded_shape #t (Seq.append pre vin);
  let mut i = 0sz;
  while (let vi2 = !i; SZ.lt vi2 nfull)
  invariant exists* (vi2: SZ.t) (vw: Seq.seq t) (vst: Seq.lseq t 8).
    pts_to i vi2 ** A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst **
    A.pts_to input #pin vin **
    pure (SZ.v vi2 <= SZ.v nfull /\ Seq.length vw == (rounds p) /\
          vst == repeati_g (SZ.v nprev + SZ.v vi2)
                   (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
  decreases (SZ.v nfull - SZ.v (!i))
  {
    let vi2 = !i;
    with vst. assert (A.pts_to st vst);
    hash_blocks_step #t #w p (reveal pre) (reveal vin) (SZ.v nprev) (SZ.v vi2) (SZ.v nfull) vst;
    unfold_repeati_g (SZ.v nprev + SZ.v vi2)
      (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv);
    update_block_impl p kt wsb st input (SZ.mul vi2 bl);
    i := SZ.add vi2 1sz;
  };
  with vi2. assert (pts_to i vi2);
  assert (pure (SZ.v vi2 == SZ.v nfull));
}

#pop-options

(** {2 The block function as a parameter}

    [hash_blocks]' contract, as a type.  Code that absorbs whole blocks and
    should run on the SHA instructions when they are there -- the streaming
    hash, and HMAC and HKDF on top of it -- takes one of these as a
    monomorphized argument rather than calling [hash_blocks] by name.
    Custard specializes it away, so passing [blocks_scalar p] or
    [Hacl.Hash.SHA2.NI.blocks_ni p] costs no indirect call, and one generic
    copy of the caller serves both. *)

inline_for_extraction noextract
let blocks_t (#t: Type0) {| w: word t |} (p: params t) =
  (kt: A.array t) -> (wsb: A.array t) -> (st: A.array t) -> (input: A.array S8.t) ->
  (nprev: SZ.t) -> (nfull: SZ.t) -> (pre: erased (Seq.seq S8.t)) ->
  (#pk: perm) -> (#vk: erased (Seq.seq t)) ->
  (#vw0: erased (Seq.seq t)) -> (#vst0: erased (Seq.lseq t 8)) ->
  (#pin: perm) -> (#vin: erased (Seq.seq S8.t)) ->
  stt unit
    (requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #t /\
               Seq.length pre + Seq.length vin < max_input #t /\
               SZ.v nfull == Seq.length vin / block_len #t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv)))
    (ensures fun _ -> exists* (vw: Seq.seq t) (vst: Seq.lseq t 8).
      A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
      pure (Seq.length pre + Seq.length vin < max_input #t /\ Seq.length vw == (rounds p) /\
            vst == repeati_g (SZ.v nprev + SZ.v nfull)
                     (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv)))

fn blocks_scalar (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                 (kt: A.array t) (wsb: A.array t) (st: A.array t) (input: A.array S8.t)
                 (nprev: SZ.t) (nfull: SZ.t) (pre: erased (Seq.seq S8.t))
                 (#pk: perm) (#vk: erased (Seq.seq t))
                 (#vw0: erased (Seq.seq t)) (#vst0: erased (Seq.lseq t 8))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #t /\
               Seq.length pre + Seq.length vin < max_input #t /\
               SZ.v nfull == Seq.length vin / block_len #t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq t) (vst: Seq.lseq t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #t /\ Seq.length vw == (rounds p) /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #t (Seq.append pre vin))) (reveal p.iv))
{
  hash_blocks p kt wsb st input (block_len_sz #t #w) nprev nfull pre
}

#push-options "--z3rlimit 100 --fuel 1 --ifuel 0"
fn hash_impl (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
             (kt: A.array t) (ivt: A.array t) (out: A.array S8.t) (input: A.array S8.t) (len: SZ.t)
             (#pk: perm) (#vk: erased (Seq.seq t))
             (#pi: perm) (#vi: erased (Seq.seq t))
             (#vout: erased (Seq.seq S8.t)) (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vin < pow2 61 /\ Seq.length vin < max_input #t)
         ** pure (SZ.v len == Seq.length vin)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' ** A.pts_to input #pin vin **
  pure (Seq.length vin < max_input #t /\ vout' == hash p vin)
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len input;
  let bl = block_len_sz #t #w;
  let ll = len_len_sz #t #w;
  let nfull = SZ.div len bl;
  let rem = SZ.rem len bl;
  let z0: t = zero #t #w;

  let mut starr = [| z0; 8sz |];
  Mem.track starr;
  A.pts_to_len starr;
  A.pts_to_len starr;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (vst: Seq.seq t).
    pts_to c vc ** A.pts_to starr vst ** A.pts_to ivt #pi vi **
    pure (SZ.v vc <= 8 /\ Seq.length vst == 8 /\
          (forall (j: nat). j < SZ.v vc ==> Seq.index vst j == Seq.index (reveal p.iv <: Seq.seq t) j))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(ivt.(vc));
    A.((starr.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (reveal p.iv <: Seq.seq t);
  Seq.lemma_eq_elim vst_init (reveal p.iv <: Seq.seq t);

  let mut wsarr = [| z0; p.nrounds |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;

  let empty : erased (Seq.seq S8.t) = hide (Seq.empty #S8.t);
  Seq.lemma_eq_elim (Seq.append (reveal empty) (reveal vin)) (reveal vin);
  Math.euclidean_division_definition (SZ.v len) (block_len #t);
  hash_blocks p kt wsarr starr input bl 0sz nfull empty;
  tail_and_finish p kt wsarr starr out input len nfull (SZ.sub len rem) rem empty;

  Mem.wipe wsarr p.nrounds;
  Mem.wipe starr 8sz;
  ()
}

#pop-options

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 0"

(** {2 Hashing a message with a one-block prefix}

    [hash p (blk || input)] where [blk] is exactly one block, computed without
    ever building the concatenation: the prefix block is absorbed first and
    the rest of the message is read straight out of the caller's buffer.

    This is what HMAC's inner hash needs -- the prefix is [K0 ^ ipad] -- and it
    is the same generalization an incremental interface would use, which is
    why [hash_blocks] and [tail_and_finish] are stated for a ghost
    block-aligned prefix rather than for this special case. *)

(** The block counts of [hash_prefixed], one block of prefix ahead of [lin]
    bytes of message. *)
let prefixed_arith (bl lin: nat)
  : Lemma (requires bl > 0)
          (ensures (bl + lin) % bl == lin % bl /\
                   (bl + lin) - lin % bl == (1 + lin / bl) * bl /\
                   1 + lin / bl <= bl + lin /\ bl == 1 * bl)
  = Math.lemma_mod_plus lin 1 bl;
    Math.euclidean_division_definition lin bl;
    Math.distributivity_add_left 1 (lin / bl) bl;
    Math.multiply_fractions lin bl;
    Math.lemma_mult_le_left (lin / bl) 1 bl

fn hash_prefixed (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                 (kt: A.array t) (ivt: A.array t) (out: A.array S8.t)
                 (blk: A.array S8.t) (input: A.array S8.t) (lin: SZ.t)
                 (#pk: perm) (#vk: erased (Seq.seq t))
                 (#pi: perm) (#vi: erased (Seq.seq t))
                 (#vout: erased (Seq.seq S8.t))
                 (#pb: perm) (#vb: erased (Seq.seq S8.t))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout **
         A.pts_to blk #pb vb ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vout == (hash_bytes p) /\
               Seq.length vb == block_len #t /\
               SZ.fits (block_len #t + Seq.length vin) /\
               block_len #t + Seq.length vin < pow2 61 /\
               block_len #t + Seq.length vin < max_input #t)
         ** pure (SZ.v lin == Seq.length vin)
ensures exists* vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to out vout' **
  A.pts_to blk #pb vb ** A.pts_to input #pin vin **
  pure (Seq.length vb + Seq.length vin < max_input #t /\
        vout' == hash p (Seq.append vb vin))
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len out;
  A.pts_to_len blk;
  A.pts_to_len input;
  let bl = block_len_sz #t #w;
  let len = SZ.add bl lin;
  let nfull = SZ.div lin bl;
  let rem = SZ.rem lin bl;
  let z0: t = zero #t #w;

  let mut starr = [| z0; 8sz |];
  Mem.track starr;
  A.pts_to_len starr;
  A.pts_to_len starr;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc 8sz)
  invariant exists* (vc: SZ.t) (vst: Seq.seq t).
    pts_to c vc ** A.pts_to starr vst ** A.pts_to ivt #pi vi **
    pure (SZ.v vc <= 8 /\ Seq.length vst == 8 /\
          (forall (j: nat). j < SZ.v vc ==> Seq.index vst j == Seq.index (reveal p.iv <: Seq.seq t) j))
  decreases (8 - SZ.v (!c))
  {
    let vc = !c;
    let x = A.(ivt.(vc));
    A.((starr.(vc) <- x));
    c := SZ.add vc 1sz;
  };
  with vst_init. assert (A.pts_to starr vst_init);
  Seq.lemma_eq_intro vst_init (reveal p.iv <: Seq.seq t);
  Seq.lemma_eq_elim vst_init (reveal p.iv <: Seq.seq t);

  let mut wsarr = [| z0; p.nrounds |];
  Mem.track wsarr;
  A.pts_to_len wsarr;
  A.pts_to_len wsarr;

  Seq.lemma_len_append (reveal vb) (reveal vin);
  padded_shape #t (Seq.append vb vin);
  padded_index_block #t (Seq.append vb vin) 0;
  append_first_block #t (reveal vb) (reveal vin);
  update_block_impl p kt wsarr starr blk 0sz;
  repeati_g_zero (update_step p (padded #t (Seq.append vb vin))) (reveal p.iv);
  unfold_repeati_g 0 (update_step p (padded #t (Seq.append vb vin))) (reveal p.iv);

  prefixed_arith (block_len #t) (SZ.v lin);
  assert (pure (SZ.v rem == SZ.v len % block_len #t));
  assert (pure (SZ.v len - SZ.v rem == (1 + SZ.v nfull) * block_len #t));
  SZ.fits_lte (1 + SZ.v nfull) (block_len #t + SZ.v lin);

  hash_blocks p kt wsarr starr input bl 1sz nfull vb;
  let nb = SZ.add 1sz nfull;
  let base_in = SZ.sub lin rem;
  tail_and_finish p kt wsarr starr out input len nb base_in rem vb;

  Mem.wipe wsarr p.nrounds;
  Mem.wipe starr 8sz;
  ()
}

#pop-options
