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

(** What the implementation needs to know about [Spec.SHA2.padded] that the
    definition does not say directly.

    The specification appends three sequences; the implementation writes bytes
    into a buffer.  [padded_index] turns the first into the second, and
    [block_at_pointwise] is how a byte-by-byte argument becomes an equality
    between blocks. *)
module Spec.SHA2.Lemmas

open Hacl.Secret.Word
open Hacl.Spec.Bytes
open Spec.SHA2

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module U8 = FStar.UInt8

let block_at_pointwise (#t: Type0) {| word t |} (s1 s2: Seq.seq S8.t) (o1 o2: nat)
  : Lemma (requires o1 + block_len #t <= Seq.length s1 /\ o2 + block_len #t <= Seq.length s2 /\
                    (forall (k: nat). k < block_len #t ==>
                       Seq.index s1 (o1 + k) == Seq.index s2 (o2 + k)))
          (ensures block_at #t s1 o1 == block_at #t s2 o2)
  = Seq.lemma_eq_intro (block_at #t s1 o1) (block_at #t s2 o2)

(** The byte at each position of the padded message. *)
let padded_index (#t: Type0) {| word t |} (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
                 (j: nat { j < Seq.length (padded #t msg) })
  : Lemma (
      let len = Seq.length msg in
      let z = pad_zeros #t len in
      let ll = len_len #t in
      Seq.index (padded #t msg) j ==
        (if j < len then Seq.index msg j
         else if j = len then S8.classify 0x80uy
         else if j < len + 1 + z then S8.classify 0uy
         else Seq.index (nat_to_be ll (8 * len)) (j - (len + 1 + z))))
  = let len = Seq.length msg in
    let z = pad_zeros #t len in
    let ll = len_len #t in
    let pre = Seq.append (Seq.create 1 (S8.classify 0x80uy)) (Seq.create z (S8.classify 0uy)) in
    let pad = Seq.append pre (nat_to_be ll (8 * len)) in
    assert (padded #t msg == Seq.append msg pad);
    if j < len then Seq.lemma_index_app1 msg pad j
    else begin
      Seq.lemma_index_app2 msg pad j;
      if j - len < 1 + z
      then Seq.lemma_index_app1 pre (nat_to_be ll (8 * len)) (j - len)
      else Seq.lemma_index_app2 pre (nat_to_be ll (8 * len)) (j - len);
      if j - len < 1 + z then begin
        if j = len
        then Seq.lemma_index_app1 (Seq.create 1 (S8.classify 0x80uy)) (Seq.create z (S8.classify 0uy)) (j - len)
        else Seq.lemma_index_app2 (Seq.create 1 (S8.classify 0x80uy)) (Seq.create z (S8.classify 0uy)) (j - len)
      end
    end

(** Length of the padded message, and of its tail beyond the whole blocks of
    the message itself. *)
let padded_shape (#t: Type0) {| word t |} (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
  : Lemma (
      let len = Seq.length msg in
      let bl = block_len #t in
      Seq.length (padded #t msg) == len + 1 + pad_zeros #t len + len_len #t /\
      Seq.length (padded #t msg) % bl == 0 /\
      len / bl * bl + (len % bl + 1 + pad_zeros #t len + len_len #t) == Seq.length (padded #t msg))
  = Math.euclidean_division_definition (Seq.length msg) (block_len #t)

(** [pad_zeros] in the form the implementation computes it: from the length of
    the last partial block rather than from the whole message length. *)
let pad_zeros_alt (#t: Type0) {| word t |} (len: nat)
  : Lemma (
      let bl = block_len #t in
      let ll = len_len #t in
      let r = len % bl in
      pad_zeros #t len == (if r + 1 + ll <= bl then bl - (r + 1 + ll) else 2 * bl - (r + 1 + ll)))
  = let bl = block_len #t in
    let ll = len_len #t in
    let r = len % bl in
    Math.lemma_mod_add_distr (1 + ll) len bl;
    assert ((len + 1 + ll) % bl == (r + 1 + ll) % bl);
    if r + 1 + ll < bl then begin
      Math.small_mod (r + 1 + ll) bl;
      Math.small_mod (bl - (r + 1 + ll)) bl
    end else if r + 1 + ll = bl then
      Math.multiple_modulo_lemma 1 bl
    else begin
      Math.lemma_mod_sub (r + 1 + ll) bl 1;
      Math.small_mod (r + 1 + ll - bl) bl;
      Math.small_mod (2 * bl - (r + 1 + ll)) bl
    end

(** A block that lies entirely inside the message is the same in the padded
    message.  This is what makes the first loop of the implementation read
    straight out of the caller's buffer. *)
let padded_index_block (#t: Type0) {| word t |} (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
                       (o: nat { o + block_len #t <= Seq.length msg })
  : Lemma (block_at #t (padded #t msg) o == block_at #t msg o)
  = padded_len #t msg;
    let aux (k: nat { k < block_len #t })
      : Lemma (Seq.index (padded #t msg) (o + k) == Seq.index msg (o + k))
      = padded_index #t msg (o + k)
    in
    FStar.Classical.forall_intro aux;
    block_at_pointwise #t (padded #t msg) msg o o

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** The heart of the tail argument, stated without the [word] class: the
    algorithm-dependent quantities appear as ordinary naturals, which keeps the
    arithmetic linear and the proof cheap. *)
let tail_generic (bl ll len ntail base: nat) (msg vt ps: Seq.seq S8.t)
  : Lemma
      (requires
        0 < bl /\ 8 <= ll /\
        Seq.length msg == len /\ 8 * len < pow2 64 /\
        len % bl + 1 + ll <= 2 * bl /\ base == len / bl * bl /\
        ntail == (if len % bl + 1 + ll <= bl then bl else 2 * bl) /\
        ntail <= Seq.length vt /\
        Seq.length ps == base + ntail /\
        (forall (j: nat). j < Seq.length ps ==>
           Seq.index ps j ==
             (if j < len then Seq.index msg j
              else if j = len then S8.classify 0x80uy
              else if j < Seq.length ps - ll then S8.classify 0uy
              else Seq.index (nat_to_be ll (8 * len)) (j - (Seq.length ps - ll)))) /\
        (forall (k: nat). k < len % bl ==> Seq.index vt k == Seq.index msg (base + k)) /\
        Seq.index vt (len % bl) == S8.classify 0x80uy /\
        (forall (k: nat). len % bl < k /\ k < ntail - 8 ==> Seq.index vt k == S8.classify 0uy) /\
        (forall (j: nat). j < 8 ==>
           Seq.index vt (ntail - 1 - j) ==
             S8.classify (U8.uint_to_t ((8 * len / pow2 (8 * j)) % 256))))
      (ensures
        (forall (o: nat). o + bl <= ntail ==>
           Seq.equal (Seq.slice ps (base + o) (base + o + bl)) (Seq.slice vt o (o + bl))))
  = let rem = len % bl in
    Math.euclidean_division_definition len bl;
    assert (base + rem == len);
    assert (base + ntail == Seq.length ps);
    let byte (k: nat { k < ntail })
      : Lemma (Seq.index vt k == Seq.index ps (base + k))
      = if k < rem then ()
        else if k = rem then ()
        else if k < ntail - ll then ()
        else begin
          let i = k - (ntail - ll) in
          let m = ll - 1 - i in
          assert (m == ntail - 1 - k);
          nat_to_be_index ll (8 * len) i;
          if m < 8 then
            assert (Seq.index vt (ntail - 1 - m) ==
                    S8.classify (U8.uint_to_t ((8 * len / pow2 (8 * m)) % 256)))
          else begin
            Math.pow2_le_compat (8 * m) 64;
            Math.small_div (8 * len) (pow2 (8 * m))
          end
        end
    in
    FStar.Classical.forall_intro byte;
    let blk (o: nat { o + bl <= ntail })
      : Lemma (Seq.equal (Seq.slice ps (base + o) (base + o + bl)) (Seq.slice vt o (o + bl)))
      = let aux (i: nat { i < bl })
          : Lemma (Seq.index (Seq.slice ps (base + o) (base + o + bl)) i ==
                   Seq.index (Seq.slice vt o (o + bl)) i)
          = Seq.lemma_index_slice ps (base + o) (base + o + bl) i;
            Seq.lemma_index_slice vt o (o + bl) i;
            byte (o + i);
            assert (Seq.index (Seq.slice ps (base + o) (base + o + bl)) i ==
                    Seq.index ps (base + (o + i)));
            assert (Seq.index (Seq.slice vt o (o + bl)) i == Seq.index vt (o + i))
        in
        FStar.Classical.forall_intro aux
    in
    FStar.Classical.forall_intro blk

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** The contents of the tail buffer the implementation builds: the last partial
    block, a [0x80] byte, zeros, and the big-endian bit length in the last
    [len_len] bytes.  The hypotheses are exactly the pointwise facts the three
    writes of [Hacl.Hash.SHA2.Core] leave behind -- note that only the low
    eight length bytes are written, the rest being zero because the message is
    shorter than [2^61] bytes. *)
let tail_bytes (#t: Type0) {| word t |} (msg: Seq.seq S8.t { Seq.length msg < max_input #t })
               (vt: Seq.seq S8.t) (ntail: nat) (base: nat)
  : Lemma
      (requires (
        let len = Seq.length msg in
        let bl = block_len #t in let ll = len_len #t in
        let rem = len % bl in
        8 * len < pow2 64 /\ base == len / bl * bl /\
        ntail == (if rem + 1 + ll <= bl then bl else 2 * bl) /\ ntail <= Seq.length vt /\
        (forall (k: nat). k < rem ==> Seq.index vt k == Seq.index msg (base + k)) /\
        Seq.index vt rem == S8.classify 0x80uy /\
        (forall (k: nat). rem < k /\ k < ntail - 8 ==> Seq.index vt k == S8.classify 0uy) /\
        (forall (j: nat). j < 8 ==>
           Seq.index vt (ntail - 1 - j) ==
             S8.classify (U8.uint_to_t ((8 * len / pow2 (8 * j)) % 256)))))
      (ensures (
        let len = Seq.length msg in
        let bl = block_len #t in
        (forall (o: nat). o + bl <= ntail ==>
           block_at #t (padded #t msg) (base + o) == block_at #t vt o)))
  = let len = Seq.length msg in
    let bl = block_len #t in
    let ll = len_len #t in
    let ps = padded #t msg in
    pad_zeros_alt #t len;
    padded_shape #t msg;
    FStar.Classical.forall_intro (padded_index #t msg);
    tail_generic bl ll len ntail base msg vt ps;
    let blk (o: nat { o + bl <= ntail })
      : Lemma (block_at #t ps (base + o) == block_at #t vt o)
      = Seq.lemma_eq_elim (Seq.slice ps (base + o) (base + o + bl)) (Seq.slice vt o (o + bl))
    in
    FStar.Classical.forall_intro blk

#pop-options
