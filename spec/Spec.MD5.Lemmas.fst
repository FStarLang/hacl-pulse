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

(** What the MD5 implementation needs to know about [Spec.MD5.padded].

    SHA-1 could borrow SHA-2's padding proofs wholesale, because SHA-1's
    padding {i is} SHA-2's at 32 bits.  MD5's is not: the bit length goes in
    little-endian, so [Spec.SHA2.Lemmas.tail_generic], which has [nat_to_be]
    in its hypotheses, does not apply.  The block structure is still shared
    -- sixty-four bytes, the same [block_at] -- so [block_at_eq] below lets
    the block-shaped lemmas cross over, and what has to be redone is the
    three lemmas that actually look at the padding bytes.

    The little-endian version is in one way {i simpler}.  SHA-2's length
    field is eight bytes for the 32-bit family and sixteen for the 64-bit
    one, and the implementation writes only the low eight, so [tail_generic]
    has to argue that the remaining bytes are zero because the message is
    short.  MD5's field is eight bytes, all of which are written -- and in
    little-endian the written bytes are the {i first} eight of the field, not
    the last. *)
module Spec.MD5.Lemmas

open Spec.MD5
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module U8 = FStar.UInt8
module L2 = Spec.SHA2.Lemmas

(** {2 What crosses over from SHA-2} *)

(** MD5's blocks are SHA-256's blocks: sixty-four bytes, cut out the same way.
    With this the block-shaped lemmas of [Spec.SHA2.Lemmas] -- and
    [Hacl.Hash.SHA1.Core]'s reasoning about them -- apply unchanged. *)
let block_at_eq (s: Seq.seq S8.t) (off: nat)
  : Lemma (Spec.SHA2.block_at #S32.t s off == block_at s off)
          [SMTPat (block_at s off)]
  = ()

let pad_zeros_eq (len: nat)
  : Lemma (Spec.SHA2.pad_zeros #S32.t len == pad_zeros len)
          [SMTPat (pad_zeros len)]
  = ()

let block_at_pointwise (s1 s2: Seq.seq S8.t) (o1 o2: nat)
  : Lemma (requires o1 + block_len <= Seq.length s1 /\ o2 + block_len <= Seq.length s2 /\
                    (forall (k: nat). k < block_len ==>
                       Seq.index s1 (o1 + k) == Seq.index s2 (o2 + k)))
          (ensures block_at s1 o1 == block_at s2 o2)
  = Seq.lemma_eq_intro (block_at s1 o1) (block_at s2 o2)

(** [pad_zeros] in the form the implementation computes it: from the length of
    the last partial block rather than from the whole message length.  The
    count of zeros does not depend on the byte order of the length field, so
    this is SHA-2's lemma. *)
let pad_zeros_alt (len: nat)
  : Lemma (let r = len % block_len in
           pad_zeros len ==
             (if r + 1 + len_len <= block_len
              then block_len - (r + 1 + len_len)
              else 2 * block_len - (r + 1 + len_len)))
  = L2.pad_zeros_alt #S32.t len

(** {2 The padding bytes} *)

(** The byte at each position of the padded message. *)
let padded_index (msg: Seq.seq S8.t { Seq.length msg < max_input })
                 (j: nat { j < Seq.length (padded msg) })
  : Lemma (
      let len = Seq.length msg in
      let z = pad_zeros len in
      Seq.index (padded msg) j ==
        (if j < len then Seq.index msg j
         else if j = len then S8.classify 0x80uy
         else if j < len + 1 + z then S8.classify 0uy
         else Seq.index (nat_to_le len_len (8 * len)) (j - (len + 1 + z))))
  = let len = Seq.length msg in
    let z = pad_zeros len in
    let pre = Seq.append (Seq.create 1 (S8.classify 0x80uy)) (Seq.create z (S8.classify 0uy)) in
    let pad = Seq.append pre (nat_to_le len_len (8 * len)) in
    assert (padded msg == Seq.append msg pad);
    if j < len then Seq.lemma_index_app1 msg pad j
    else begin
      Seq.lemma_index_app2 msg pad j;
      if j - len < 1 + z
      then Seq.lemma_index_app1 pre (nat_to_le len_len (8 * len)) (j - len)
      else Seq.lemma_index_app2 pre (nat_to_le len_len (8 * len)) (j - len);
      if j - len < 1 + z then begin
        if j = len
        then Seq.lemma_index_app1 (Seq.create 1 (S8.classify 0x80uy))
                                  (Seq.create z (S8.classify 0uy)) (j - len)
        else Seq.lemma_index_app2 (Seq.create 1 (S8.classify 0x80uy))
                                  (Seq.create z (S8.classify 0uy)) (j - len)
      end
    end

(** Length of the padded message, and of its tail beyond the whole blocks of
    the message itself. *)
let padded_shape (msg: Seq.seq S8.t { Seq.length msg < max_input })
  : Lemma (
      let len = Seq.length msg in
      Seq.length (padded msg) == len + 1 + pad_zeros len + len_len /\
      Seq.length (padded msg) % block_len == 0 /\
      len / block_len * block_len + (len % block_len + 1 + pad_zeros len + len_len) ==
        Seq.length (padded msg))
  = Math.euclidean_division_definition (Seq.length msg) block_len

(** A block that lies entirely inside the message is the same in the padded
    message. *)
let padded_index_block (msg: Seq.seq S8.t { Seq.length msg < max_input })
                       (o: nat { o + block_len <= Seq.length msg })
  : Lemma (block_at (padded msg) o == block_at msg o)
  = padded_len msg;
    let aux (k: nat { k < block_len })
      : Lemma (Seq.index (padded msg) (o + k) == Seq.index msg (o + k))
      = padded_index msg (o + k)
    in
    FStar.Classical.forall_intro aux;
    block_at_pointwise (padded msg) msg o o

(** A block of the second half is a block of the padded whole. *)
let padded_index_block_shift (pre: Seq.seq S8.t) (msg: Seq.seq S8.t) (o: nat)
  : Lemma (requires Seq.length pre + Seq.length msg < max_input /\
                    o + block_len <= Seq.length msg)
          (ensures block_at (padded (Seq.append pre msg)) (Seq.length pre + o) ==
                   block_at msg o)
  = let m = Seq.append pre msg in
    Seq.lemma_len_append pre msg;
    padded_index_block m (Seq.length pre + o);
    L2.append_index_right pre msg;
    block_at_pointwise m msg (Seq.length pre + o) o

(** The first block of a concatenation whose left half is exactly one block --
    the [K0 ^ ipad] block of HMAC. *)
let append_first_block (pre: Seq.seq S8.t) (s: Seq.seq S8.t)
  : Lemma (requires Seq.length pre == block_len)
          (ensures block_at (Seq.append pre s) 0 == block_at pre 0)
  = Seq.lemma_len_append pre s;
    let aux (k: nat { k < block_len })
      : Lemma (Seq.index (Seq.append pre s) (0 + k) == Seq.index pre (0 + k))
      = Seq.lemma_index_app1 pre s k
    in
    FStar.Classical.forall_intro aux;
    block_at_pointwise (Seq.append pre s) pre 0 0

(** {2 The tail buffer} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** The heart of the tail argument, stated without reference to MD5: the
    algorithm-dependent quantities are ordinary naturals, which keeps the
    arithmetic linear.  Unlike SHA-2's, the length field here is exactly
    eight bytes, and the implementation writes all of them -- byte [j] of the
    little-endian field sits at [ntail - 8 + j]. *)
let tail_generic_le (bl: pos) (len ntail: nat) (base: nat { base + len % bl == len })
                    (msg vt ps: Seq.seq S8.t)
  : Lemma
      (requires
        Seq.length msg == len /\ 8 * len < pow2 64 /\
        len % bl + 1 + 8 <= 2 * bl /\ base == len / bl * bl /\
        ntail == (if len % bl + 1 + 8 <= bl then bl else 2 * bl) /\
        ntail <= Seq.length vt /\
        Seq.length ps == base + ntail /\
        (forall (j: nat). j < Seq.length ps ==>
           Seq.index ps j ==
             (if j < len then Seq.index msg j
              else if j = len then S8.classify 0x80uy
              else if j < Seq.length ps - 8 then S8.classify 0uy
              else Seq.index (nat_to_le 8 (8 * len)) (j - (Seq.length ps - 8)))) /\
        (forall (k: nat). k < len % bl ==> Seq.index vt k == Seq.index msg (base + k)) /\
        Seq.index vt (len % bl) == S8.classify 0x80uy /\
        (forall (k: nat). len % bl < k /\ k < ntail - 8 ==> Seq.index vt k == S8.classify 0uy) /\
        (forall (j: nat). j < 8 ==>
           Seq.index vt (ntail - 8 + j) ==
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
        else if k < ntail - 8 then ()
        else begin
          let j = k - (ntail - 8) in
          nat_to_le_index 8 (8 * len) j
        end
    in
    FStar.Classical.forall_intro byte;
    L2.slices_of_bytes bl ntail base vt ps

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** The contents of the tail buffer the implementation builds: the last
    partial block, a [0x80] byte, zeros, and the little-endian bit length in
    the last eight bytes.  The hypotheses are exactly the pointwise facts the
    three writes of [Hacl.Hash.MD5.Core] leave behind. *)
let tail_bytes (msg: Seq.seq S8.t { Seq.length msg < max_input })
               (vt: Seq.seq S8.t) (ntail: nat) (base: nat)
  : Lemma
      (requires (
        let len = Seq.length msg in
        let rem = len % block_len in
        8 * len < pow2 64 /\ base == len / block_len * block_len /\
        ntail == (if rem + 1 + len_len <= block_len then block_len else 2 * block_len) /\
        ntail <= Seq.length vt /\
        (forall (k: nat). k < rem ==> Seq.index vt k == Seq.index msg (base + k)) /\
        Seq.index vt rem == S8.classify 0x80uy /\
        (forall (k: nat). rem < k /\ k < ntail - 8 ==> Seq.index vt k == S8.classify 0uy) /\
        (forall (j: nat). j < 8 ==>
           Seq.index vt (ntail - 8 + j) ==
             S8.classify (U8.uint_to_t ((8 * len / pow2 (8 * j)) % 256)))))
      (ensures
        (forall (o: nat). o + block_len <= ntail ==>
           block_at (padded msg) (base + o) == block_at vt o))
  = let len = Seq.length msg in
    let ps = padded msg in
    pad_zeros_alt len;
    padded_shape msg;
    FStar.Classical.forall_intro (padded_index msg);
    Math.euclidean_division_definition len block_len;
    tail_generic_le block_len len ntail base msg vt ps;
    let blk (o: nat { o + block_len <= ntail })
      : Lemma (block_at ps (base + o) == block_at vt o)
      = Seq.lemma_eq_elim (Seq.slice ps (base + o) (base + o + block_len))
                          (Seq.slice vt o (o + block_len))
    in
    FStar.Classical.forall_intro blk

#pop-options
