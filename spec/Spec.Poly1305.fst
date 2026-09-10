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

(** The Poly1305 one-time authenticator, as specified in RFC 8439.

    The specification is arithmetic on natural numbers: there are no limbs
    here, and no secret integers except in the byte sequences that come in and
    go out.  Everything the implementation does with five twenty-six-bit limbs
    is justified against this, in [Hacl.Poly1305.Field].

    Clamping is written the way RFC 8439 writes it -- as a mask on four
    particular bytes of the key -- rather than as one 128-bit [logand].  The
    two are the same, but the byte form is what an implementation can do
    limb by limb without a bit-level argument.

    As in [Spec.Blake2], the message is viewed as blocks without ever building
    the block sequence: [block_of] computes the [i]th block directly out of
    the message, so the implementation's loop invariant never has to mention a
    [Seq.append]. *)
module Spec.Poly1305

open Hacl.Spec.Loops
open Hacl.Spec.Bytes

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

(** {2 The field} *)

let prime : pos = pow2 130 - 5

let size_block = 16
let size_key = 32
let size_tag = 16

(** {2 The key}

    A Poly1305 key is thirty-two bytes: the first sixteen become the
    multiplier [r], after clamping, and the last sixteen the additive part
    [s]. *)

(** RFC 8439's clamp: bytes 3, 7, 11 and 15 keep their low four bits, and
    bytes 4, 8 and 12 lose their low two. *)
let clamp_byte (i: nat { i < 16 }) (b: S8.t) : S8.t =
  if i % 4 = 3 then S8.logand b (S8.classify 0x0fuy)
  else if i % 4 = 0 && i > 0 then S8.logand b (S8.classify 0xfcuy)
  else b

let clamp (rb: Seq.lseq S8.t 16) : Seq.lseq S8.t 16 =
  Seq.init 16 (fun i -> clamp_byte i (Seq.index rb i))

let r_of (k: Seq.lseq S8.t 32) : GTot nat =
  le_nat_bound (clamp (Seq.slice k 0 16));
  le_nat (clamp (Seq.slice k 0 16))

let s_of (k: Seq.lseq S8.t 32) : GTot nat =
  le_nat_bound (Seq.slice k 16 32);
  le_nat (Seq.slice k 16 32)

(** {2 Blocks}

    A block contributes its little-endian value plus a one placed just above
    its top byte -- for a full block that is [2^128], for a short final block
    it is lower.  That extra bit is what stops a message from being extended
    with zero bytes. *)

let block_val (b: Seq.seq S8.t { Seq.length b <= 16 }) : GTot nat =
  le_nat_bound b;
  le_nat b + pow2 (8 * Seq.length b)

let block_val_bound (b: Seq.seq S8.t { Seq.length b <= 16 })
  : Lemma (block_val b < pow2 129)
  = le_nat_bound b;
    Math.pow2_le_compat 128 (8 * Seq.length b);
    Math.pow2_le_compat 128 (8 * Seq.length b)

(** The number of blocks, and the [i]th one, computed straight out of the
    message. *)
let nblocks (len: nat) : nat = (len + 15) / 16

let block_len (len: nat) (i: nat { i < nblocks len }) : n: nat { 1 <= n /\ n <= 16 } =
  Math.euclidean_division_definition (len + 15) 16;
  Math.lemma_mod_lt (len + 15) 16;
  Math.lemma_mult_le_left 16 (i + 1) (nblocks len);
  if 16 * i + 16 <= len then 16 else len - 16 * i

let block_of (msg: Seq.seq S8.t) (i: nat { i < nblocks (Seq.length msg) })
  : b: Seq.seq S8.t { Seq.length b == block_len (Seq.length msg) i }
  = Seq.slice msg (16 * i) (16 * i + block_len (Seq.length msg) i)

(** [repeati_g] hands its step function every natural number, so the block
    view has to be total; out of range it is the empty sequence, which the
    fold never reaches. *)
let block_at (msg: Seq.seq S8.t) (i: nat) : b: Seq.seq S8.t { Seq.length b <= 16 } =
  if i < nblocks (Seq.length msg) then block_of msg i else Seq.empty

(** {2 The accumulator} *)

let update (r: nat) (acc: nat) (b: Seq.seq S8.t { Seq.length b <= 16 }) : GTot nat =
  ((acc + block_val b) * r) % prime

let poly (msg: Seq.seq S8.t) (r: nat) : GTot nat =
  repeati_g (nblocks (Seq.length msg))
            (fun i acc -> update r acc (block_at msg i))
            0

(** {2 The tag}

    The accumulator, plus [s], truncated to sixteen little-endian bytes. *)

let finish (acc: nat) (s: nat) : GTot (Seq.lseq S8.t 16) =
  nat_to_le 16 ((acc + s) % pow2 128)

let poly1305 (msg: Seq.seq S8.t) (k: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 16) =
  finish (poly msg (r_of k)) (s_of k)

(** {2 Facts about the block view}

    Exactly the shape [Spec.Blake2] needed: the last block is the only short
    one, and the block count is what the implementation's loop runs to. *)

let nblocks_bound (len: nat) : Lemma (16 * nblocks len < len + 16) =
  Math.euclidean_division_definition (len + 15) 16;
  Math.lemma_mod_lt (len + 15) 16

let nblocks_full (len: nat) (i: nat { i < nblocks len })
  : Lemma (requires i + 1 < nblocks len) (ensures block_len len i == 16)
  = Math.lemma_mult_le_left 16 (i + 2) (nblocks len);
    nblocks_bound len

let block_bound (len: nat) (i: nat { i < nblocks len })
  : Lemma (16 * i + block_len len i <= len)
  = nblocks_bound len;
    Math.lemma_mult_le_left 16 (i + 1) (nblocks len)

(** {2 Clamping, pointwise}

    [clamp] is a [Seq.init], so an implementation that masks seven particular
    bytes has to be matched against it index by index.  These two lemmas are
    that match: the first says what one index of the result is, and the
    second lifts sixteen of those to the sequence. *)

let clamp_index (rb: Seq.lseq S8.t 16) (i: nat { i < 16 })
  : Lemma (Seq.index (clamp rb) i == clamp_byte i (Seq.index rb i))
  = ()

let clamp_eq (rb: Seq.lseq S8.t 16) (vt: Seq.seq S8.t)
  : Lemma (requires Seq.length vt == 16 /\
                    (forall (i: nat). i < 16 ==>
                       Seq.index vt i == clamp_byte i (Seq.index rb i)))
          (ensures vt == clamp rb)
  = Seq.lemma_eq_intro vt (clamp rb)

(** The block count as a division and a remainder, which is how the
    implementation runs it: a loop over the full blocks and then, if there is
    a remainder, one short block. *)
let nblocks_split (len: nat)
  : Lemma (nblocks len == len / 16 + (if len % 16 = 0 then 0 else 1))
  = Math.euclidean_division_definition len 16;
    Math.lemma_mod_lt len 16;
    if len % 16 = 0 then Math.division_multiplication_lemma len 16 1

(** {2 Absorbing a message in segments}

    ChaCha20-Poly1305 authenticates a concatenation -- the additional data,
    the ciphertext and a length block, each padded out to a multiple of
    sixteen -- that no implementation can afford to build.  What it can do is
    absorb the pieces one after another into a running accumulator, and that
    is what this section justifies.

    Two things are needed.  [poly_acc] is [poly] started somewhere other than
    zero, so that "absorb this segment next" is a statement about a function
    of the accumulator.  [blocks_acc] is the same fold written over sixteen
    bytes at a fixed offset rather than over [block_at], which is what a loop
    can actually do: the last block of a segment is short in [block_at]'s view
    but is a full, zero-padded block in the concatenation's. *)

(** Both folds are written over a *named* step, not a lambda: two lambdas
    that are not the same source occurrence are two different constants to the
    solver, however obviously equal they look, and every one of these lemmas
    is an equation between two folds. *)
let pstep (msg: Seq.seq S8.t) (r: nat) (i: nat) (a: nat) : GTot nat =
  update r a (block_at msg i)

let poly_acc (msg: Seq.seq S8.t) (r: nat) (acc: nat) : GTot nat =
  repeati_g (nblocks (Seq.length msg)) (pstep msg r) acc

let poly_is_acc (msg: Seq.seq S8.t) (r: nat) : Lemma (poly msg r == poly_acc msg r 0)
  = repeati_g_ext (nblocks (Seq.length msg))
                  (fun i acc -> update r acc (block_at msg i))
                  (pstep msg r) 0

(** The sixteen bytes at [off], or nothing if they are not all there.  Total,
    so that it can appear under a lambda that F* must typecheck at every
    index. *)
let block16 (msg: Seq.seq S8.t) (off: nat) : GTot (b: Seq.seq S8.t { Seq.length b <= 16 }) =
  if off + 16 <= Seq.length msg then Seq.slice msg off (off + 16) else Seq.empty

let bstep (msg: Seq.seq S8.t) (off: nat) (r: nat) (i: nat) (a: nat) : GTot nat =
  update r a (block16 msg (off + 16 * i))

let blocks_acc (msg: Seq.seq S8.t) (off: nat) (n: nat) (r: nat) (acc: nat) : GTot nat =
  repeati_g n (bstep msg off r) acc

#push-options "--fuel 0 --ifuel 1 --z3rlimit 40"

(** On a message whose length is a multiple of sixteen the two views of a
    block agree at every index, including past the end, where both are
    empty. *)
let block_at_aligned (msg: Seq.seq S8.t) (i: nat)
  : Lemma (requires Seq.length msg % 16 == 0)
          (ensures block_at msg i == block16 msg (16 * i))
  = nblocks_split (Seq.length msg);
    if i < nblocks (Seq.length msg) then
      (Math.lemma_mult_le_left 16 (i + 1) (nblocks (Seq.length msg));
       Math.euclidean_division_definition (Seq.length msg) 16)
    else
      (Math.lemma_mult_le_left 16 (nblocks (Seq.length msg) + 1) (i + 1);
       Math.euclidean_division_definition (Seq.length msg) 16)

let poly_acc_aligned (msg: Seq.seq S8.t) (r: nat) (acc: nat)
  : Lemma (requires Seq.length msg % 16 == 0)
          (ensures poly_acc msg r acc ==
                   blocks_acc msg 0 (Seq.length msg / 16) r acc)
  = nblocks_split (Seq.length msg);
    FStar.Classical.forall_intro (Classical.move_requires (block_at_aligned msg));
    repeati_g_ext (nblocks (Seq.length msg)) (pstep msg r) (bstep msg 0 r) acc

(** Sixteen bytes of a prefix are sixteen bytes of the whole. *)
let block16_prefix (a b: Seq.seq S8.t) (off: nat)
  : Lemma (requires off + 16 <= Seq.length a)
          (ensures block16 (Seq.append a b) off == block16 a off)
  = Seq.lemma_eq_intro (Seq.slice (Seq.append a b) off (off + 16))
                       (Seq.slice a off (off + 16))

let blocks_acc_prefix (a b: Seq.seq S8.t) (n: nat) (r: nat) (acc: nat)
  : Lemma (requires 16 * n <= Seq.length a)
          (ensures blocks_acc (Seq.append a b) 0 n r acc == blocks_acc a 0 n r acc)
  = let aux (i: nat)
      : Lemma (i < n ==> block16 (Seq.append a b) (0 + 16 * i) == block16 a (0 + 16 * i))
      = if i < n then
          (Math.lemma_mult_le_left 16 (i + 1) n;
           block16_prefix a b (16 * i))
    in
    FStar.Classical.forall_intro aux;
    repeati_g_ext n (bstep (Seq.append a b) 0 r) (bstep a 0 r) acc

#pop-options

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"

(** Slices of a concatenation.  Both halves, because a segment's blocks come
    out of the left and everything after it out of the right. *)
let slice_append_r (a b: Seq.seq S8.t) (x: nat) (y: nat)
  : Lemma (requires x <= y /\ y <= Seq.length b)
          (ensures Seq.slice (Seq.append a b) (Seq.length a + x) (Seq.length a + y) ==
                   Seq.slice b x y)
  = Seq.lemma_eq_intro
      (Seq.slice (Seq.append a b) (Seq.length a + x) (Seq.length a + y))
      (Seq.slice b x y)

let slice_append_l (a b: Seq.seq S8.t) (x: nat) (y: nat)
  : Lemma (requires x <= y /\ y <= Seq.length a)
          (ensures Seq.slice (Seq.append a b) x y == Seq.slice a x y)
  = Seq.lemma_eq_intro (Seq.slice (Seq.append a b) x y) (Seq.slice a x y)

(** The block view of a concatenation whose first part is a whole number of
    blocks: the first [len a / 16] blocks are the first part's, and the rest
    are the second part's, shifted. *)
let block_at_append_l (a b: Seq.seq S8.t) (i: nat)
  : Lemma (requires Seq.length a % 16 == 0 /\ i < Seq.length a / 16)
          (ensures block_at (Seq.append a b) i == block_at a i)
  = nblocks_split (Seq.length a);
    nblocks_split (Seq.length a + Seq.length b);
    Math.euclidean_division_definition (Seq.length a) 16;
    Math.lemma_mult_le_left 16 (i + 1) (Seq.length a / 16);
    slice_append_l a b (16 * i) (16 * i + 16)

let block_at_append_r (a b: Seq.seq S8.t) (i: nat)
  : Lemma (requires Seq.length a % 16 == 0)
          (ensures block_at (Seq.append a b) (Seq.length a / 16 + i) == block_at b i)
  = let m = Seq.length a / 16 in
    nblocks_split (Seq.length a);
    nblocks_split (Seq.length b);
    nblocks_split (Seq.length a + Seq.length b);
    Math.euclidean_division_definition (Seq.length a) 16;
    Math.euclidean_division_definition (Seq.length b) 16;
    if i < nblocks (Seq.length b) then
      (block_bound (Seq.length b) i;
       slice_append_r a b (16 * i) (16 * i + block_len (Seq.length b) i))

let poly_acc_append (a b: Seq.seq S8.t) (r: nat) (acc: nat)
  : Lemma (requires Seq.length a % 16 == 0)
          (ensures poly_acc (Seq.append a b) r acc == poly_acc b r (poly_acc a r acc))
  = let ab = Seq.append a b in
    let m = Seq.length a / 16 in
    nblocks_split (Seq.length a);
    nblocks_split (Seq.length b);
    nblocks_split (Seq.length a + Seq.length b);
    Math.euclidean_division_definition (Seq.length a) 16;
    repeati_g_split m (nblocks (Seq.length ab)) (pstep ab r) acc;
    FStar.Classical.forall_intro
      (Classical.move_requires (block_at_append_l a b));
    repeati_g_ext m (pstep ab r) (pstep a r) acc;
    FStar.Classical.forall_intro
      (Classical.move_requires (block_at_append_r a b));
    repeati_g_ext (nblocks (Seq.length b))
                  (shift_g m (pstep ab r)) (pstep b r) (poly_acc a r acc)

#pop-options

(** {2 A padded segment}

    RFC 8439's [pad16]: zeros out to the next multiple of sixteen, and nothing
    at all when the length is already one.  Note that this padding is *not*
    Poly1305's own -- the padded segment's last block is a full sixteen-byte
    block, high bit and all, whose tail happens to be zero, whereas Poly1305's
    short block carries its length in the position of a one bit.  That is why
    an implementation cannot reach the AEAD's tag by calling the plain MAC on
    the pieces. *)

let zeros (n: nat) : Seq.lseq S8.t n = Seq.create n (S8.classify 0uy)

let pad16_len (n: nat) : nat = (16 - n % 16) % 16

let pad16 (b: Seq.seq S8.t) : Seq.seq S8.t =
  Seq.append b (zeros (pad16_len (Seq.length b)))

(** What absorbing a padded segment does to the accumulator: the whole blocks
    of the segment, and then, if it does not end on a boundary, one more block
    made of the tail followed by zeros. *)
let seg_tail (msg: Seq.seq S8.t) : GTot (b: Seq.seq S8.t { Seq.length b <= 16 }) =
  if Seq.length msg % 16 = 0 then Seq.empty
  else Seq.append (Seq.slice msg (Seq.length msg - Seq.length msg % 16) (Seq.length msg))
                  (zeros (16 - Seq.length msg % 16))

let seg_acc (msg: Seq.seq S8.t) (r: nat) (acc: nat) : GTot nat =
  let a1 = blocks_acc msg 0 (Seq.length msg / 16) r acc in
  if Seq.length msg % 16 = 0 then a1 else update r a1 (seg_tail msg)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 60"

let slice_pad (msg: Seq.seq S8.t) (z: Seq.seq S8.t)
  : Lemma (requires Seq.length msg % 16 <> 0 /\
                    Seq.length z == 16 - Seq.length msg % 16)
          (ensures (let n = Seq.length msg / 16 in
                    Math.euclidean_division_definition (Seq.length msg) 16;
                    Seq.slice (Seq.append msg z) (16 * n) (16 * n + 16) ==
                    Seq.append (Seq.slice msg (16 * n) (Seq.length msg)) z))
  = Math.euclidean_division_definition (Seq.length msg) 16;
    let n = Seq.length msg / 16 in
    Seq.lemma_eq_intro (Seq.slice (Seq.append msg z) (16 * n) (16 * n + 16))
                       (Seq.append (Seq.slice msg (16 * n) (Seq.length msg)) z)

let poly_acc_seg (msg: Seq.seq S8.t) (r: nat) (acc: nat)
  : Lemma (poly_acc (pad16 msg) r acc == seg_acc msg r acc)
  = let q = Seq.length msg % 16 in
    let n = Seq.length msg / 16 in
    Math.euclidean_division_definition (Seq.length msg) 16;
    Math.lemma_mod_lt (Seq.length msg) 16;
    if q = 0 then
      (Seq.lemma_eq_intro (pad16 msg) msg;
       poly_acc_aligned msg r acc)
    else
      (let z = zeros (16 - q) in
       let p = Seq.append msg z in
       Seq.lemma_eq_intro (pad16 msg) p;
       Math.cancel_mul_mod (n + 1) 16;
       Math.cancel_mul_div (n + 1) 16;
       poly_acc_aligned p r acc;
       unfold_repeati_g n (bstep p 0 r) acc;
       blocks_acc_prefix msg z n r acc;
       slice_pad msg z)

#pop-options

let pad16_aligned (b: Seq.seq S8.t)
  : Lemma (Seq.length (pad16 b) % 16 == 0)
  = Math.lemma_mod_lt (Seq.length b) 16;
    Math.euclidean_division_definition (Seq.length b) 16;
    if Seq.length b % 16 = 0 then Math.cancel_mul_mod (Seq.length b / 16) 16
    else Math.cancel_mul_mod (Seq.length b / 16 + 1) 16
