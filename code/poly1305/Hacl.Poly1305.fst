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

(** The Poly1305 one-time authenticator.

    Four five-limb field elements on the stack -- the multiplier, the
    accumulator, the current block and the multiplication's scratch -- and one
    loop.  Each iteration is a load, five adds and the multiplication; there
    is no carry chain between the addition and the multiplication, because
    [fmul] accepts limbs two bits over the radix and [fadd] cannot produce
    more than that.

    The loop runs over the full blocks only.  A short final block is the one
    thing outside it, which is where the padding lives; the specification's
    [nblocks] is that count plus one when the length is not a multiple of
    sixteen, and [nblocks_split] is the only thing anyone needs to know about
    the arrangement.

    The loop and the two kinds of last block are three separate functions
    rather than one, because ChaCha20-Poly1305 needs them in a different
    order: it authenticates a concatenation of segments, each padded out to a
    whole number of blocks with zeros, so its last block of a segment is a
    full block and not Poly1305's own short one.  [absorb_blocks],
    [absorb_pad] and [absorb_seg] are what it uses; [absorb_tail] is what the
    plain MAC uses.

    The invariant is a congruence, not an equation: the accumulator is only
    ever equal to the specification's modulo [prime], because the carry chain
    inside [fmul] wraps the top of the number round to the bottom.  It is
    made an equation once, at the end, by [Hacl.Poly1305.Reduce.reduce]. *)
module Hacl.Poly1305

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Spec.Loops
open Spec.Poly1305.Field
open Hacl.Poly1305.Field
open Hacl.Poly1305.Load
open Hacl.Poly1305.Reduce

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Spec = Spec.Poly1305

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 What one iteration does to the accumulator} *)

(** One iteration.  The accumulator held [x], which is congruent to the
    specification's [y]; a block is added and the product taken, and the
    result is congruent to the specification's next value.  Congruence is all
    that survives [fmul], and all that is needed. *)
let step_cong (x y bv rr: nat)
  : Lemma (requires x % prime == y)
          (ensures ((x + bv) * rr) % prime == ((y + bv) * rr) % prime)
  = Math.lemma_mod_add_distr bv x prime;
    Math.lemma_mod_mul_distr_l (x + bv) rr prime;
    Math.lemma_mod_mul_distr_l (y + bv) rr prime

(** The block loop's invariant, advanced by one.  Stated over [16 * i] and
    never over [block_at]: [block_at] unfolds to a division, and a division
    inside a separation-logic query is what makes the solver give up. *)
let blocks_step (msg: Seq.seq S8.t) (r: nat) (i: nat) (x z acc: nat)
  : Lemma (requires 16 * i + 16 <= Seq.length msg /\
                    x % prime == Spec.blocks_acc msg 0 i r acc /\
                    z % prime ==
                      ((x + Spec.block_val (Seq.slice msg (16 * i) (16 * i + 16)))
                       * r) % prime)
          (ensures z % prime == Spec.blocks_acc msg 0 (i + 1) r acc)
  = unfold_repeati_g i (Spec.bstep msg 0 r) acc;
    step_cong x (Spec.blocks_acc msg 0 i r acc)
              (Spec.block_val (Seq.slice msg (16 * i) (16 * i + 16))) r

(** And the plain MAC's short last block, if any: the full blocks and the
    tail together are the whole message. *)
let last_block (msg: Seq.seq S8.t) (i: nat)
  : Lemma (requires 16 * i == Seq.length msg - Seq.length msg % 16 /\
                    Seq.length msg % 16 <> 0)
          (ensures Spec.block_at msg i ==
                   Seq.slice msg (16 * i) (16 * i + Seq.length msg % 16))
  = Spec.nblocks_split (Seq.length msg);
    Math.euclidean_division_definition (Seq.length msg) 16

let mac_tail (msg: Seq.seq S8.t) (r: nat) (n: nat) (q: nat) (a z: nat)
  : Lemma (requires q == Seq.length msg % 16 /\
                    16 * n == Seq.length msg - q /\
                    a == Spec.blocks_acc msg 0 n r 0 /\
                    z % prime ==
                      (if q = 0 then a
                       else ((a + Spec.block_val (Seq.slice msg (16 * n) (16 * n + q)))
                             * r) % prime))
          (ensures z % prime == Spec.poly msg r)
  = Spec.poly_is_acc msg r;
    Spec.poly_acc_split msg r 0;
    Math.euclidean_division_definition (Seq.length msg) 16;
    if q <> 0 then last_block msg n

(** The block of a segment's padded tail is a full block whose last bytes are
    zero -- not Poly1305's short block, which carries its length in the
    position of a one bit. *)
let pad_block (msg: Seq.seq S8.t) (tmp: Seq.seq S8.t) (off: nat) (blen: nat)
  : Lemma (requires blen < 16 /\ off + blen <= Seq.length msg /\
                    Seq.length tmp == 16 /\
                    (forall (k: nat). k < blen ==>
                       Seq.index tmp k == Seq.index msg (off + k)) /\
                    (forall (k: nat). blen <= k /\ k < 16 ==>
                       Seq.index tmp k == S8.classify 0uy))
          (ensures Seq.slice tmp 0 16 ==
                   Seq.append (Seq.slice msg off (off + blen))
                              (Spec.zeros (16 - blen)))
  = Seq.lemma_eq_intro (Seq.slice tmp 0 16)
                       (Seq.append (Seq.slice msg off (off + blen))
                                   (Spec.zeros (16 - blen)))

#pop-options

(** {2 The block loop}

    Whole multiples of four blocks go to [Hacl.Poly1305.Vec256.absorb_vec]
    first, when the processor and the length allow; the rest go one block at
    a time.  Inlined, because once the call to the vector path is in it the
    C compiler stops inlining it by itself, and the one-block loop is slower
    out of line. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

inline_for_extraction
fn absorb_blocks (h: A.array S64.t) (r: A.array S64.t) (d: A.array S64.t)
                 (e: A.array S64.t) (msg: A.array S8.t) (n: SZ.t)
                 (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
                 (#vd: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S64.t))
                 (#pm: perm) (#vmsg: erased (Seq.seq S8.t)) (#acc: erased nat)
requires A.pts_to h vh ** A.pts_to r vr ** A.pts_to d vd ** A.pts_to e ve **
         A.pts_to msg #pm vmsg **
         pure (Seq.length vh == 5 /\ Seq.length vr == 9 /\ Seq.length vd == 5 /\
               Seq.length ve == 5 /\ bounded vh 27 /\ bounded vr 26 /\ has5 vr /\
               16 * SZ.v n <= Seq.length vmsg /\
               feval vh % prime == reveal acc)
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t) (ve': Seq.seq S64.t).
  A.pts_to h vh' ** A.pts_to r vr ** A.pts_to d vd' ** A.pts_to e ve' **
  A.pts_to msg #pm vmsg **
  pure (Seq.length vh' == 5 /\ Seq.length vd' == 5 /\ Seq.length ve' == 5 /\
        bounded vh' 27 /\ bounded vr 26 /\ has5 vr /\ 16 * SZ.v n <= Seq.length vmsg /\
        feval vh' % prime ==
          Spec.blocks_acc vmsg 0 (SZ.v n) (feval vr) (reveal acc))
{
  A.pts_to_len h;
  A.pts_to_len msg;
  A.pts_to_len e;
  let k = Hacl.Poly1305.Vec256.absorb_vec h r d msg n #vh #vr #vd #pm #vmsg #acc;
  let mut i = k;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vh1: Seq.seq S64.t) (vd1: Seq.seq S64.t)
                    (ve1: Seq.seq S64.t).
    pts_to i vi ** A.pts_to h vh1 ** A.pts_to r vr ** A.pts_to d vd1 **
    A.pts_to e ve1 ** A.pts_to msg #pm vmsg **
    pure (SZ.v vi <= SZ.v n /\ Seq.length vh1 == 5 /\ Seq.length vd1 == 5 /\
          Seq.length ve1 == 5 /\ bounded vh1 27 /\
          feval vh1 % prime ==
            Spec.blocks_acc vmsg 0 (SZ.v vi) (feval vr) (reveal acc))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right 16 (SZ.v vi + 1) (SZ.v n);
    let off = SZ.mul vi 16sz;
    load_full e msg off;
    with vh0. assert (A.pts_to h vh0);
    fadd h e;
    fmul h r d;
    with vh2. assert (A.pts_to h vh2);
    blocks_step vmsg (feval vr) (SZ.v vi) (feval vh0) (feval vh2) (reveal acc);
    i := SZ.add vi 1sz;
  }
}

#pop-options

(** {2 The two kinds of last block} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Poly1305's own short block: the bytes, then a one, then nothing.  A
    separate function, and not an [if] inside the driver, because a Pulse [if]
    has to be the last statement of something for its two branches to be
    checked against one written-down postcondition. *)
fn absorb_tail (h: A.array S64.t) (r: A.array S64.t) (d: A.array S64.t)
               (e: A.array S64.t) (msg: A.array S8.t) (off: SZ.t) (blen: SZ.t)
               (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
               (#vd: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S64.t))
               (#pm: perm) (#vmsg: erased (Seq.seq S8.t)) (#acc: erased nat)
requires A.pts_to h vh ** A.pts_to r vr ** A.pts_to d vd ** A.pts_to e ve **
         A.pts_to msg #pm vmsg **
         pure (Seq.length vh == 5 /\ Seq.length vr == 9 /\ Seq.length vd == 5 /\
               Seq.length ve == 5 /\ bounded vh 27 /\ bounded vr 26 /\ has5 vr /\
               SZ.v blen < 16 /\ SZ.v off + SZ.v blen <= Seq.length vmsg /\
               feval vh % prime == reveal acc)
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t) (ve': Seq.seq S64.t).
  A.pts_to h vh' ** A.pts_to r vr ** A.pts_to d vd' ** A.pts_to e ve' **
  A.pts_to msg #pm vmsg **
  pure (Seq.length vh' == 5 /\ Seq.length vd' == 5 /\ Seq.length ve' == 5 /\
        bounded vh' 27 /\ bounded vr 26 /\ has5 vr /\
        SZ.v blen < 16 /\ SZ.v off + SZ.v blen <= Seq.length vmsg /\
        feval vh' % prime ==
          (if SZ.v blen = 0 then reveal acc
           else ((reveal acc +
                  Spec.block_val (Seq.slice vmsg (SZ.v off) (SZ.v off + SZ.v blen)))
                 * feval vr) % prime))
{
  if SZ.gt blen 0sz {
    load_last e msg off blen;
    with ve0. assert (A.pts_to e ve0);
    step_cong (feval vh) (reveal acc) (feval ve0) (feval vr);
    fadd h e;
    fmul h r d;
  } else {
    ()
  }
}

(** The AEAD's padded block: the bytes, then zeros out to sixteen, absorbed as
    a full block. *)
fn absorb_pad (h: A.array S64.t) (r: A.array S64.t) (d: A.array S64.t)
              (e: A.array S64.t) (msg: A.array S8.t) (off: SZ.t) (blen: SZ.t)
              (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
              (#vd: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S64.t))
              (#pm: perm) (#vmsg: erased (Seq.seq S8.t)) (#acc: erased nat)
requires A.pts_to h vh ** A.pts_to r vr ** A.pts_to d vd ** A.pts_to e ve **
         A.pts_to msg #pm vmsg **
         pure (Seq.length vh == 5 /\ Seq.length vr == 9 /\ Seq.length vd == 5 /\
               Seq.length ve == 5 /\ bounded vh 27 /\ bounded vr 26 /\ has5 vr /\
               0 < SZ.v blen /\ SZ.v blen < 16 /\
               SZ.v off + SZ.v blen <= Seq.length vmsg /\
               feval vh % prime == reveal acc)
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t) (ve': Seq.seq S64.t).
  A.pts_to h vh' ** A.pts_to r vr ** A.pts_to d vd' ** A.pts_to e ve' **
  A.pts_to msg #pm vmsg **
  pure (Seq.length vh' == 5 /\ Seq.length vd' == 5 /\ Seq.length ve' == 5 /\
        bounded vh' 27 /\ bounded vr 26 /\ has5 vr /\
        SZ.v blen < 16 /\ SZ.v off + SZ.v blen <= Seq.length vmsg /\
        feval vh' % prime ==
          ((reveal acc +
            Spec.block_val (Seq.append
                             (Seq.slice vmsg (SZ.v off) (SZ.v off + SZ.v blen))
                             (Spec.zeros (16 - SZ.v blen))))
           * feval vr) % prime)
{
  A.pts_to_len msg;
  let z8 = S8.classify 0uy;
  let mut tarr = [| z8; 16sz |];
  A.pts_to_len tarr;
  A.pts_to_len tarr;
  Hacl.Impl.Copy.copy_range tarr 0sz msg off blen;
  with vt. assert (A.pts_to tarr vt);
  pad_block vmsg vt (SZ.v off) (SZ.v blen);
  load_full e tarr 0sz;
  with ve0. assert (A.pts_to e ve0);
  step_cong (feval vh) (reveal acc) (feval ve0) (feval vr);
  fadd h e;
  fmul h r d;
  ()
}

#pop-options

(** {2 A padded segment}

    What ChaCha20-Poly1305 absorbs: the whole blocks of a slice, and then, if
    it does not end on a boundary, one more block of the tail followed by
    zeros.  The [if] is the last statement, which is what lets its two
    branches be checked against the postcondition's own [if]. *)

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"

fn absorb_seg (h: A.array S64.t) (r: A.array S64.t) (d: A.array S64.t)
              (e: A.array S64.t) (msg: A.array S8.t) (len: SZ.t)
              (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
              (#vd: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S64.t))
              (#pm: perm) (#vmsg: erased (Seq.seq S8.t)) (#acc: erased nat)
requires A.pts_to h vh ** A.pts_to r vr ** A.pts_to d vd ** A.pts_to e ve **
         A.pts_to msg #pm vmsg **
         pure (Seq.length vh == 5 /\ Seq.length vr == 9 /\ Seq.length vd == 5 /\
               Seq.length ve == 5 /\ bounded vh 27 /\ bounded vr 26 /\ has5 vr /\
               feval vh % prime == reveal acc)
         ** pure (SZ.v len == Seq.length vmsg)
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t) (ve': Seq.seq S64.t).
  A.pts_to h vh' ** A.pts_to r vr ** A.pts_to d vd' ** A.pts_to e ve' **
  A.pts_to msg #pm vmsg **
  pure (Seq.length vh' == 5 /\ Seq.length vd' == 5 /\ Seq.length ve' == 5 /\
        bounded vh' 27 /\ bounded vr 26 /\ has5 vr /\
        feval vh' % prime == Spec.seg_acc vmsg (feval vr) (reveal acc))
{
  A.pts_to_len msg;
  let n = SZ.div len 16sz;
  let q = SZ.rem len 16sz;
  Math.euclidean_division_definition (SZ.v len) 16;
  Math.lemma_mod_lt (SZ.v len) 16;
  absorb_blocks h r d e msg n #_ #_ #_ #_ #_ #_ #acc;
  let off = SZ.mul n 16sz;
  if SZ.gt q 0sz {
    absorb_pad h r d e msg off q
      #_ #_ #_ #_ #_ #_ #(hide (Spec.blocks_acc vmsg 0 (SZ.v n) (feval vr) acc));
  } else {
    ()
  }
}

#pop-options

(** {2 The driver} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn mac (out: A.array S8.t) (msg: A.array S8.t) (len: SZ.t) (key: A.array S8.t)
                (#vout: erased (Seq.seq S8.t))
                (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
                (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires A.pts_to out vout ** A.pts_to msg #pm vmsg ** A.pts_to key #pk vkey **
         pure (Seq.length vout == 16 /\ Seq.length vkey == 32)
         ** pure (SZ.v len == Seq.length vmsg)
ensures exists* (vout': Seq.seq S8.t).
  A.pts_to out vout' ** A.pts_to msg #pm vmsg ** A.pts_to key #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vout' == 16 /\
        vout' == Spec.poly1305 vmsg vkey)
{
  A.pts_to_len out;
  A.pts_to_len msg;
  A.pts_to_len key;
  let z = S64.zero;
  let mut rarr = [| z; 9sz |];
  A.pts_to_len rarr;
  A.pts_to_len rarr;
  let mut harr = [| z; 5sz |];
  A.pts_to_len harr;
  A.pts_to_len harr;
  let mut earr = [| z; 5sz |];
  A.pts_to_len earr;
  A.pts_to_len earr;
  let mut darr = [| z; 5sz |];
  A.pts_to_len darr;
  A.pts_to_len darr;

  load_r rarr key;
  set_zero harr;
  with vr. assert (A.pts_to rarr vr);
  Math.pow2_lt_compat 27 26;

  let full = SZ.div len 16sz;
  Math.multiply_fractions (SZ.v len) 16;
  Math.euclidean_division_definition (SZ.v len) 16;
  Math.lemma_mod_lt (SZ.v len) 16;
  absorb_blocks harr rarr darr earr msg full #_ #_ #_ #_ #_ #_ #(hide 0);

  (* The short final block, if there is one. *)
  let rem = SZ.rem len 16sz;
  let off = SZ.mul full 16sz;
  with vh0. assert (A.pts_to harr vh0);
  absorb_tail harr rarr darr earr msg off rem
    #_ #_ #_ #_ #_ #_ #(hide (Spec.blocks_acc vmsg 0 (SZ.v full) (feval vr) 0));
  with vh3. assert (A.pts_to harr vh3);
  mac_tail vmsg (feval vr) (SZ.v full) (SZ.v rem)
           (Spec.blocks_acc vmsg 0 (SZ.v full) (feval vr) 0) (feval vh3);

  reduce harr;
  with vhf. assert (A.pts_to harr vhf);
  store_tag out harr key;
  ()
}

#pop-options
