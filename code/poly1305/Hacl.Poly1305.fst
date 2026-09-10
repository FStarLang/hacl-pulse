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

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Spec = Spec.Poly1305

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** {2 The fold the loop computes} *)

(** The specification's step, at a fixed message and multiplier.  Named so
    that the loop invariant and the lemmas below agree on it. *)
let step (msg: Seq.seq S8.t) (r: nat) (i: nat) (acc: nat) : GTot nat =
  Spec.update r acc (Spec.block_at msg i)

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

(** The specification writes its step as a lambda and the invariant below
    writes it as [step]; [repeati_g_ext] is the only thing that relates them. *)
let poly_ext (msg: Seq.seq S8.t) (r: nat)
  : Lemma (Spec.poly msg r ==
           repeati_g (Spec.nblocks (Seq.length msg)) (step msg r) 0)
  = repeati_g_ext (Spec.nblocks (Seq.length msg))
                  (fun i acc -> Spec.update r acc (Spec.block_at msg i))
                  (step msg r) 0

(** A full block of the message is the sixteen bytes at [16 i]. *)
let full_block (msg: Seq.seq S8.t) (i: nat)
  : Lemma (requires 16 * i + 16 <= Seq.length msg)
          (ensures Spec.block_at msg i ==
                   Seq.slice msg (16 * i) (16 * i + 16))
  = Math.lemma_div_le (16 * i + 16) (Seq.length msg) 16;
    Math.cancel_mul_div (i + 1) 16;
    Spec.nblocks_split (Seq.length msg)

(** And the short one is what is left over. *)
let last_block (msg: Seq.seq S8.t) (i: nat)
  : Lemma (requires 16 * i == Seq.length msg - Seq.length msg % 16 /\
                    Seq.length msg % 16 <> 0)
          (ensures Spec.block_at msg i ==
                   Seq.slice msg (16 * i) (16 * i + Seq.length msg % 16))
  = Spec.nblocks_split (Seq.length msg);
    Math.euclidean_division_definition (Seq.length msg) 16

(** One whole iteration as a single implication over naturals, so that the
    loop body proves its invariant by instantiating one lemma rather than by
    chaining four facts inside a separation-logic query. *)
let step_of (msg: Seq.seq S8.t) (r: nat) (i: nat)
            (b: Seq.seq S8.t { Seq.length b <= 16 }) (x z: nat)
  : Lemma (requires x % prime == repeati_g i (step msg r) 0 /\
                    Spec.block_at msg i == b /\
                    z % prime == ((x + Spec.block_val b) * r) % prime)
          (ensures z % prime == repeati_g (i + 1) (step msg r) 0)
  = step_cong x (repeati_g i (step msg r) 0) (Spec.block_val b) r;
    unfold_repeati_g i (step msg r) 0

(** The two shapes the loop actually uses.  Neither mentions [block_at] or
    [nblocks]: those unfold to divisions, and a division inside a
    separation-logic query is what makes the solver give up.  Here the
    division is discharged once, in a context that holds nothing else. *)
let step_full (msg: Seq.seq S8.t) (r: nat) (i: nat) (x z: nat)
  : Lemma (requires 16 * i + 16 <= Seq.length msg /\
                    x % prime == repeati_g i (step msg r) 0 /\
                    z % prime ==
                      ((x + Spec.block_val (Seq.slice msg (16 * i) (16 * i + 16)))
                       * r) % prime)
          (ensures z % prime == repeati_g (i + 1) (step msg r) 0)
  = full_block msg i;
    step_of msg r i (Seq.slice msg (16 * i) (16 * i + 16)) x z

(** And the tail, whether or not there is one: the caller runs the loop over
    [len / 16] blocks and then one conditional block, and this says that the
    two together are [nblocks len] of them. *)
let step_tail (msg: Seq.seq S8.t) (r: nat) (i: nat) (n: nat) (a z: nat)
  : Lemma (requires n == Seq.length msg % 16 /\
                    16 * i == Seq.length msg - n /\
                    a == repeati_g i (step msg r) 0 /\
                    z % prime ==
                      (if n = 0 then a
                       else ((a + Spec.block_val (Seq.slice msg (16 * i) (16 * i + n)))
                             * r) % prime))
          (ensures z % prime ==
                   repeati_g (Spec.nblocks (Seq.length msg)) (step msg r) 0)
  = Spec.nblocks_split (Seq.length msg);
    Math.euclidean_division_definition (Seq.length msg) 16;
    if n = 0 then ()
    else (last_block msg i; unfold_repeati_g i (step msg r) 0)

#pop-options

(** {2 The short final block}

    A separate function, and not an [if] inside the driver, because a Pulse
    [if] has to be the last statement of something for its two branches to be
    checked against one written-down postcondition.  Here that postcondition
    is an [if] on the length as well: no block at all when the message divides
    into sixteens, and one padded block otherwise. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn absorb_tail (h: S.slice S64.t) (r: S.slice S64.t) (d: S.slice S64.t)
               (e: S.slice S64.t) (msg: S.slice S8.t) (off: SZ.t) (blen: SZ.t)
               (#vh: erased (Seq.seq S64.t)) (#vr: erased (Seq.seq S64.t))
               (#vd: erased (Seq.seq S64.t)) (#ve: erased (Seq.seq S64.t))
               (#pm: perm) (#vmsg: erased (Seq.seq S8.t)) (#acc: erased nat)
requires S.pts_to h vh ** S.pts_to r vr ** S.pts_to d vd ** S.pts_to e ve **
         S.pts_to msg #pm vmsg **
         pure (Seq.length vh == 5 /\ Seq.length vr == 5 /\ Seq.length vd == 5 /\
               Seq.length ve == 5 /\ bounded vh 27 /\ bounded vr 26 /\
               SZ.v blen < 16 /\ SZ.v off + SZ.v blen <= Seq.length vmsg /\
               feval vh % prime == reveal acc)
ensures exists* (vh': Seq.seq S64.t) (vd': Seq.seq S64.t) (ve': Seq.seq S64.t).
  S.pts_to h vh' ** S.pts_to r vr ** S.pts_to d vd' ** S.pts_to e ve' **
  S.pts_to msg #pm vmsg **
  pure (Seq.length vh' == 5 /\ Seq.length vd' == 5 /\ Seq.length ve' == 5 /\
        bounded vh' 27 /\ bounded vr 26 /\
        SZ.v blen < 16 /\ SZ.v off + SZ.v blen <= Seq.length vmsg /\
        feval vh' % prime ==
          (if SZ.v blen = 0 then reveal acc
           else ((reveal acc +
                  Spec.block_val (Seq.slice vmsg (SZ.v off) (SZ.v off + SZ.v blen)))
                 * feval vr) % prime))
{
  if SZ.gt blen 0sz {
    load_last e msg off blen;
    with ve0. assert (S.pts_to e ve0);
    step_cong (feval vh) (reveal acc) (feval ve0) (feval vr);
    fadd h e;
    fmul h r d;
  } else {
    ()
  }
}

#pop-options

(** {2 The block loop} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

fn poly1305_mac (out: S.slice S8.t) (msg: S.slice S8.t) (key: S.slice S8.t)
                (#vout: erased (Seq.seq S8.t))
                (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
                (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to msg #pm vmsg ** S.pts_to key #pk vkey **
         pure (Seq.length vout == 16 /\ Seq.length vkey == 32)
ensures exists* (vout': Seq.seq S8.t).
  S.pts_to out vout' ** S.pts_to msg #pm vmsg ** S.pts_to key #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vout' == 16 /\
        vout' == Spec.poly1305 vmsg vkey)
{
  S.pts_to_len out;
  S.pts_to_len msg;
  S.pts_to_len key;
  let z = S64.zero;
  let mut rarr = [| z; 5sz |];
  A.pts_to_len rarr;
  let r = S.from_array rarr 5sz;
  S.pts_to_len r;
  let mut harr = [| z; 5sz |];
  A.pts_to_len harr;
  let h = S.from_array harr 5sz;
  S.pts_to_len h;
  let mut earr = [| z; 5sz |];
  A.pts_to_len earr;
  let e = S.from_array earr 5sz;
  S.pts_to_len e;
  let mut darr = [| z; 5sz |];
  A.pts_to_len darr;
  let d = S.from_array darr 5sz;
  S.pts_to_len d;

  load_r r key;
  set_zero h;
  with vr. assert (S.pts_to r vr);
  let rn: erased nat = hide (feval vr);
  Math.pow2_lt_compat 27 26;
  repeati_g_zero (step vmsg (reveal rn)) 0;

  let len = S.len msg;
  let full = SZ.div len 16sz;

  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi full)
  invariant exists* (vi: SZ.t) (vh: Seq.seq S64.t) (vd: Seq.seq S64.t)
                    (ve: Seq.seq S64.t).
    pts_to i vi ** S.pts_to h vh ** S.pts_to r vr ** S.pts_to d vd **
    S.pts_to e ve ** S.pts_to msg #pm vmsg ** S.pts_to key #pk vkey **
    S.pts_to out vout ** S.is_from_array rarr r ** S.is_from_array harr h **
    S.is_from_array earr e ** S.is_from_array darr d **
    pure (SZ.v vi <= SZ.v full /\ Seq.length vh == 5 /\ Seq.length vd == 5 /\
          Seq.length ve == 5 /\ bounded vh 27 /\
          feval vh % prime ==
            repeati_g (SZ.v vi) (step vmsg (reveal rn)) 0)
  decreases (SZ.v full - SZ.v (!i))
  {
    let vi = !i;
    let off = SZ.mul vi 16sz;
    Math.lemma_mult_le_right 16 (SZ.v vi + 1) (SZ.v full);
    Math.multiply_fractions (SZ.v len) 16;
    load_full e msg off;
    with vh0. assert (S.pts_to h vh0);
    with ve. assert (S.pts_to e ve);
    fadd h e;
    with vh1. assert (S.pts_to h vh1);
    fmul h r d;
    with vh2. assert (S.pts_to h vh2);
    step_full vmsg (reveal rn) (SZ.v vi) (feval vh0) (feval vh2);
    i := SZ.add vi 1sz;
  };

  (* The short final block, if there is one. *)
  let rem = SZ.rem len 16sz;
  Math.euclidean_division_definition (SZ.v len) 16;
  Math.lemma_mod_lt (SZ.v len) 16;
  let off = SZ.mul full 16sz;
  with vh0. assert (S.pts_to h vh0);
  absorb_tail h r d e msg off rem
    #_ #_ #_ #_ #_ #_ #(hide (repeati_g (SZ.v full) (step vmsg (reveal rn)) 0));
  with vh3. assert (S.pts_to h vh3);
  step_tail vmsg (reveal rn) (SZ.v full) (SZ.v rem)
            (repeati_g (SZ.v full) (step vmsg (reveal rn)) 0) (feval vh3);

  reduce h;
  with vhf. assert (S.pts_to h vhf);
  poly_ext vmsg (reveal rn);
  store_tag out h key;
  S.to_array d;
  S.to_array e;
  S.to_array h;
  S.to_array r;
}

#pop-options
