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

(** The message, recovered from the eight by eight matrix.

    The inverse of [Hacl.Frodo.Encode]: add half a step to each entry and
    truncate, which is rounding to the nearest multiple of [2^(logq - bits)];
    reassemble the eight rounded fields of a row into one secret [UInt64] and
    write that row out little-endian.

    Decoding is a module of its own only because it and encoding each keep
    the solver busy for the better part of half an hour, and two modules
    check in parallel. *)
module Hacl.Frodo.Decode

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Frodo.Params

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module M = Spec.Frodo.Matrix
module F = Spec.Frodo
module B = Hacl.Spec.Bytes
module Math = FStar.Math.Lemmas


(** As in [Hacl.Frodo.Encode], the loop invariant says only that the flat
    prefix written so far agrees with the specification.  Putting
    [row_val p m ii] under a quantifier would put [ii * bits p] there too,
    and a product of two variables under a quantifier is enough to make
    every other fact in the query unprovable as well. *)
(** [F.key_decode] is a [Seq.init_ghost] whose body divides by [bits p].
    Mentioning it under a quantifier lets the [Seq.index] trigger fire with a
    bound variable on the left of that division, and a division by a variable
    poisons the whole query -- after it, even [U32.v (8ul *^ j) == 8 * j]
    times out.  So the loop invariants talk about this opaque copy instead,
    and the two are reconciled once, at the very end. *)
[@@"opaque_to_smt"]
let kd (p: params) (m: M.matrix nbar nbar) : GTot (Seq.lseq S8.t (bytes_mu p)) =
  F.key_decode p m

let kd_eq (p: params) (m: M.matrix nbar nbar) : Lemma (kd p m == F.key_decode p m)
  = reveal_opaque (`%kd) kd

let prefix_step (v: Seq.seq S8.t) (spec: Seq.seq S8.t)
                (t: nat { t < Seq.length v /\ Seq.length v == Seq.length spec })
  : Lemma (requires forall (u: nat). u < t ==> Seq.index v u == Seq.index spec u)
          (ensures Seq.length (Seq.upd v t (Seq.index spec t)) == Seq.length spec /\
                   (forall (u: nat). u < t + 1 ==>
                      Seq.index (Seq.upd v t (Seq.index spec t)) u == Seq.index spec u))
  = ()

(** [nbar] is not marked [unfold], and after nine hundred seconds of
    quantifier instantiation the solver is in no state to delta-unfold it. *)
let nbar_8 () : Lemma (nbar == 8) = ()

(** [bits p * k] and [i * bits p] are products of two variables. *)
let sh_ok (p: params) (k: nat { k <= nbar })
  : Lemma (bits p * k <= 64 /\ (k < nbar ==> bits p * k < 64) /\ k * bits p <= bytes_mu p)
  = Math.lemma_mult_le_right (bits p) k nbar;
    Math.swap_mul k (bits p)

(** One step of the row accumulator: shifting the next rounded field into
    place cannot wrap, because the whole row is at most [bits p * nbar <= 64]
    bits wide. *)
let row_step (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar }) (k: nat { k < nbar })
             (acc: nat) (d: nat)
  : Lemma (requires acc == F.row_head p m i k /\
                    d == F.dc p (M.get nbar nbar m i k) /\
                    d < pow2 (bits p))
          (ensures bits p * k < 64 /\ bits p * (k + 1) <= 64 /\
                   (d * pow2 (bits p * k)) % pow2 64 == d * pow2 (bits p * k) /\
                   (acc + d * pow2 (bits p * k)) % pow2 64 == F.row_head p m i (k + 1))
  = sh_ok p k;
    sh_ok p (k + 1);
    F.row_head_bound p m i k;
    F.row_head_bound p m i (k + 1);
    Math.distributivity_add_right (bits p) k 1;
    Math.pow2_plus (bits p) (bits p * k);
    Math.lemma_mult_le_right (pow2 (bits p * k)) d (pow2 (bits p) - 1);
    Math.distributivity_sub_left (pow2 (bits p)) 1 (pow2 (bits p * k));
    Math.pow2_le_compat 64 (bits p * (k + 1));
    Math.small_mod (d * pow2 (bits p * k)) (pow2 64);
    Math.small_mod (acc + d * pow2 (bits p * k)) (pow2 64)

let pow2_8 () : Lemma (pow2 8 == 256) = Math.pow2_double_mult 7; assert_norm (pow2 8 == 256)

(** The one byte, named: the only place [row_val] appears, and here the row
    index is a concrete term rather than a bound variable. *)
let kd_at (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar }) (j: nat { j < bits p })
  : Lemma (i * bits p + j < bytes_mu p /\
           S8.v (Seq.index (kd p m) (i * bits p + j)) ==
             (F.row_val p m i / pow2 (8 * j)) % 256)
  = kd_eq p m;
    M.index_bound nbar (bits p) i j;
    Math.lemma_div_plus j i (bits p);
    Math.lemma_mod_plus j i (bits p);
    Math.small_div j (bits p);
    Math.small_mod j (bits p)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"


(** [mu <- key_decode p m]: round each entry to its nearest multiple of
    [2^(logq - bits)], reassemble eight of them into a row, and write the
    row out little-endian. *)
fn key_decode ([@@@FStar.Attributes.monomorphize] p: params)
              (mu: A.array S8.t) (m: A.array S16.t)
              (#pm: perm) (#vmu: erased (Seq.seq S8.t))
              (#vm: erased (M.matrix nbar nbar))
requires A.pts_to mu vmu ** A.pts_to m #pm vm **
         pure (Seq.length vmu == bytes_mu p)
ensures exists* v. A.pts_to mu v ** A.pts_to m #pm vm **
        pure (v == F.key_decode p vm)
{
  A.pts_to_len mu;
  A.pts_to_len m;
  Hacl.SizeT.fits32 ();
  let nb = SZ.uint32_to_sizet p.bits;
  let down = U32.sub p.logq p.bits;
  let half = S16.shift_left S16.one (U32.sub down 1ul);
  let bmask = S16.mask_low p.bits;
  let mut pos = 0sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (vpos: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** pts_to pos vpos ** A.pts_to mu v ** A.pts_to m #pm vm **
    pure (SZ.v vi <= nbar /\ Seq.length v == bytes_mu p /\
          SZ.v vpos == SZ.v vi * bits p /\ SZ.v vpos <= bytes_mu p /\
          (forall (u: nat). u < SZ.v vpos ==>
             Seq.index v u == Seq.index (kd p vm) u))
  decreases (nbar - SZ.v (!i))
  {
    let vi = !i;
    sh_ok p (SZ.v vi);
    sh_ok p (SZ.v vi + 1);
    let mut row = S64.zero;
    let mut k = 0sz;
    while (let vk = !k; SZ.lt vk 8sz)
    invariant exists* (vk: SZ.t) (vrow: S64.t) (vpos: SZ.t) (v: Seq.seq S8.t).
      pts_to i vi ** pts_to k vk ** pts_to row vrow ** pts_to pos vpos **
      A.pts_to mu v ** A.pts_to m #pm vm **
      pure (SZ.v vi < nbar /\ SZ.v vk <= nbar /\ Seq.length v == bytes_mu p /\
            SZ.v vpos == SZ.v vi * bits p /\ SZ.v vpos <= bytes_mu p /\
            (forall (u: nat). u < SZ.v vpos ==>
               Seq.index v u == Seq.index (kd p vm) u) /\
            S64.v vrow == F.row_head p vm (SZ.v vi) (SZ.v vk))
    decreases (nbar - SZ.v (!k))
    {
      let vk = !k;
      sh_ok p (SZ.v vk);
      sh_ok p (SZ.v vk + 1);
      let vrow = !row;
      let c = A.(m.(SZ.add (SZ.mul vi 8sz) vk));
      F.row_head_bound p vm (SZ.v vi) (SZ.v vk);
      F.row_head_bound p vm (SZ.v vi) (SZ.v vk + 1);
      S16.logand_mask_low (S16.shift_right (S16.add_mod c half) down) p.bits;
      let d = S16.logand (S16.shift_right (S16.add_mod c half) down) bmask;
      assert (pure (S16.v d == F.dc p (M.get nbar nbar vm (SZ.v vi) (SZ.v vk)) /\
                    S16.v d < pow2 (bits p)));
      row_step p vm (SZ.v vi) (SZ.v vk) (S64.v vrow) (S16.v d);
      row := S64.add_mod vrow (S64.shift_left (Cast.u16_to_u64 d) (U32.mul p.bits (SZ.sizet_to_uint32 vk)));
      k := SZ.add vk 1sz;
    };
    let vrow = !row;
    assert (pure (S64.v vrow == F.row_val p vm (SZ.v vi)));
    let mut j = 0sz;
    while (let vj = !j; SZ.lt vj nb)
    invariant exists* (vj: SZ.t) (vpos: SZ.t) (v: Seq.seq S8.t).
      pts_to i vi ** pts_to j vj ** pts_to pos vpos ** A.pts_to mu v ** A.pts_to m #pm vm **
      pure (SZ.v vi < nbar /\ SZ.v vj <= bits p /\ Seq.length v == bytes_mu p /\
            SZ.v vpos == SZ.v vi * bits p + SZ.v vj /\ SZ.v vpos <= bytes_mu p /\
            S64.v vrow == F.row_val p vm (SZ.v vi) /\
            (forall (u: nat). u < SZ.v vpos ==>
               Seq.index v u == Seq.index (kd p vm) u))
    decreases (bits p - SZ.v (!j))
    {
      let vj = !j;
      let vpos = !pos;
      let sh = U32.mul 8ul (SZ.sizet_to_uint32 vj);
      assert (pure (U32.v sh == 8 * SZ.v vj /\ U32.v sh < 64));
      let b = Cast.u64_to_u8 (S64.shift_right vrow sh);
      assert (pure (S8.v b == S64.v vrow / pow2 (U32.v sh) % pow2 8));
      pow2_8 ();
      assert (pure (S8.v b == (F.row_val p vm (SZ.v vi) / pow2 (8 * SZ.v vj)) % 256));
      Math.lemma_mult_le_right (bits p) (SZ.v vi + 1) nbar;
      Math.distributivity_add_left (SZ.v vi) 1 (bits p);
      kd_at p vm (SZ.v vi) (SZ.v vj);
      assert (pure (S8.v b == S8.v (Seq.index (kd p vm) (SZ.v vpos))));
      with vcur. assert (A.pts_to mu vcur);
      prefix_step vcur (kd p vm) (SZ.v vpos);
      A.((mu.(vpos) <- b));
      pos := SZ.add vpos 1sz;
      j := SZ.add vj 1sz;
    };
    Math.distributivity_add_left (SZ.v vi) 1 (bits p);
    sh_ok p (SZ.v vi + 1);
    i := SZ.add vi 1sz;
  };
  let vlast = !i;
  let vpos = !pos;
  with v. assert (A.pts_to mu v);
  nbar_8 ();
  sh_ok p nbar;
  Math.swap_mul nbar (bits p);
  assert (pure (SZ.v vlast == nbar /\ SZ.v vpos == bytes_mu p));
  assert (pure (Seq.length v == bytes_mu p /\
                (forall (u: nat). u < bytes_mu p ==>
                   Seq.index v u == Seq.index (kd p vm) u)));
  Seq.lemma_eq_intro v (kd p vm);
  kd_eq p vm;
  assert (pure (v == F.key_decode p vm));
}

#pop-options
