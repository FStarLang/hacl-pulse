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

(** The message, as an eight by eight matrix.

    mu is cut into eight chunks of [bits] bytes.  Each chunk is read as a
    little-endian integer and its [bits]-wide fields, least significant
    first, become one row, each shifted up to the top of its [logq] bits so
    that the noise added during encapsulation lands below it.  Decoding adds
    half a step and truncates, which is rounding to the nearest multiple.

    Eight chunks of at most eight bytes is at most sixty-four bits, so the
    chunk is a single secret [UInt64] and no bignum appears. *)
module Hacl.Frodo.Encode

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

(** A window of a window is a window. *)
let slice_shift (v: Seq.seq S8.t) (base: nat) (nb: nat { base + nb <= Seq.length v })
                (j: nat { j <= nb })
  : Lemma (Seq.slice (Seq.slice v base (base + nb)) j nb == Seq.slice v (base + j) (base + nb))
  = Seq.slice_slice v base (base + nb) j nb

(** [key_encode] is written one cell at a time, left to right, and the
    loop invariant says only that the flat prefix written so far agrees with
    the specification.  Nothing quantified ever mentions [mu_chunk]: that
    would put [ii * bits p] under a quantifier, and a product of two
    variables under a quantifier is enough to make every other fact in the
    query unprovable too. *)
let prefix_step (v: Seq.seq S16.t) (spec: Seq.seq S16.t)
                (t: nat { t < Seq.length v /\ Seq.length v == Seq.length spec })
  : Lemma (requires forall (u: nat). u < t ==> Seq.index v u == Seq.index spec u)
          (ensures Seq.length (Seq.upd v t (Seq.index spec t)) == Seq.length spec /\
                   (forall (u: nat). u < t + 1 ==>
                      Seq.index (Seq.upd v t (Seq.index spec t)) u == Seq.index spec u))
  = ()

(** The one cell, named: this is the only place [mu_chunk] appears, and here
    the row index is a concrete term rather than a bound variable. *)
let ke_at (p: params) (mu: Seq.lseq S8.t (bytes_mu p))
          (i: nat { i < nbar }) (k: nat { k < nbar })
  : Lemma (i * nbar + k < nbar * nbar /\
           S16.v (Seq.index (F.key_encode p mu) (i * nbar + k)) ==
             F.ec_val p (F.mu_chunk p mu i) k)
  = M.index_bound nbar nbar i k;
    M.get_flat nbar nbar (F.key_encode p mu) (i * nbar + k);
    Math.lemma_div_plus k i nbar;
    Math.lemma_mod_plus k i nbar;
    Math.small_div k nbar;
    Math.small_mod k nbar;
    F.ec_bound p (F.mu_chunk p mu i) k

(** [bits p * k] is a product of two variables, so its bound is a hint. *)
let sh_ok (p: params) (k: nat { k < nbar })
  : Lemma (bits p * k < 64 /\ bits p * k + bits p <= 64)
  = Math.lemma_mult_le_right (bits p) (k + 1) nbar

(** The whole of one encoding step, as a pure fact: the 64-bit
    multiplication cannot wrap, so the shift is exact. *)
let ec_val_ok (p: params) (x: nat) (k: nat)
  : Lemma (ensures (let y = (x / pow2 (bits p * k)) % pow2 (bits p) in
                    (y * pow2 (logq p - bits p)) % pow2 64 == F.ec_val p x k /\
                    F.ec_val p x k < pow2 16))
  = F.ec_bound p x k;
    Math.pow2_le_compat 64 16;
    Math.small_mod (F.ec_val p x k) (pow2 64)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** [mu[base .. base + nb)] as a little-endian integer, read from the top
    down so that each step is one application of [le_nat]'s own recursion. *)
fn chunk (mu: A.array S8.t) (base: SZ.t) (nb: SZ.t { SZ.v nb <= 8 })
         (#p: perm) (#vmu: erased (Seq.seq S8.t))
requires A.pts_to mu #p vmu ** pure (SZ.v base + SZ.v nb <= Seq.length vmu)
returns x: S64.t
ensures A.pts_to mu #p vmu **
        pure (SZ.v base + SZ.v nb <= Seq.length vmu /\
              S64.v x == B.le_nat (Seq.slice vmu (SZ.v base) (SZ.v base + SZ.v nb)))
{
  A.pts_to_len mu;
  let mut acc = S64.zero;
  let mut j = nb;
  while (let vj = !j; SZ.gt vj 0sz)
  invariant exists* (vj: SZ.t) (vacc: S64.t).
    pts_to j vj ** pts_to acc vacc ** A.pts_to mu #p vmu **
    pure (SZ.v vj <= SZ.v nb /\
          S64.v vacc == B.le_nat (Seq.slice vmu (SZ.v base + SZ.v vj)
                                                (SZ.v base + SZ.v nb)) /\
          S64.v vacc < pow2 (8 * (SZ.v nb - SZ.v vj)))
  decreases (SZ.v (!j))
  {
    let vj = !j;
    let vacc = !acc;
    let k = SZ.sub vj 1sz;
    let b = A.(mu.(SZ.add base k));
    slice_shift vmu (SZ.v base) (SZ.v nb) (SZ.v k);
    slice_shift vmu (SZ.v base) (SZ.v nb) (SZ.v vj);
    B.le_nat_cons (Seq.slice vmu (SZ.v base) (SZ.v base + SZ.v nb)) (SZ.v k);
    B.le_nat_bound (Seq.slice vmu (SZ.v base + SZ.v k) (SZ.v base + SZ.v nb));
    Math.pow2_le_compat 64 (8 * (SZ.v nb - SZ.v k));
    acc := S64.add_mod (Cast.u8_to_u64 b) (S64.shift_left vacc 8ul);
    j := k;
  };
  !acc
}

(** [m <- key_encode p mu]. *)
fn key_encode ([@@@FStar.Attributes.monomorphize] p: params)
              (m: A.array S16.t) (mu: A.array S8.t)
              (#pm: perm) (#vm: erased (Seq.seq S16.t))
              (#vmu: erased (Seq.lseq S8.t (bytes_mu p)))
requires A.pts_to m vm ** A.pts_to mu #pm vmu **
         pure (Seq.length vm == nbar * nbar)
ensures exists* v. A.pts_to m v ** A.pts_to mu #pm vmu **
        pure (v == F.key_encode p vmu)
{
  A.pts_to_len m;
  A.pts_to_len mu;
  Hacl.SizeT.fits32 ();
  let nb = SZ.uint32_to_sizet p.bits;
  let up = U32.sub p.logq p.bits;
  let mask = S64.mask_low p.bits;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to m v ** A.pts_to mu #pm vmu **
    pure (SZ.v vi <= nbar /\ Seq.length v == nbar * nbar /\
          (forall (u: nat). u < SZ.v vi * nbar ==>
             Seq.index v u == Seq.index (F.key_encode p vmu) u))
  decreases (nbar - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right (SZ.v nb) (SZ.v vi + 1) nbar;
    let x = chunk mu (SZ.mul vi nb) nb;
    assert (pure (S64.v x == F.mu_chunk p vmu (SZ.v vi)));
    let mut k = 0sz;
    while (let vk = !k; SZ.lt vk 8sz)
    invariant exists* (vk: SZ.t) (v: Seq.seq S16.t).
      pts_to i vi ** pts_to k vk ** A.pts_to m v ** A.pts_to mu #pm vmu **
      pure (SZ.v vi < nbar /\ SZ.v vk <= nbar /\ Seq.length v == nbar * nbar /\
            (forall (u: nat). u < SZ.v vi * nbar + SZ.v vk ==>
               Seq.index v u == Seq.index (F.key_encode p vmu) u))
    decreases (nbar - SZ.v (!k))
    {
      let vk = !k;
      sh_ok p (SZ.v vk);
      let sh = U32.mul p.bits (SZ.sizet_to_uint32 vk);
      S64.logand_mask_low (S64.shift_right x sh) p.bits;
      let y = S64.logand (S64.shift_right x sh) mask;
      ec_val_ok p (S64.v x) (SZ.v vk);
      let z = S64.shift_left y up;
      Math.small_mod (F.ec_val p (S64.v x) (SZ.v vk)) (pow2 16);
      ke_at p vmu (SZ.v vi) (SZ.v vk);
      let w = Cast.u64_to_u16 z;
      assert (pure (w == Seq.index (F.key_encode p vmu) (SZ.v vi * nbar + SZ.v vk)));
      with vcur. assert (A.pts_to m vcur);
      prefix_step vcur (F.key_encode p vmu) (SZ.v vi * nbar + SZ.v vk);
      A.((m.(SZ.add (SZ.mul vi 8sz) vk) <- w));
      k := SZ.add vk 1sz;
    };
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to m v);
  Seq.lemma_eq_intro v (F.key_encode p vmu);
  assert (pure (v == F.key_encode p vmu));
}

#pop-options
