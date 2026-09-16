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

let key_encode_eq (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) (res: M.matrix nbar nbar)
  : Lemma (requires forall (i: nat) (k: nat). i < nbar /\ k < nbar ==>
                      S16.v (Seq.index res (i * nbar + k)) ==
                        F.ec_val p (F.mu_chunk p mu i) k)
          (ensures res == F.key_encode p mu)
  = let aux (t: nat { t < nbar * nbar })
      : Lemma (Seq.index res t == Seq.index (F.key_encode p mu) t)
      = M.div_lt t nbar nbar;
        Math.euclidean_division_definition t nbar;
        F.ec_bound p (F.mu_chunk p mu (t / nbar)) (t % nbar)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro res (F.key_encode p mu)

let key_decode_eq (p: params) (m: M.matrix nbar nbar) (res: Seq.lseq S8.t (bytes_mu p))
  : Lemma (requires forall (i: nat) (j: nat). i < nbar /\ j < bits p ==>
                      i * bits p + j < bytes_mu p /\
                      S8.v (Seq.index res (i * bits p + j)) ==
                        (F.row_val p m i / pow2 (8 * j)) % 256)
          (ensures res == F.key_decode p m)
  = let aux (t: nat { t < bytes_mu p })
      : Lemma (Seq.index res t == Seq.index (F.key_decode p m) t)
      = M.div_lt t nbar (bits p);
        Math.euclidean_division_definition t (bits p)
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro res (F.key_decode p m)

#push-options "--z3rlimit 600 --fuel 1 --ifuel 1"

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
          (forall (ii: nat) (kk: nat). ii < SZ.v vi /\ kk < nbar ==>
             S16.v (Seq.index v (ii * nbar + kk)) == F.ec_val p (F.mu_chunk p vmu ii) kk))
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
            (forall (ii: nat) (kk: nat). ii < SZ.v vi /\ kk < nbar ==>
               S16.v (Seq.index v (ii * nbar + kk)) == F.ec_val p (F.mu_chunk p vmu ii) kk) /\
            (forall (kk: nat). kk < SZ.v vk ==>
               S16.v (Seq.index v (SZ.v vi * nbar + kk)) ==
                 F.ec_val p (F.mu_chunk p vmu (SZ.v vi)) kk))
    decreases (nbar - SZ.v (!k))
    {
      let vk = !k;
      let sh = U32.mul p.bits (SZ.sizet_to_uint32 vk);
      S64.logand_mask_low (S64.shift_right x sh) p.bits;
      let y = S64.logand (S64.shift_right x sh) mask;
      Math.pow2_plus (bits p) (logq p - bits p);
      Math.pow2_le_compat 64 (logq p);
      let z = S64.shift_left y up;
      assert (pure (S64.v z == F.ec_val p (S64.v x) (SZ.v vk)));
      Math.pow2_le_compat 16 (logq p);
      A.((m.(SZ.add (SZ.mul vi 8sz) vk) <- Cast.u64_to_u16 z));
      k := SZ.add vk 1sz;
    };
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to m v);
  assert (pure (Seq.length v == nbar * nbar /\
                (forall (ii: nat) (kk: nat). ii < nbar /\ kk < nbar ==>
                   S16.v (Seq.index v (ii * nbar + kk)) ==
                     F.ec_val p (F.mu_chunk p vmu ii) kk)));
  key_encode_eq p vmu v;
  assert (pure (v == F.key_encode p vmu));
}

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
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 8sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to mu v ** A.pts_to m #pm vm **
    pure (SZ.v vi <= nbar /\ Seq.length v == bytes_mu p /\
          (forall (ii: nat) (jj: nat). ii < SZ.v vi /\ jj < bits p ==>
             ii * bits p + jj < bytes_mu p /\
             S8.v (Seq.index v (ii * bits p + jj)) ==
               (F.row_val p vm ii / pow2 (8 * jj)) % 256))
  decreases (nbar - SZ.v (!i))
  {
    let vi = !i;
    let mut row = S64.zero;
    let mut k = 0sz;
    while (let vk = !k; SZ.lt vk 8sz)
    invariant exists* (vk: SZ.t) (vrow: S64.t) (v: Seq.seq S8.t).
      pts_to i vi ** pts_to k vk ** pts_to row vrow ** A.pts_to mu v ** A.pts_to m #pm vm **
      pure (SZ.v vi < nbar /\ SZ.v vk <= nbar /\ Seq.length v == bytes_mu p /\
            (forall (ii: nat) (jj: nat). ii < SZ.v vi /\ jj < bits p ==>
               ii * bits p + jj < bytes_mu p /\
               S8.v (Seq.index v (ii * bits p + jj)) ==
                 (F.row_val p vm ii / pow2 (8 * jj)) % 256) /\
            S64.v vrow == F.row_head p vm (SZ.v vi) (SZ.v vk))
    decreases (nbar - SZ.v (!k))
    {
      let vk = !k;
      let vrow = !row;
      let c = A.(m.(SZ.add (SZ.mul vi 8sz) vk));
      F.row_head_bound p vm (SZ.v vi) (SZ.v vk);
      F.row_head_bound p vm (SZ.v vi) (SZ.v vk + 1);
      S16.logand_mask_low (S16.shift_right (S16.add_mod c half) down) p.bits;
      let d = S16.logand (S16.shift_right (S16.add_mod c half) down) bmask;
      assert (pure (S16.v d == F.dc p (M.get nbar nbar vm (SZ.v vi) (SZ.v vk))));
      Math.pow2_plus (bits p) (bits p * SZ.v vk);
      Math.pow2_le_compat 64 (bits p * (SZ.v vk + 1));
      row := S64.add_mod vrow (S64.shift_left (Cast.u16_to_u64 d) (U32.mul p.bits (SZ.sizet_to_uint32 vk)));
      k := SZ.add vk 1sz;
    };
    let vrow = !row;
    assert (pure (S64.v vrow == F.row_val p vm (SZ.v vi)));
    let mut j = 0sz;
    while (let vj = !j; SZ.lt vj nb)
    invariant exists* (vj: SZ.t) (v: Seq.seq S8.t).
      pts_to i vi ** pts_to j vj ** A.pts_to mu v ** A.pts_to m #pm vm **
      pure (SZ.v vi < nbar /\ SZ.v vj <= bits p /\ Seq.length v == bytes_mu p /\
            (forall (ii: nat) (jj: nat). ii < SZ.v vi /\ jj < bits p ==>
               ii * bits p + jj < bytes_mu p /\
               S8.v (Seq.index v (ii * bits p + jj)) ==
                 (F.row_val p vm ii / pow2 (8 * jj)) % 256) /\
            (forall (jj: nat). jj < SZ.v vj ==>
               SZ.v vi * bits p + jj < bytes_mu p /\
               S8.v (Seq.index v (SZ.v vi * bits p + jj)) ==
                 (F.row_val p vm (SZ.v vi) / pow2 (8 * jj)) % 256))
    decreases (bits p - SZ.v (!j))
    {
      let vj = !j;
      Math.lemma_mult_le_right (bits p) (SZ.v vi + 1) nbar;
      A.((mu.(SZ.add (SZ.mul vi nb) vj) <- Cast.u64_to_u8 (S64.shift_right vrow (U32.mul 8ul (SZ.sizet_to_uint32 vj)))));
      j := SZ.add vj 1sz;
    };
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to mu v);
  key_decode_eq p vm v;
  assert (pure (v == F.key_decode p vm));
}

#pop-options
