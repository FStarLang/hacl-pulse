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


(** The vector coders: the polynomial coders of {!Hacl.Impl.MLDSA.Encode}
    run over each entry in turn, the same loop as ML-KEM's
    {!Hacl.Impl.MLKEM.VecCodec}. *)
module Hacl.Impl.MLDSA.VecCodec

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Encode
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Encode
open Hacl.Impl.MLKEM.VecLemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub
module HSZ = Hacl.SizeT
module KZ = Spec.MLKEM.Zq
module KE = Spec.MLKEM.Encode
module T = FStar.Tactics.V2

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Flat sequences} *)

let flat_g_index (#a: Type) (k: pos) (m: pos) (f: (i: nat { i < k }) -> GTot (Seq.lseq a m))
                 (t: nat { t < k * m })
  : Lemma (KZ.div_lt t k m; Seq.index (KZ.flat_of_fun_g k m f) t == Seq.index (f (t / m)) (t % m))
  = Seq.init_ghost_index_ (k * m) (fun t -> KZ.div_lt t k m; Seq.index (f (t / m)) (t % m)) t

let flat_g_ext (#a: Type) (k: pos) (m: pos) (f g: (i: nat { i < k }) -> GTot (Seq.lseq a m))
  : Lemma (requires forall (i: nat { i < k }). f i == g i)
          (ensures KZ.flat_of_fun_g k m f == KZ.flat_of_fun_g k m g)
  = let aux (t: nat { t < k * m })
      : Lemma (Seq.index (KZ.flat_of_fun_g k m f) t == Seq.index (KZ.flat_of_fun_g k m g) t)
      = flat_g_index k m f t; flat_g_index k m g t in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (KZ.flat_of_fun_g k m f) (KZ.flat_of_fun_g k m g)

let blk (k: pos) (vs: Seq.seq zqt { Seq.length vs == k * n }) (i: nat { i < k })
  : Seq.seq zqt
  = Math.lemma_mult_le_right n (i + 1) k;
    Seq.slice vs (i * n) (i * n + n)

(** {2 What the vector coders compute} *)

let vpack (signed: bool) (b: zq) (d: pos { d <= 20 }) (k: pos)
          (vs: Seq.seq zqt { Seq.length vs == k * n })
  : GTot (Seq.lseq S8.t (k * (32 * d)))
  = KZ.flat_of_fun_g k (32 * d) (fun i -> simple_bit_pack d (src signed b (blk k vs i)))

let vpack_simple (d: pos { d <= 20 }) (k: pos) (b: zq) (vs: Seq.seq zqt { Seq.length vs == k * n })
  : Lemma (vpack false b d k vs == vec_simple_bit_pack d k (as_ints vs))
  = let aux (i: nat { i < k })
      : Lemma (simple_bit_pack d (src false b (blk k vs i)) ==
               simple_bit_pack d (KZ.flat_at k n (as_ints vs) i))
      = as_ints_flat_at k n vs i in
    Classical.forall_intro aux;
    flat_g_ext k (32 * d)
      (fun i -> simple_bit_pack d (src false b (blk k vs i)))
      (fun i -> simple_bit_pack d (KZ.flat_at k n (as_ints vs) i));
    assert (vpack false b d k vs == vec_simple_bit_pack d k (as_ints vs))
      by (T.norm [delta_only [`%vpack; `%vec_simple_bit_pack]]; T.smt ())

let vpack_signed (d: pos { d <= 20 }) (k: pos) (b: zq) (vs: Seq.seq zqt { Seq.length vs == k * n })
  : Lemma (vpack true b d k vs == vec_bit_pack b d k (as_zqs vs))
  = let aux (i: nat { i < k })
      : Lemma (simple_bit_pack d (src true b (blk k vs i)) ==
               bit_pack b d (vec_at #k (as_zqs vs) i))
      = as_zqs_at k vs i;
        src_signed b (blk k vs i) d in
    Classical.forall_intro aux;
    flat_g_ext k (32 * d)
      (fun i -> simple_bit_pack d (src true b (blk k vs i)))
      (fun i -> bit_pack b d (vec_at #k (as_zqs vs) i));
    assert (vpack true b d k vs == vec_bit_pack b d k (as_zqs vs))
      by (T.norm [delta_only [`%vpack; `%vec_bit_pack]]; T.smt ())

let pfield (signed: bool) (b: zq) (d: pos { d <= 20 }) (bl: Seq.lseq S8.t (32 * d))
  : GTot (Seq.lseq nat n)
  = Seq.init_ghost n (fun j -> field signed b d bl j)

let pfield_all (signed: bool) (b: zq) (d: pos { d <= 20 }) (bl: Seq.lseq S8.t (32 * d))
  : Lemma (forall (j: nat). j < n ==> Seq.index (pfield signed b d bl) j == field signed b d bl j)
  = let aux (j: nat { j < n }) : Lemma (Seq.index (pfield signed b d bl) j == field signed b d bl j)
      = Seq.init_ghost_index_ n (fun j -> field signed b d bl j) j in
    Classical.forall_intro aux

let vunpack (signed: bool) (b: zq) (d: pos { d <= 20 }) (k: pos)
            (vb: Seq.lseq S8.t (k * (32 * d)))
  : GTot (Seq.lseq nat (k * n))
  = KZ.flat_of_fun_g k n (fun i -> pfield signed b d (KZ.flat_at k (32 * d) vb i))

let vunpack_index (signed: bool) (b: zq) (d: pos { d <= 20 }) (k: pos)
                  (vb: Seq.lseq S8.t (k * (32 * d))) (t: nat { t < k * n })
  : Lemma (KZ.div_lt t k n;
           Seq.index (vunpack signed b d k vb) t ==
           field signed b d (KZ.flat_at k (32 * d) vb (t / n)) (t % n))
  = KZ.div_lt t k n;
    flat_g_index k n (fun i -> pfield signed b d (KZ.flat_at k (32 * d) vb i)) t;
    Seq.init_ghost_index_ n (fun j -> field signed b d (KZ.flat_at k (32 * d) vb (t / n)) j) (t % n)

let vunpack_blk (signed: bool) (b: zq) (d: pos { d <= 20 }) (k: pos)
                (vb: Seq.lseq S8.t (k * (32 * d))) (i: nat { i < k })
  : Lemma (forall (j: nat). j < n ==>
             Seq.index (KZ.flat_at k n (vunpack signed b d k vb) i) j ==
             field signed b d (KZ.flat_at k (32 * d) vb i) j)
  = let aux (j: nat { j < n })
      : Lemma (Seq.index (KZ.flat_at k n (vunpack signed b d k vb) i) j ==
               field signed b d (KZ.flat_at k (32 * d) vb i) j)
      = Math.lemma_mult_le_right n (i + 1) k;
        vunpack_index signed b d k vb (i * n + j);
        Math.lemma_div_plus j i n;
        Math.small_div j n;
        Math.lemma_mod_plus j i n;
        Math.small_mod j n in
    Classical.forall_intro aux

let vunpack_step (signed: bool) (b: zq) (d: pos { d <= 20 }) (k: pos)
                 (vb: Seq.lseq S8.t (k * (32 * d))) (i: nat { i < k })
                 (lo hi: nat) (b1: Seq.seq zqt)
  : Lemma (requires lo == i * (32 * d) /\ hi == lo + 32 * d /\ Seq.length b1 == n /\
                    hi <= k * (32 * d) /\
                    (forall (j: nat). j < n ==>
                       field_ok signed b d (Seq.slice vb lo hi) j (Seq.index b1 j)))
          (ensures forall (j: nat). j < n ==>
                     (S32.v (Seq.index b1 j) <: nat) ==
                     Seq.index (KZ.flat_at k n (vunpack signed b d k vb) i) j)
  = vunpack_blk signed b d k vb i;
    assert (Seq.slice vb lo hi == KZ.flat_at k (32 * d) vb i)

let vunpacked (signed: bool) (b: zq) (d: pos { d <= 20 }) (k: pos)
              (vb: Seq.lseq S8.t (k * (32 * d))) (v: Seq.seq zqt { Seq.length v == k * n }) : prop
  = (signed ==> as_zqs v == vec_bit_unpack b d k vb) /\
    (not signed ==> as_ints v == vec_simple_bit_unpack d k vb)

let vunpacked_intro (signed: bool) (b: zq) (d: pos { d <= 20 }) (k: pos)
                    (vb: Seq.lseq S8.t (k * (32 * d))) (v: Seq.seq zqt { Seq.length v == k * n })
  : Lemma (requires forall (t: nat). t < k * n ==> S32.v (Seq.index v t) == Seq.index (vunpack signed b d k vb) t)
          (ensures vunpacked signed b d k vb v)
  = if signed then begin
      let f = (fun i -> bit_unpack b d (KZ.flat_at k (32 * d) vb i)) in
      let aux (t: nat { t < k * n })
        : Lemma (Seq.index (as_zqs v) t == Seq.index (vec_bit_unpack b d k vb) t)
        = vunpack_index signed b d k vb t;
          KZ.div_lt t k n;
          flat_g_index k n f t;
          bu_index b d (KZ.flat_at k (32 * d) vb (t / n)) (t % n) in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro (as_zqs v) (vec_bit_unpack b d k vb)
    end else begin
      let f = (fun i -> simple_bit_unpack d (KZ.flat_at k (32 * d) vb i)) in
      let aux (t: nat { t < k * n })
        : Lemma (Seq.index (as_ints v) t == Seq.index (vec_simple_bit_unpack d k vb) t)
        = vunpack_index signed b d k vb t;
          KZ.div_lt t k n;
          flat_g_index k n f t;
          sbu_index d (KZ.flat_at k (32 * d) vb (t / n)) (t % n) in
      Classical.forall_intro aux;
      Seq.lemma_eq_intro (as_ints v) (vec_simple_bit_unpack d k vb)
    end

let vec_ok (d k: SZ.t) : prop = pack_ok d /\ 1 <= SZ.v k /\ SZ.v k <= 8

(** Index arithmetic for block [i]: hoisted so the loop bodies stay linear. *)
let blk_bounds (k: nat) (m: pos) (i: nat { i < k })
  : Lemma (i * m + m <= k * m /\ (i + 1) * m == i * m + m)
  = Math.lemma_mult_le_right m (i + 1) k;
    Math.distributivity_add_left i 1 m

#push-options "--z3rlimit 200"

(** [out <- ] the packing of each entry. *)
fn vec_pack (out: A.array S8.t) (f: A.array zqt)
            ([@@@FStar.Attributes.monomorphize] d: SZ.t) (signed: bool) (b: zqt)
            ([@@@FStar.Attributes.monomorphize] k: SZ.t)
            (#p: perm) (#vo: erased (Seq.seq S8.t)) (#vs: erased (Seq.seq zqt))
requires A.pts_to out vo ** A.pts_to f #p vs **
         pure (vec_ok d k /\ Seq.length vs == SZ.v k * n /\
               Seq.length vo == SZ.v k * (32 * SZ.v d))
ensures exists* v. A.pts_to out v ** A.pts_to f #p vs **
  pure (vec_ok d k /\ Seq.length vs == SZ.v k * n /\
        v == vpack signed (S32.v b) (SZ.v d) (SZ.v k) vs)
{
  A.pts_to_len out;
  A.pts_to_len f;
  HSZ.fits32 ();
  assert_norm (8 * (32 * 20) < pow2 32);
  assert_norm (8 * n < pow2 32);
  let el = SZ.mul 32sz d;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to f #p vs **
    pure (SZ.v vi <= SZ.v k /\ vec_ok d k /\
          Seq.length vs == SZ.v k * n /\
          Seq.length v == SZ.v k * (32 * SZ.v d) /\
          (forall (t: nat). t < SZ.v vi * (32 * SZ.v d) ==>
             Seq.index v t == Seq.index (vpack signed (S32.v b) (SZ.v d) (SZ.v k) vs) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    blk_bounds (SZ.v k) n (SZ.v vi);
    blk_bounds (SZ.v k) (32 * SZ.v d) (SZ.v vi);
    Math.lemma_mult_le_right (32 * SZ.v d) (SZ.v k) 8;
    Math.lemma_mult_le_left 8 (32 * SZ.v d) (32 * 20);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi * (32 * SZ.v d) + 32 * SZ.v d);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    let blo = SZ.mul vi el;
    let bhi = SZ.add blo el;
    KZ.flat_at_of_fun_g (SZ.v k) (32 * SZ.v d)
      (fun i -> simple_bit_pack (SZ.v d) (src signed (S32.v b) (blk (SZ.v k) vs i))) (SZ.v vi);
    with w0. assert (A.pts_to out w0);
    let bl = Sub.sub f lo hi;
    let obl = Sub.sub out blo bhi;
    pack_poly obl bl d signed b;
    with b1. assert (A.pts_to obl b1);
    Sub.unsub_id f (SZ.v lo) (SZ.v hi) bl;
    Sub.unsub out (SZ.v blo) (SZ.v bhi) obl;
    with w1. assert (A.pts_to out w1);
    flat_step (SZ.v k) (32 * SZ.v d) (fun (x: S8.t) -> x) (SZ.v vi) w0 w1 b1
              (vpack signed (S32.v b) (SZ.v d) (SZ.v k) vs);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  Seq.lemma_eq_intro v (vpack signed (S32.v b) (SZ.v d) (SZ.v k) vs);
  ()
}

(** [dst <- ] the unpacking of each block. *)
fn vec_unpack (dst: A.array zqt) (bs: A.array S8.t)
              ([@@@FStar.Attributes.monomorphize] d: SZ.t) (signed: bool) (b: zqt)
              ([@@@FStar.Attributes.monomorphize] k: SZ.t)
              (#p: perm) (#vd: erased (Seq.seq zqt)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to bs #p vb **
         pure (vec_ok d k /\ Seq.length vd == SZ.v k * n /\
               Seq.length vb == SZ.v k * (32 * SZ.v d))
ensures exists* v. A.pts_to dst v ** A.pts_to bs #p vb **
  pure (vec_ok d k /\ Seq.length v == SZ.v k * n /\
        Seq.length vb == SZ.v k * (32 * SZ.v d) /\
        vunpacked signed (S32.v b) (SZ.v d) (SZ.v k) vb v)
{
  A.pts_to_len dst;
  A.pts_to_len bs;
  HSZ.fits32 ();
  assert_norm (8 * (32 * 20) < pow2 32);
  assert_norm (8 * n < pow2 32);
  let el = SZ.mul 32sz d;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to bs #p vb **
    pure (SZ.v vi <= SZ.v k /\ vec_ok d k /\
          Seq.length v == SZ.v k * n /\
          Seq.length vb == SZ.v k * (32 * SZ.v d) /\
          (forall (t: nat). t < SZ.v vi * n ==>
             (S32.v (Seq.index v t) <: nat) ==
               Seq.index (vunpack signed (S32.v b) (SZ.v d) (SZ.v k) vb) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    blk_bounds (SZ.v k) n (SZ.v vi);
    blk_bounds (SZ.v k) (32 * SZ.v d) (SZ.v vi);
    Math.lemma_mult_le_right (32 * SZ.v d) (SZ.v k) 8;
    Math.lemma_mult_le_left 8 (32 * SZ.v d) (32 * 20);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi * (32 * SZ.v d) + 32 * SZ.v d);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    let blo = SZ.mul vi el;
    let bhi = SZ.add blo el;
    with w0. assert (A.pts_to dst w0);
    let bbl = Sub.sub bs blo bhi;
    let bl = Sub.sub dst lo hi;
    unpack_poly bl bbl d signed b;
    with b1. assert (A.pts_to bl b1);
    vunpack_step signed (S32.v b) (SZ.v d) (SZ.v k) vb (SZ.v vi) (SZ.v blo) (SZ.v bhi) b1;
    Sub.unsub_id bs (SZ.v blo) (SZ.v bhi) bbl;
    Sub.unsub dst (SZ.v lo) (SZ.v hi) bl;
    with w1. assert (A.pts_to dst w1);
    flat_step (SZ.v k) n (fun (x: zqt) -> (S32.v x <: nat)) (SZ.v vi) w0 w1 b1
              (vunpack signed (S32.v b) (SZ.v d) (SZ.v k) vb);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  vunpacked_intro signed (S32.v b) (SZ.v d) (SZ.v k) vb v;
  ()
}

#pop-options
#pop-options
