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

(** The matrix and the noise vector.

    Both are loops that fill one polynomial at a time from a seed the loop
    itself builds: [rho] and two indices for the matrix, a secret seed and a
    running public counter for the noise.  The matrix is public -- it is
    derived from a seed that travels in the clear -- so its indices are
    ordinary [size_t]s, while the noise counter is a public byte over a
    secret seed. *)
module Hacl.Impl.MLKEM.Gen

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.Sample
open Spec.MLKEM
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.Sampler
open Hacl.Impl.MLKEM.GenLemmas
open Hacl.Impl.Copy

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Sub = Hacl.Impl.Sub
module HSZ = Hacl.SizeT
module Mem = Hacl.Mem
module V = Hacl.Vec256

(** [SZ.rem] is specified via [SZ.mod_spec]; relate it to [%] explicitly. *)
let mod_spec_eq (a: SZ.t) (b: SZ.t { SZ.v b <> 0 })
  : Lemma (SZ.mod_spec (SZ.v a) (SZ.v b) == SZ.v a % SZ.v b)
  = Math.euclidean_division_definition (SZ.v a) (SZ.v b)

(** The seed of matrix entry [c]. *)
let entry_seed (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool) (c: nat { c < k * k })
  : Seq.lseq S8.t 34
  = div_lt c k k;
    matrix_seed rho (if tr then c % k else c / k) (if tr then c / k else c % k)

(** The first [c] entries of the matrix are in place. *)
[@@"opaque_to_smt"]
let gen_prefix (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool)
               (v: Seq.seq zqt) (c: nat { c <= k * k }) : prop =
  Seq.length v == k * k * n /\
  (Math.lemma_mult_le_right n c (k * k);
   forall (t: nat). t < c * n ==>
     S16.v (Seq.index v t) == Seq.index (gen_matrix k rho tr) t)

let gen_prefix_len (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool)
                   (v: Seq.seq zqt) (c: nat { c <= k * k })
  : Lemma (requires gen_prefix k rho tr v c) (ensures Seq.length v == k * k * n)
  = reveal_opaque (`%gen_prefix) (gen_prefix k rho tr v c)

let gen_prefix_zero (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool) (v: Seq.seq zqt)
  : Lemma (requires Seq.length v == k * k * n) (ensures gen_prefix k rho tr v 0)
  = reveal_opaque (`%gen_prefix) (gen_prefix k rho tr v 0)

let gen_prefix_done (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool) (v: Seq.seq zqt)
  : Lemma (requires gen_prefix k rho tr v (k * k))
          (ensures Seq.length v == k * k * n /\ as_zqs v == gen_matrix k rho tr)
  = reveal_opaque (`%gen_prefix) (gen_prefix k rho tr v (k * k));
    gen_entry_done k rho tr v

let gen_prefix_step (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool)
                    (c: nat { c < k * k })
                    (w0 w1: Seq.seq zqt) (b: Seq.seq zqt) (sd: Seq.seq S8.t)
  : Lemma (requires
      gen_prefix k rho tr w0 c /\ Seq.length w0 == k * k * n /\
      Seq.length w1 == k * k * n /\ Seq.length b == n /\
      (forall (t: nat). t < Seq.length w1 ==>
         Seq.index w1 t == (if c * n <= t && t < c * n + n
                            then Seq.index b (t - c * n) else Seq.index w0 t)) /\
      Seq.length sd == 34 /\ sd == entry_seed k rho tr c /\ as_poly b == sample_ntt sd)
    (ensures gen_prefix k rho tr w1 (c + 1))
  = reveal_opaque (`%gen_prefix) (gen_prefix k rho tr w0 c);
    gen_entry_step k rho tr c w0 w1 b sd;
    reveal_opaque (`%gen_prefix) (gen_prefix k rho tr w1 (c + 1))

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** [sd[32..34) <- ] the indices of entry [c]; the rest of [sd] is [rho]. *)
inline_for_extraction
fn set_seed (sd: A.array S8.t) (tr: bool) (k: SZ.t) (vc: SZ.t)
            (vr: erased (Seq.seq S8.t)) (#vsd0: erased (Seq.seq S8.t))
requires A.pts_to sd vsd0 **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ SZ.v vc < SZ.v k * SZ.v k /\
               Seq.length vsd0 == 34 /\ Seq.length vr == 32 /\
               (forall (t: nat). t < 32 ==> Seq.index vsd0 t == Seq.index vr t))
ensures exists* (vsd: Seq.seq S8.t). A.pts_to sd vsd **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ SZ.v vc < SZ.v k * SZ.v k /\
        Seq.length vsd == 34 /\ Seq.length vr == 32 /\
        (forall (t: nat). t < 32 ==> Seq.index vsd t == Seq.index vr t) /\
        vsd == entry_seed (SZ.v k) vr tr (SZ.v vc))
{
  A.pts_to_len sd;
  HSZ.fits32 ();
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  let ci = SZ.div vc k;
  let cj = SZ.rem vc k;
  mod_spec_eq vc k;
  assert (pure (SZ.v ci == SZ.v vc / SZ.v k /\ SZ.v cj == SZ.v vc % SZ.v k));
  div_lt (SZ.v vc) (SZ.v k) (SZ.v k);
  let bi = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 ci);
  let bj = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 cj);
  Math.small_mod (SZ.v ci) 256;
  Math.small_mod (SZ.v cj) 256;
  Math.small_mod (SZ.v ci) 4294967296;
  Math.small_mod (SZ.v cj) 4294967296;
  assert (pure (U8.v bi == SZ.v ci /\ U8.v bj == SZ.v cj));
  let b32 = (if tr then bi else bj);
  let b33 = (if tr then bj else bi);
  A.((sd.(32sz) <- S8.classify b32));
  A.((sd.(33sz) <- S8.classify b33));
  with vsd. assert (A.pts_to sd vsd);
  seed_eq vr (SZ.v ci) (SZ.v cj) tr vsd;
  assert (pure (vsd == entry_seed (SZ.v k) vr tr (SZ.v vc)));
}

(** [dst <- src], one polynomial. *)
inline_for_extraction
fn copy_poly (dst: A.array zqt) (src: A.array zqt)
             (#vd: erased (Seq.seq zqt)) (#vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src vs **
         pure (Seq.length vd == n /\ Seq.length vs == n)
ensures A.pts_to dst vs ** A.pts_to src vs
{
  A.pts_to_len dst;
  A.pts_to_len src;
  HSZ.fits32 ();
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src vs **
    pure (SZ.v vi <= n /\ Seq.length v == n /\ Seq.length vs == n /\
          (forall (t: nat). t < SZ.v vi ==> Seq.index v t == Seq.index vs t))
  decreases (n - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    A.(dst.(vi) <- x);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  assert (pure (Seq.equal v vs));
  rewrite (A.pts_to dst v) as (A.pts_to dst vs);
}

(** Entry [c] of the matrix, sampled elsewhere into [src], goes in. *)
inline_for_extraction
fn put_entry (dst: A.array zqt) (src: A.array zqt) (tr: bool) (k: SZ.t) (vc: SZ.t)
             (vr: erased (Seq.seq S8.t)) (vsd: erased (Seq.seq S8.t))
             (#vd: erased (Seq.seq zqt)) (#vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src vs **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ SZ.v vc < SZ.v k * SZ.v k /\
               Seq.length vr == 32 /\ Seq.length vs == n /\ Seq.length vsd == 34 /\
               gen_prefix (SZ.v k) vr tr vd (SZ.v vc) /\
               reveal vsd == entry_seed (SZ.v k) vr tr (SZ.v vc) /\
               as_poly vs == sample_ntt vsd)
ensures exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to src vs **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ SZ.v vc < SZ.v k * SZ.v k /\
        Seq.length vr == 32 /\ Seq.length vs == n /\
        gen_prefix (SZ.v k) vr tr v (SZ.v vc + 1))
{
  gen_prefix_len (SZ.v k) vr tr vd (SZ.v vc);
  A.pts_to_len dst;
  HSZ.fits32 ();
  assert_norm (4 * 4 * n < pow2 32);
  Math.lemma_mult_le_right n (SZ.v vc + 1) (SZ.v k * SZ.v k);
  Math.distributivity_add_left (SZ.v vc) 1 n;
  Math.lemma_mult_le_right (SZ.v k) (SZ.v k) 4;
  Math.lemma_mult_le_left 4 (SZ.v k) 4;
  Math.lemma_mult_le_right n (SZ.v k * SZ.v k) 16;
  SZ.fits_u32_implies_fits (SZ.v vc * n + n);
  let lo = SZ.mul vc 256sz;
  let hi = SZ.add lo 256sz;
  let blk = Sub.sub dst lo hi;
  copy_poly blk src;
  Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
  with w1. assert (A.pts_to dst w1);
  assert (pure (SZ.v lo == SZ.v vc * n /\ SZ.v hi == SZ.v vc * n + n));
  assert (pure (Seq.length w1 == SZ.v k * SZ.v k * n));
  assert (pure (forall (t: nat). t < Seq.length w1 ==>
         Seq.index w1 t == (if SZ.v vc * n <= t && t < SZ.v vc * n + n
                            then Seq.index vs (t - SZ.v vc * n) else Seq.index vd t)));
  gen_prefix_step (SZ.v k) vr tr (SZ.v vc) vd w1 vs vsd;
  assert (pure (gen_prefix (SZ.v k) vr tr w1 (SZ.v vc + 1)));
  assert (pure (Seq.length vs == n));
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Matrix entries [c .. c + 4), sampled together.  Uses AVX2: the caller
    checks {!Hacl.Vec256.supported}. *)
fn gen_entries4 (dst: A.array zqt) (rho: A.array S8.t) (tr: bool) (k: SZ.t) (vc: SZ.t)
                (#vd: erased (Seq.seq zqt)) (#p: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #p vr **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ SZ.v vc + 4 <= SZ.v k * SZ.v k /\
               Seq.length vr == 32 /\ gen_prefix (SZ.v k) vr tr vd (SZ.v vc))
ensures exists* (v: Seq.seq zqt). A.pts_to dst v ** A.pts_to rho #p vr **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ SZ.v vc + 4 <= SZ.v k * SZ.v k /\
        Seq.length vr == 32 /\ gen_prefix (SZ.v k) vr tr v (SZ.v vc + 4))
{
  A.pts_to_len rho;
  HSZ.fits32 ();
  assert_norm (4 * 4 < pow2 32);
  SZ.fits_u32_implies_fits (SZ.v vc + 3);
  let vc1 = SZ.add vc 1sz;
  let vc2 = SZ.add vc 2sz;
  let vc3 = SZ.add vc 3sz;
  let z8 = S8.classify 0uy;
  let mut sd0 = [| z8; 34sz |];
  Mem.track sd0;
  let mut sd1 = [| z8; 34sz |];
  Mem.track sd1;
  let mut sd2 = [| z8; 34sz |];
  Mem.track sd2;
  let mut sd3 = [| z8; 34sz |];
  Mem.track sd3;
  copy_prefix sd0 rho 32sz;
  copy_prefix sd1 rho 32sz;
  copy_prefix sd2 rho 32sz;
  copy_prefix sd3 rho 32sz;
  set_seed sd0 tr k vc vr;
  set_seed sd1 tr k vc1 vr;
  set_seed sd2 tr k vc2 vr;
  set_seed sd3 tr k vc3 vr;
  with e0. assert (A.pts_to sd0 e0);
  with e1. assert (A.pts_to sd1 e1);
  with e2. assert (A.pts_to sd2 e2);
  with e3. assert (A.pts_to sd3 e3);
  let z16 : zqt = S16.classify 0us;
  let mut p0 = [| z16; 256sz |];
  Mem.track p0;
  A.pts_to_len p0;
  let mut p1 = [| z16; 256sz |];
  Mem.track p1;
  A.pts_to_len p1;
  let mut p2 = [| z16; 256sz |];
  Mem.track p2;
  A.pts_to_len p2;
  let mut p3 = [| z16; 256sz |];
  Mem.track p3;
  A.pts_to_len p3;
  assert (pure (Seq.length e0 == 34 /\ Seq.length e1 == 34 /\
                Seq.length e2 == 34 /\ Seq.length e3 == 34));
  with q0 q1 q2 q3. assert (A.pts_to p0 q0 ** A.pts_to p1 q1 ** A.pts_to p2 q2 ** A.pts_to p3 q3);
  assert (pure (Seq.length q0 == n /\ Seq.length q1 == n /\
                Seq.length q2 == n /\ Seq.length q3 == n));
  sample_ntt4_impl p0 p1 p2 p3 sd0 sd1 sd2 sd3 34sz;
  put_entry dst p0 tr k vc vr e0;
  put_entry dst p1 tr k vc1 vr e1;
  put_entry dst p2 tr k vc2 vr e2;
  put_entry dst p3 tr k vc3 vr e3;
  Mem.wipe p3 256sz;
  Mem.wipe p2 256sz;
  Mem.wipe p1 256sz;
  Mem.wipe p0 256sz;
  Mem.wipe sd3 34sz;
  Mem.wipe sd2 34sz;
  Mem.wipe sd1 34sz;
  Mem.wipe sd0 34sz;
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Algorithm 13 line 3 and Algorithm 14 line 4: the [k x k] matrix, row
    major, [SampleNTT] of [rho] and the two indices.  [tr] swaps the two
    indices, which is how the standard transposes. *)
fn gen_matrix_impl (dst: A.array zqt) (rho: A.array S8.t) (tr: bool) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   (#vd: erased (Seq.seq zqt)) (#p: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to rho #p vr **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\
               Seq.length vd == SZ.v k * SZ.v k * n /\ Seq.length vr == 32)
ensures exists* v. A.pts_to dst v ** A.pts_to rho #p vr **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ Seq.length vr == 32 /\
        Seq.length v == SZ.v k * SZ.v k * n /\
        as_zqs v == gen_matrix (SZ.v k) vr tr)
{
  A.pts_to_len dst;
  A.pts_to_len rho;
  HSZ.fits32 ();
  assert_norm (4 * 4 * n < pow2 32);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  let z8 = S8.classify 0uy;
  let mut sd = [| z8; 34sz |];
  Mem.track sd;
  A.pts_to_len sd;
  copy_prefix sd rho 32sz;
  gen_prefix_zero (SZ.v k) vr tr vd;
  let kk = SZ.mul k k;
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc kk)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt) (vsd: Seq.seq S8.t).
    pts_to c vc ** A.pts_to dst v ** A.pts_to rho #p vr ** A.pts_to sd vsd **
    pure (SZ.v vc <= SZ.v k * SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
          Seq.length v == SZ.v k * SZ.v k * n /\ Seq.length vr == 32 /\
          Seq.length vsd == 34 /\
          (forall (t: nat). t < 32 ==> Seq.index vsd t == Seq.index vr t) /\
          gen_prefix (SZ.v k) vr tr v (SZ.v vc))
  decreases (SZ.v k * SZ.v k - SZ.v (!c))
  {
    let vc = !c;
    with v0. assert (A.pts_to dst v0);
    assert (pure (gen_prefix (SZ.v k) vr tr v0 (SZ.v vc)));
    SZ.fits_u32_implies_fits (SZ.v vc + 4);
    if (SZ.lte (SZ.add vc 4sz) kk && V.supported ()) {
      gen_entries4 dst rho tr k vc;
      with v1. assert (A.pts_to dst v1);
      gen_prefix_len (SZ.v k) vr tr v1 (SZ.v vc + 4);
      c := SZ.add vc 4sz;
    } else {
      Math.lemma_mult_le_right n (SZ.v vc + 1) (SZ.v k * SZ.v k);
      Math.distributivity_add_left (SZ.v vc) 1 n;
      Math.lemma_mult_le_right (SZ.v k) (SZ.v k) 4;
      Math.lemma_mult_le_left 4 (SZ.v k) 4;
      Math.lemma_mult_le_right n (SZ.v k * SZ.v k) 16;
      SZ.fits_u32_implies_fits (SZ.v vc * n + n);
      let lo = SZ.mul vc 256sz;
      let hi = SZ.add lo 256sz;
      set_seed sd tr k vc vr;
      with vsd. assert (A.pts_to sd vsd);
      let blk = Sub.sub dst lo hi;
      sample_ntt_impl blk sd 34sz;
      with b1. assert (A.pts_to blk b1);
      Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
      with w1. assert (A.pts_to dst w1);
      gen_prefix_len (SZ.v k) vr tr v0 (SZ.v vc);
      gen_prefix_step (SZ.v k) vr tr (SZ.v vc) v0 w1 b1 vsd;
      c := SZ.add vc 1sz;
    }
  };
  with v. assert (A.pts_to dst v);
  let vc = !c;
  assert (pure (SZ.v vc == SZ.v k * SZ.v k));
  gen_prefix_done (SZ.v k) vr tr v;
  Mem.wipe sd 34sz;
}

(** Algorithm 13 lines 8-11: [k] consecutive PRF calls with a running
    counter. *)
fn noise_vec_impl (dst: A.array zqt) (s: A.array S8.t) (start: U8.t) ([@@@FStar.Attributes.monomorphize] eta: SZ.t) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  (#vd: erased (Seq.seq zqt)) (#p: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to s #p vs **
         pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
               U8.v start + SZ.v k <= 256 /\
               Seq.length vd == SZ.v k * n /\ Seq.length vs == 32)
ensures exists* v. A.pts_to dst v ** A.pts_to s #p vs **
  pure (1 <= SZ.v k /\ SZ.v k <= 4 /\ 1 <= SZ.v eta /\ SZ.v eta <= 3 /\
        U8.v start + SZ.v k <= 256 /\ Seq.length vs == 32 /\
        Seq.length v == SZ.v k * n /\
        as_zqs v == noise_vec (SZ.v k) (SZ.v eta) vs (U8.v start))
{
  A.pts_to_len dst;
  A.pts_to_len s;
  HSZ.fits32 ();
  assert_norm (4 * n < pow2 32);
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi k)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to s #p vs **
    pure (SZ.v vi <= SZ.v k /\ 1 <= SZ.v k /\ SZ.v k <= 4 /\
          1 <= SZ.v eta /\ SZ.v eta <= 3 /\ U8.v start + SZ.v k <= 256 /\
          Seq.length v == SZ.v k * n /\ Seq.length vs == 32 /\
          (forall (t: nat). t < SZ.v vi * n ==>
             S16.v (Seq.index v t) ==
               Seq.index (noise_vec (SZ.v k) (SZ.v eta) vs (U8.v start)) t))
  decreases (SZ.v k - SZ.v (!i))
  {
    let vi = !i;
    Math.lemma_mult_le_right n (SZ.v vi + 1) (SZ.v k);
    SZ.fits_u32_implies_fits (SZ.v vi * n + n);
    SZ.fits_u32_implies_fits (SZ.v vi + 1);
    let lo = SZ.mul vi 256sz;
    let hi = SZ.add lo 256sz;
    let bi = Cast.uint32_to_uint8 (SZ.sizet_to_uint32 vi);
    let byte = U8.add start bi;
    Math.small_mod (SZ.v vi) 256;
    Math.small_mod (SZ.v vi) 4294967296;
    assert (pure (U8.v bi == SZ.v vi));
    assert (pure (U8.v byte == U8.v start + SZ.v vi));
    U8.uv_inv byte;
    assert (pure (byte == U8.uint_to_t (U8.v start + SZ.v vi)));
    with w0. assert (A.pts_to dst w0);
    let blk = Sub.sub dst lo hi;
    sample_poly_cbd_impl blk s byte eta;
    with b1. assert (A.pts_to blk b1);
    Sub.unsub dst (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to dst w1);
    noise_entry_step (SZ.v k) (SZ.v eta) vs (U8.v start) (SZ.v vi) w0 w1 b1;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  noise_entry_done (SZ.v k) (SZ.v eta) vs (U8.v start) v;
  assert (pure (as_zqs v == noise_vec (SZ.v k) (SZ.v eta) vs (U8.v start)));
}

#pop-options
