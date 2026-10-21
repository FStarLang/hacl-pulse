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


(** Algorithm 6, [ML-DSA.KeyGen_internal]. *)
module Hacl.Impl.MLDSA.KeyGen

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Encode
open Spec.MLDSA.Sample
open Spec.MLDSA.Rounding
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Vec
open Hacl.Impl.MLDSA.VecRound
open Hacl.Impl.MLDSA.Sampler
open Hacl.Impl.MLDSA.Pack
open Hacl.Impl.MLDSA.Glue

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Cast = FStar.Int.Cast
module Classical = FStar.Classical
module HSZ = Hacl.SizeT
module Sub = Hacl.Impl.Sub
module Copy = Hacl.Impl.Copy
module M = Spec.MLDSA
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let seed_eq (p: params) (xi: Seq.seq S8.t) (v: Seq.seq S8.t)
  : Lemma (requires Seq.length xi == 32 /\ Seq.length v == 34 /\
                    (forall (t: nat). t < 32 ==> Seq.index v t == Seq.index xi t) /\
                    S8.v (Seq.index v 32) == p.k /\ S8.v (Seq.index v 33) == p.l)
          (ensures v == M.keygen_seed p xi)
  = let s = M.keygen_seed p xi in
    let aux (t: nat { t < 34 }) : Lemma (Seq.index v t == Seq.index s t)
      = if t < 32 then ()
        else S8.v_extensional (Seq.index v t) (Seq.index s t)
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro v s

let slice_eq (a b: Seq.seq S8.t) (i j: nat) (m: nat)
  : Lemma (requires i + m <= Seq.length a /\ j + m <= Seq.length b /\
                    (forall (t: nat). t < m ==> Seq.index a (i + t) == Seq.index b (j + t)))
          (ensures Seq.slice a i (i + m) == Seq.slice b j (j + m))
  = Seq.lemma_eq_intro (Seq.slice a i (i + m)) (Seq.slice b j (j + m))

(** The [t] half: [t = NTT^-1(A NTT(s1)) + s2], split into [t1] (returned
    in [t1]) and [t0] (left in [t]). *)
fn keygen_t_impl (p: erased params) (t t1 a s1 s2: A.array zqt)
                 ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                 (#vt #v1: erased (Seq.seq zqt)) (#pa #ps1 #ps2: perm)
                 (#va #vs1 #vs2: erased (Seq.seq zqt))
requires A.pts_to t vt ** A.pts_to t1 v1 ** A.pts_to a #pa va **
         A.pts_to s1 #ps1 vs1 ** A.pts_to s2 #ps2 vs2 **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\
               Seq.length vt == p.k * n /\ Seq.length v1 == p.k * n /\
               Seq.length va == p.k * p.l * n /\
               Seq.length vs1 == p.l * n /\ Seq.length vs2 == p.k * n)
ensures exists* (w0 w1: Seq.seq zqt).
  A.pts_to t w0 ** A.pts_to t1 w1 ** A.pts_to a #pa va **
  A.pts_to s1 #ps1 vs1 ** A.pts_to s2 #ps2 vs2 **
  pure (Seq.length w0 == p.k * n /\ Seq.length w1 == p.k * n /\
        Seq.length va == p.k * p.l * n /\
        Seq.length vs1 == p.l * n /\ Seq.length vs2 == p.k * n /\
        (let tt = M.keygen_t p (as_zqs va) (as_zqs vs1) (as_zqs vs2) in
         as_zqs w0 == vec_power2round_lo tt /\
         as_ints w1 == vec_power2round_hi tt /\
         (forall (i: nat). i < p.k * n ==> S32.v (Seq.index w1 i) < 1024)))
{
  HSZ.fits32 ();
  let ln = SZ.mul l 256sz;
  let kn = SZ.mul k 256sz;
  let mut s1h = [| (S32.zero <: zqt); ln |];
  Mem.track s1h;
  zcopy s1h s1 ln;
  vec_ntt_impl s1h l;
  let mut tmp = [| (S32.zero <: zqt); 256sz |];
  Mem.track tmp;
  mat_vec_mul_impl t a s1h tmp k l;
  vec_intt_impl t k;
  with u. assert (A.pts_to t u);
  add_inplace t s2 kn;
  with u'. assert (A.pts_to t u');
  add_eq p.k u' u vs2;
  power2round_impl t t1 k;
  Mem.wipe tmp 256sz;
  Mem.wipe s1h ln;
  ()
}

fn pk_assemble (p: erased params) (pk h: A.array S8.t) (t1: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                (#vp0: erased (Seq.seq S8.t)) (#ph #pt: perm)
                (#vh: erased (Seq.seq S8.t)) (#vt: erased (Seq.seq zqt))
requires A.pts_to pk vp0 ** A.pts_to h #ph vh ** A.pts_to t1 #pt vt **
         pure (SZ.v k == p.k /\ Seq.length vp0 == pk_len p /\ Seq.length vh == 128 /\
               Seq.length vt == p.k * n)
ensures exists* (vp: Seq.seq S8.t).
  A.pts_to pk vp ** A.pts_to h #ph vh ** A.pts_to t1 #pt vt **
  pure (Seq.length vh == 128 /\ Seq.length vt == p.k * n /\ Seq.length vp == pk_len p /\
        vp == pk_encode p (Seq.slice vh 0 32) (as_ints vt))
{
  A.pts_to_len pk;
  Copy.copy_prefix pk h 32sz;
  with vp1. assert (A.pts_to pk vp1);
  slice_eq vp1 vh 0 0 32;
  pk_encode_impl p pk t1 k;
  ()
}

fn sk_assemble (p: erased params) (sk h tr: A.array S8.t) (s1 s2 t0: A.array zqt)
               ([@@@FStar.Attributes.monomorphize] k: SZ.t)
               ([@@@FStar.Attributes.monomorphize] l: SZ.t)
               ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
               (#vs0: erased (Seq.seq S8.t)) (#ph #ptr #p1 #p2 #p0: perm)
               (#vh #vtr: erased (Seq.seq S8.t)) (#v1 #v2 #v0: erased (Seq.seq zqt))
requires A.pts_to sk vs0 ** A.pts_to h #ph vh ** A.pts_to tr #ptr vtr **
         A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 ** A.pts_to t0 #p0 v0 **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
               Seq.length vs0 == sk_len p /\ Seq.length vh == 128 /\ Seq.length vtr == 64 /\
               Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n)
ensures exists* (vs: Seq.seq S8.t).
  A.pts_to sk vs ** A.pts_to h #ph vh ** A.pts_to tr #ptr vtr **
  A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 ** A.pts_to t0 #p0 v0 **
  pure (Seq.length vh == 128 /\ Seq.length vtr == 64 /\ Seq.length vs == sk_len p /\
        Seq.length v1 == p.l * n /\ Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
        vs == sk_encode p (Seq.slice vh 0 32) (Seq.slice vh 96 128) vtr
                        (as_zqs v1) (as_zqs v2) (as_zqs v0))
{
  A.pts_to_len sk;
  Copy.copy_prefix sk h 32sz;
  Copy.copy_range sk 32sz h 96sz 32sz;
  Copy.copy_at sk 64sz tr 64sz;
  with vk1. assert (A.pts_to sk vk1);
  slice_eq vk1 vh 0 0 32;
  slice_eq vk1 vh 32 96 32;
  slice_eq vk1 vtr 64 0 64;
  assert (pure (Seq.equal (Seq.slice vtr 0 64) vtr));
  sk_encode_impl p sk s1 s2 t0 k l eta;
  ()
}

let keygen_eq (p: params) (vx: Seq.lseq S8.t 32) (vh: Seq.lseq S8.t 128)
              (va vs1 vs2 vt0 vt1: Seq.seq zqt) (vtr: Seq.lseq S8.t 64)
              (vp: Seq.lseq S8.t (pk_len p)) (vs: Seq.lseq S8.t (sk_len p))
  : Lemma (requires
      vh == M.hash (M.keygen_seed p vx) 128 /\
      Seq.length va == p.k * p.l * n /\ Seq.length vs1 == p.l * n /\
      Seq.length vs2 == p.k * n /\ Seq.length vt0 == p.k * n /\ Seq.length vt1 == p.k * n /\
      as_zqs va == expand_a p (Seq.slice vh 0 32) /\
      as_zqs vs1 == expand_s1 p (Seq.slice vh 32 96) /\
      as_zqs vs2 == expand_s2 p (Seq.slice vh 32 96) /\
      (let tt = M.keygen_t p (as_zqs va) (as_zqs vs1) (as_zqs vs2) in
       as_zqs vt0 == vec_power2round_lo tt /\ as_ints vt1 == vec_power2round_hi tt) /\
      vp == pk_encode p (Seq.slice vh 0 32) (as_ints vt1) /\
      vtr == M.hash vp 64 /\
      vs == sk_encode p (Seq.slice vh 0 32) (Seq.slice vh 96 128) vtr
                      (as_zqs vs1) (as_zqs vs2) (as_zqs vt0))
    (ensures vp == fst (M.keygen_internal p vx) /\ vs == snd (M.keygen_internal p vx))
  = ()

fn keygen_impl (pk sk xi: A.array S8.t) (p: erased params)
               ([@@@FStar.Attributes.monomorphize] k: SZ.t)
               ([@@@FStar.Attributes.monomorphize] l: SZ.t)
               ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
               (#vp0 #vs0: erased (Seq.seq S8.t)) (#px: perm) (#vx: erased (Seq.seq S8.t))
requires A.pts_to pk vp0 ** A.pts_to sk vs0 ** A.pts_to xi #px vx **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
               Seq.length vx == 32 /\ Seq.length vp0 == pk_len p /\ Seq.length vs0 == sk_len p)
ensures exists* (vp vs: Seq.seq S8.t).
  A.pts_to pk vp ** A.pts_to sk vs ** A.pts_to xi #px vx **
  pure (Seq.length vx == 32 /\ Seq.length vp == pk_len p /\ Seq.length vs == sk_len p /\
        vp == fst (M.keygen_internal p vx) /\ vs == snd (M.keygen_internal p vx))
{
  A.pts_to_len pk;
  A.pts_to_len sk;
  A.pts_to_len xi;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sk_len p);
  let pkl = SZ.add 32sz (SZ.mul 320sz k);
  let kn = SZ.mul k 256sz;
  let ln = SZ.mul l 256sz;
  let kln = SZ.mul (SZ.mul k l) 256sz;
  (* h = H(xi || k || l, 128) *)
  let mut seed = [| (S8.zero <: S8.t); 34sz |];
  Mem.track seed;
  A.pts_to_len seed;
  Copy.copy_prefix seed xi 32sz;
  A.(seed.(32sz) <- S8.classify (Cast.uint32_to_uint8 (SZ.sizet_to_uint32 k)));
  A.(seed.(33sz) <- S8.classify (Cast.uint32_to_uint8 (SZ.sizet_to_uint32 l)));
  with vsd. assert (A.pts_to seed vsd);
  FStar.Math.Lemmas.small_mod (SZ.v k) 256;
  FStar.Math.Lemmas.small_mod (SZ.v l) 256;
  seed_eq p vx vsd;
  let mut h = [| (S8.zero <: S8.t); 128sz |];
  Mem.track h;
  Hacl.Hash.SHA3.shake256 h 128sz seed 34sz;
  Mem.wipe seed 34sz;
  with vh. assert (A.pts_to h vh);
  (* the matrix and the secret vectors *)
  let a = Mem.alloc (S32.zero <: zqt) kln;
  let rho = Sub.sub h 0sz 32sz;
  expand_a_impl p a rho k l;
  Sub.unsub_id h 0 32 rho;
  with va. assert (A.pts_to a va);
  let mut s1 = [| (S32.zero <: zqt); ln |];
  Mem.track s1;
  let mut s2 = [| (S32.zero <: zqt); kn |];
  Mem.track s2;
  let rho' = Sub.sub h 32sz 96sz;
  expand_s_impl p s1 s2 rho' k l eta;
  Sub.unsub_id h 32 96 rho';
  with vs1. assert (A.pts_to s1 vs1);
  with vs2. assert (A.pts_to s2 vs2);
  (* t *)
  let t = Mem.alloc (S32.zero <: zqt) kn;
  let t1 = Mem.alloc (S32.zero <: zqt) kn;
  keygen_t_impl p t t1 a s1 s2 k l;
  Mem.free a kln;
  with vt0. assert (A.pts_to t vt0);
  with vt1. assert (A.pts_to t1 vt1);
  (* pk *)
  pk_assemble p pk h t1 k;
  Mem.free t1 kn;
  with vp. assert (A.pts_to pk vp);
  (* sk *)
  let mut tr = [| (S8.zero <: S8.t); 64sz |];
  Mem.track tr;
  Hacl.Hash.SHA3.shake256 tr 64sz pk pkl;
  with vtr. assert (A.pts_to tr vtr);
  sk_assemble p sk h tr s1 s2 t k l eta;
  Mem.free t kn;
  Mem.wipe s2 kn;
  Mem.wipe s1 ln;
  Mem.wipe h 128sz;
  Mem.wipe tr 64sz;
  with vs. assert (A.pts_to sk vs);
  keygen_eq p vx vh va vs1 vs2 vt0 vt1 vtr vp vs;
  ()
}

#pop-options
