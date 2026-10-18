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


(** Pieces shared by key generation, signing and verification: a copy,
    the lemmas that turn the elementwise loops of {!Hacl.Impl.MLDSA.Vec}
    into the specification's vector operations, and the challenge hash
    [c~ = H(mu || w1Encode(w1))]. *)
module Hacl.Impl.MLDSA.Glue

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Encode
open Hacl.Impl.MLDSA.Zq

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Classical = FStar.Classical
module HSZ = Hacl.SizeT
module Sub = Hacl.Impl.Sub
module Copy = Hacl.Impl.Copy
module Pack = Hacl.Impl.MLDSA.Pack
module M = Spec.MLDSA

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Vector lemmas} *)

let add_eq (k: pos) (w a b: Seq.seq zqt)
  : Lemma (requires Seq.length w == k * n /\ Seq.length a == k * n /\ Seq.length b == k * n /\
                    (forall (t: nat). t < k * n ==>
                       S32.v (Seq.index w t) == add (S32.v (Seq.index a t)) (S32.v (Seq.index b t))))
          (ensures as_zqs w == vec_add #k (as_zqs a) (as_zqs b))
  = Seq.lemma_eq_intro (as_zqs w) (vec_add #k (as_zqs a) (as_zqs b))

let sub_eq (k: pos) (w a b: Seq.seq zqt)
  : Lemma (requires Seq.length w == k * n /\ Seq.length a == k * n /\ Seq.length b == k * n /\
                    (forall (t: nat). t < k * n ==>
                       S32.v (Seq.index w t) == sub (S32.v (Seq.index a t)) (S32.v (Seq.index b t))))
          (ensures as_zqs w == vec_sub #k (as_zqs a) (as_zqs b))
  = Seq.lemma_eq_intro (as_zqs w) (vec_sub #k (as_zqs a) (as_zqs b))

let t1_shift_eq (k: pos) (w v: Seq.seq zqt) (t1: Seq.lseq nat (k * n))
  : Lemma (requires Seq.length w == k * n /\ Seq.length v == k * n /\ as_ints v == t1 /\
                    (forall (i: nat). i < k * n ==> S32.v (Seq.index v i) < 1024) /\
                    (forall (i: nat). i < k * n ==>
                       S32.v (Seq.index w i) == S32.v (Seq.index v i) * pow2 d))
          (ensures as_zqs w == M.t1_shift #k t1)
  = assert_norm (pow2 d == 8192);
    let aux (i: nat { i < k * n })
      : Lemma (Seq.index (as_zqs w) i == Seq.index (M.t1_shift #k t1) i)
      = as_ints_index v i;
        FStar.Math.Lemmas.small_mod (S32.v (Seq.index w i)) q
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (as_zqs w) (M.t1_shift #k t1)

(** {2 Copies} *)

fn zcopy (dst src: A.array zqt) (len: SZ.t)
         (#vd: erased (Seq.seq zqt)) (#ps: perm) (#vs: erased (Seq.seq zqt))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
         pure (Seq.length vd == SZ.v len /\ Seq.length vs == SZ.v len)
ensures A.pts_to dst vs ** A.pts_to src #ps vs
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq zqt).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #ps vs **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\ Seq.length vs == SZ.v len /\
          (forall (t: nat). t < SZ.v vi ==> Seq.index v t == Seq.index vs t))
  decreases (SZ.v len - SZ.v (!i))
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

(** {2 The challenge hash} *)

let challenge_glue (p: params) (vb vm vw: Seq.seq S8.t)
  : Lemma (requires Seq.length vm == 64 /\ Seq.length vb == 64 + Seq.length vw /\
                    (forall (t: nat). t < 64 ==> Seq.index vb t == Seq.index vm t) /\
                    Seq.slice vb 64 (Seq.length vb) == vw)
          (ensures vb == Seq.append vm vw)
  = Seq.lemma_eq_intro vb (Seq.append vm vw)

(** [ct <- H(mu || w1Encode(w1), ct_len)]. *)
fn challenge_impl (p: erased params) (ct: A.array S8.t) (mu: A.array S8.t) (w1: A.array zqt)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                  (gd: U32.t)
                  (#vc: erased (Seq.seq S8.t)) (#pm #pw: perm)
                  (#vm: erased (Seq.seq S8.t)) (#vw: erased (Seq.seq zqt))
requires A.pts_to ct vc ** A.pts_to mu #pm vm ** A.pts_to w1 #pw vw **
         pure (SZ.v k == p.k /\ SZ.v ctl == ct_len p /\ U32.v gd == p.gamma2_div /\
               Seq.length vc == ct_len p /\ Seq.length vm == 64 /\ Seq.length vw == p.k * n)
ensures exists* (v: Seq.seq S8.t). A.pts_to ct v ** A.pts_to mu #pm vm ** A.pts_to w1 #pw vw **
  pure (Seq.length vm == 64 /\ Seq.length vw == p.k * n /\
        v == M.challenge_hash p vm (as_ints vw))
{
  A.pts_to_len ct;
  HSZ.fits32 ();
  let wb = (if gd = 88ul then 6sz else 4sz);
  let el = SZ.mul k (SZ.mul 32sz wb);
  let bl = SZ.add 64sz el;
  let mut buf = [| (S8.zero <: S8.t); bl |];
  A.pts_to_len buf;
  Copy.copy_prefix buf mu 64sz;
  let wbuf = Sub.sub buf 64sz bl;
  Pack.w1_encode_impl p wbuf w1 k gd;
  with ve. assert (A.pts_to wbuf ve);
  Sub.unsub buf 64 (SZ.v bl) wbuf;
  with vb. assert (A.pts_to buf vb);
  assert (pure (Seq.equal (Seq.slice vb 64 (SZ.v bl)) ve));
  challenge_glue p vb vm ve;
  Hacl.Hash.SHA3.shake256 ct ctl buf bl;
  ()
}

#pop-options
