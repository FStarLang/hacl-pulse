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

(** HMAC_DRBG: the state transition, generic in the hash.

    The state travels as three caller-owned pointers -- [k], [v] and a
    one-element counter -- rather than as a heap-allocated struct, which is
    the convention the streaming hashes already use.  So there is no
    [create_in] and no [free] anywhere in this library. *)
module Hacl.HMAC.DRBG.Core

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HMAC
open Spec.HMAC_DRBG
open Hacl.Impl.Copy
open Hacl.HMAC.Core
open Hacl.HMAC.Cat

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

(** {2 One re-keying}

    [K := HMAC(K, V || c || d1 || d2 || d3)] then [V := HMAC(K, V)].  Both outputs go
    to scratch first: the new [K] is keyed by the old one and the new [V] is
    the old one hashed, so writing in place would alias. *)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

fn rekey (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
         (kt: A.array t) (ivt: A.array t)
         (k: A.array S8.t) (v: A.array S8.t)
         (d1: A.array S8.t) (n1: SZ.t) (d2: A.array S8.t) (n2: SZ.t)
         (d3: A.array S8.t) (n3: SZ.t) (c: U8.t)
         (#pk: perm) (#vk: erased (Seq.seq t))
         (#pi: perm) (#vi: erased (Seq.seq t))
         (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
         (#p1: perm) (#vd1: erased (Seq.seq S8.t))
         (#p2: perm) (#vd2: erased (Seq.seq S8.t))
         (#p3: perm) (#vd3: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to k vkey ** A.pts_to v vval ** A.pts_to d1 #p1 vd1 ** A.pts_to d2 #p2 vd2 ** A.pts_to d3 #p3 vd3 **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vval == (hash_bytes p) /\
               data_ok p (dcat vd1 vd2 vd3) /\
               SZ.fits (block_len #t + (hash_bytes p) + 1 + Seq.length (dcat vd1 vd2 vd3)))
         ** pure (SZ.v n1 == Seq.length vd1)
         ** pure (SZ.v n2 == Seq.length vd2)
         ** pure (SZ.v n3 == Seq.length vd3)
ensures exists* vkey' vval'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to d1 #p1 vd1 ** A.pts_to d2 #p2 vd2 ** A.pts_to d3 #p3 vd3 **
  pure (vkey' == hm p vkey (tagged vval c (dcat vd1 vd2 vd3)) /\ vval' == hm p vkey' vval)
{
  A.pts_to_len kt; A.pts_to_len ivt;
  A.pts_to_len k; A.pts_to_len v;
  A.pts_to_len d1; A.pts_to_len d2; A.pts_to_len d3;
  let hb = p.nhash_bytes;
  let z8 = S8.classify 0uy;
  outer_fits #t p;
  sizes #t p;

  (** [tarr <- V || c] *)
  let tn = SZ.add hb 1sz;
  let mut tarr = [| z8; tn |]; A.pts_to_len tarr;
  A.pts_to_len tarr;
  copy_prefix tarr v hb;
  A.((tarr.(hb) <- S8.classify c));
  with vtmp. assert (A.pts_to tarr vtmp);
  tagged_prefix (reveal vval) c (reveal vtmp);
  tagged_split (reveal vval) c (dcat vd1 vd2 vd3);

  let mut k1arr = [| z8; hb |]; A.pts_to_len k1arr;
  A.pts_to_len k1arr;
  hmac_cat p kt ivt k1arr k tarr d1 d2 d3 hb tn n1 n2 n3;
  with vk1. assert (A.pts_to k1arr vk1);
  hm_def p (reveal vkey) (tagged (reveal vval) c (dcat vd1 vd2 vd3));

  let mut v1arr = [| z8; hb |]; A.pts_to_len v1arr;
  A.pts_to_len v1arr;
  hmac_impl p kt ivt v1arr k1arr hb v hb;
  hm_def p (reveal vk1) (reveal vval);

  copy_exact k k1arr hb;
  copy_exact v v1arr hb;

  ()
}

#pop-options

(** {2 The update function, 10.1.2.2}

    One re-keying, and a second with the tag [0x01] when there is data. *)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

fn update (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
          (kt: A.array t) (ivt: A.array t)
          (k: A.array S8.t) (v: A.array S8.t)
          (d1: A.array S8.t) (n1: SZ.t) (d2: A.array S8.t) (n2: SZ.t) (d3: A.array S8.t) (n3: SZ.t)
          (#pk: perm) (#vk: erased (Seq.seq t))
          (#pi: perm) (#vi: erased (Seq.seq t))
          (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
          (#p1: perm) (#vd1: erased (Seq.seq S8.t))
         (#p2: perm) (#vd2: erased (Seq.seq S8.t))
         (#p3: perm) (#vd3: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to k vkey ** A.pts_to v vval ** A.pts_to d1 #p1 vd1 ** A.pts_to d2 #p2 vd2 ** A.pts_to d3 #p3 vd3 **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vval == (hash_bytes p) /\
               data_ok p (dcat vd1 vd2 vd3) /\
               SZ.fits (block_len #t + (hash_bytes p) + 1 + Seq.length (dcat vd1 vd2 vd3)))
         ** pure (SZ.v n1 == Seq.length vd1)
         ** pure (SZ.v n2 == Seq.length vd2)
         ** pure (SZ.v n3 == Seq.length vd3)
ensures exists* vkey' vval'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to d1 #p1 vd1 ** A.pts_to d2 #p2 vd2 ** A.pts_to d3 #p3 vd3 **
  pure ((vkey', vval') == upd p vkey vval (dcat vd1 vd2 vd3))
{
  A.pts_to_len k; A.pts_to_len v;
  A.pts_to_len d1; A.pts_to_len d2; A.pts_to_len d3;
  outer_fits #t p;
  rekey p kt ivt k v d1 n1 d2 n2 d3 n3 0x00uy;
  hm_def p (reveal vkey) (tagged (reveal vval) 0x00uy (dcat vd1 vd2 vd3));
  with vk1. assert (A.pts_to k vk1);
  with vv1. assert (A.pts_to v vv1);
  hm_def p (reveal vk1) (reveal vval);
  if (SZ.gt n1 0sz || SZ.gt n2 0sz || SZ.gt n3 0sz) {
    rekey p kt ivt k v d1 n1 d2 n2 d3 n3 0x01uy;
    hm_def p (reveal vk1) (tagged (reveal vv1) 0x01uy (dcat vd1 vd2 vd3));
    with vk2. assert (A.pts_to k vk2);
    hm_def p (reveal vk2) (reveal vv1);
    ()
  } else {
    ()
  }
}

#pop-options
