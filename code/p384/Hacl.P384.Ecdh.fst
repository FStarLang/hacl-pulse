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

(** ECDH on P-384.

    As for P-256, the shared secret is the whole point [x || y], and
    [dh_initiator] -- the private key times the generator -- doubles as
    key generation: it is how a public key is derived from a private one.

    The responder rejects an infinite result.  With a valid public key and
    a scalar below the order that cannot happen, since the group has prime
    order, but the check is one comparison and removes the argument. *)
module Hacl.P384.Ecdh

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Spec.Bytes
open Hacl.Impl.Limb64
open Hacl.Bignum.Base
open Hacl.P384.Field
open Hacl.P384.PointMul
open Hacl.P384.Verify
open Hacl.P384.Encode
open Hacl.P384.Key

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module Mem = Hacl.Mem

let dhi (vs: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 96)) =
  if Seq.length vs = 48 then P.dh_initiator vs else None

let dhr (vp vs: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 96)) =
  if Seq.length vp = 96 && Seq.length vs = 48 then P.dh_responder vp vs else None

#push-options "--fuel 0 --ifuel 1 --z3rlimit 200"

fn dh_initiator (out sk: A.array S8.t)
                (#vo: erased (Seq.seq S8.t))
                (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to sk #ps vs **
  pure (Seq.length vo == 96 /\ Seq.length vs == 48)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to sk #ps vs **
  pure (Seq.length wo == 96 /\ r == Some? (dhi vs) /\
        (r ==> wo == Some?.v (dhi vs)))
{
  A.pts_to_len out;
  let z = S64.zero;
  let mut k = [| z; 6sz |];
  Mem.track k; A.pts_to_len k; let mut px = [| z; 6sz |];
  Mem.track px; A.pts_to_len px; let mut py = [| z; 6sz |];
  Mem.track py; A.pts_to_len py; let mut pz = [| z; 6sz |];
  Mem.track pz; A.pts_to_len pz;
  let ok = load_scalar k sk;
  if ok {
    point_mul_g px py pz k;
    with wx wy wz. assert (A.pts_to px wx ** A.pts_to py wy ** A.pts_to pz wz);
    with vk. assert (A.pts_to k vk);
    peq_out (pt wx wy wz) (P.point_mul_g (num vk));
    store_point out px py pz;
    Mem.wipe pz 6sz;
    Mem.wipe py 6sz;
    Mem.wipe px 6sz;
    Mem.wipe k 6sz;
    true
  } else {
    Mem.wipe pz 6sz;
    Mem.wipe py 6sz;
    Mem.wipe px 6sz;
    Mem.wipe k 6sz;
    false
  }
}

fn dh_responder (out pk sk: A.array S8.t)
                (#vo: erased (Seq.seq S8.t))
                (#pp: perm) (#vp: erased (Seq.seq S8.t))
                (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to pk #pp vp ** A.pts_to sk #ps vs **
  pure (Seq.length vo == 96 /\ Seq.length vp == 96 /\ Seq.length vs == 48)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to pk #pp vp ** A.pts_to sk #ps vs **
  pure (Seq.length wo == 96 /\ r == Some? (dhr vp vs) /\
        (r ==> wo == Some?.v (dhr vp vs)))
{
  A.pts_to_len out;
  let z = S64.zero;
  let mut k = [| z; 6sz |];
  Mem.track k; A.pts_to_len k; let mut qx = [| z; 6sz |];
  Mem.track qx; A.pts_to_len qx; let mut qy = [| z; 6sz |];
  Mem.track qy; A.pts_to_len qy; let mut qz = [| z; 6sz |];
  Mem.track qz; A.pts_to_len qz; let mut px = [| z; 6sz |];
  Mem.track px; A.pts_to_len px; let mut py = [| z; 6sz |];
  Mem.track py; A.pts_to_len py; let mut pz = [| z; 6sz |];
  Mem.track pz; A.pts_to_len pz;
  let okq = load_point qx qy qz pk;
  let okk = load_scalar k sk;
  if (okq && okk) {
    lp_on_curve vp;
    point_mul px py pz qx qy qz k;
    with wx wy wz. assert (A.pts_to px wx ** A.pts_to py wy ** A.pts_to pz wz);
    with vk. assert (A.pts_to k vk);
    with q0 q1 q2. assert (A.pts_to qx q0 ** A.pts_to qy q1 ** A.pts_to qz q2);
    peq_out (pt wx wy wz) (P.point_mul (num vk) (pt q0 q1 q2));
    let inf = fis_zero pz;
    if inf {
      Mem.wipe pz 6sz;
      Mem.wipe py 6sz;
      Mem.wipe px 6sz;
      Mem.wipe qz 6sz;
      Mem.wipe qy 6sz;
      Mem.wipe qx 6sz;
      Mem.wipe k 6sz;
      false
    } else {
      store_point out px py pz;
      Mem.wipe pz 6sz;
      Mem.wipe py 6sz;
      Mem.wipe px 6sz;
      Mem.wipe qz 6sz;
      Mem.wipe qy 6sz;
      Mem.wipe qx 6sz;
      Mem.wipe k 6sz;
      true
    }
  } else {
    Mem.wipe pz 6sz;
    Mem.wipe py 6sz;
    Mem.wipe px 6sz;
    Mem.wipe qz 6sz;
    Mem.wipe qy 6sz;
    Mem.wipe qx 6sz;
    Mem.wipe k 6sz;
    false
  }
}

#pop-options
