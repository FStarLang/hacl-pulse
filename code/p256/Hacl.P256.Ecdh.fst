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

(** ECDH.

    The shared secret is the whole point, [x || y], and not just the
    x-coordinate.  That is HACL*'s API; changing it would silently break
    every caller, so it stands.

    The responder rejects an infinite result.  With a valid public key and
    a scalar below the order that cannot happen -- the group has prime
    order -- but the check costs one comparison and removes the argument. *)
module Hacl.P256.Ecdh

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Spec.Bytes
open Hacl.P256.Field
open Hacl.P256.Point
open Hacl.P256.PointMul
open Hacl.P256.Encode
open Hacl.P256.Key

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** As elsewhere, an [ensures] is elaborated with no [requires] in scope,
    so the lengths of the inputs travel in total wrappers. *)
let dhi (vs: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vs = 32 then P.dh_initiator vs else None

let dhr (vp vs: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vp = 64 && Seq.length vs = 32 then P.dh_responder vp vs else None

fn dh_initiator (out sk: S.slice S8.t)
                (#vo: erased (Seq.seq S8.t))
                (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires S.pts_to out vo ** S.pts_to sk #ps vs **
  pure (Seq.length vo == 64 /\ Seq.length vs == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  S.pts_to out wo ** S.pts_to sk #ps vs **
  pure (Seq.length wo == 64 /\ r == Some? (dhi vs) /\
        (r ==> wo == Some?.v (dhi vs)))
{
  S.pts_to_len out;
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; let k = S.from_array a0 16sz;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let px = S.from_array a1 16sz;
  let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let py = S.from_array a2 16sz;
  let mut a3 = [| z; 16sz |]; A.pts_to_len a3; let pz = S.from_array a3 16sz;
  S.pts_to_len k; S.pts_to_len px; S.pts_to_len py; S.pts_to_len pz;

  let ok = load_scalar k sk;
  if ok {
    point_mul_g px py pz k;
    store_point out px py pz;
    S.to_array k; S.to_array px; S.to_array py; S.to_array pz;
    true
  } else {
    S.to_array k; S.to_array px; S.to_array py; S.to_array pz;
    false
  }
}

fn dh_responder (out pk sk: S.slice S8.t)
                (#vo: erased (Seq.seq S8.t))
                (#pp: perm) (#vp: erased (Seq.seq S8.t))
                (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires S.pts_to out vo ** S.pts_to pk #pp vp ** S.pts_to sk #ps vs **
  pure (Seq.length vo == 64 /\ Seq.length vp == 64 /\ Seq.length vs == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  S.pts_to out wo ** S.pts_to pk #pp vp ** S.pts_to sk #ps vs **
  pure (Seq.length wo == 64 /\ r == Some? (dhr vp vs) /\
        (r ==> wo == Some?.v (dhr vp vs)))
{
  S.pts_to_len out;
  let z = S64.zero;
  let mut a0 = [| z; 16sz |]; A.pts_to_len a0; let k = S.from_array a0 16sz;
  let mut a1 = [| z; 16sz |]; A.pts_to_len a1; let qx = S.from_array a1 16sz;
  let mut a2 = [| z; 16sz |]; A.pts_to_len a2; let qy = S.from_array a2 16sz;
  let mut a3 = [| z; 16sz |]; A.pts_to_len a3; let qz = S.from_array a3 16sz;
  let mut a4 = [| z; 16sz |]; A.pts_to_len a4; let rx = S.from_array a4 16sz;
  let mut a5 = [| z; 16sz |]; A.pts_to_len a5; let ry = S.from_array a5 16sz;
  let mut a6 = [| z; 16sz |]; A.pts_to_len a6; let rz = S.from_array a6 16sz;
  S.pts_to_len k; S.pts_to_len qx; S.pts_to_len qy; S.pts_to_len qz;
  S.pts_to_len rx; S.pts_to_len ry; S.pts_to_len rz;

  let okq = load_point qx qy qz pk;
  let okk = load_scalar k sk;
  if (okq && okk) {
    point_mul rx ry rz qx qy qz k;
    let inf = fis_zero rz;
    if inf {
      S.to_array k; S.to_array qx; S.to_array qy; S.to_array qz;
      S.to_array rx; S.to_array ry; S.to_array rz;
      false
    } else {
      store_point out rx ry rz;
      S.to_array k; S.to_array qx; S.to_array qy; S.to_array qz;
      S.to_array rx; S.to_array ry; S.to_array rz;
      true
    }
  } else {
    S.to_array k; S.to_array qx; S.to_array qy; S.to_array qz;
    S.to_array rx; S.to_array ry; S.to_array rz;
    false
  }
}

#pop-options
