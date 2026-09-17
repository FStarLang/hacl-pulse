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
module Hacl.K256.Ecdh

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.K256.Field
open Hacl.Spec.Bytes
open Hacl.K256.Field
open Hacl.K256.Point
open Hacl.K256.PointMul
open Hacl.K256.Encode
open Hacl.K256.Key

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module K = Spec.K256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** As elsewhere, an [ensures] is elaborated with no [requires] in scope,
    so the lengths of the inputs travel in total wrappers. *)
let dhi (vs: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vs = 32 then K.dh_initiator vs else None

let dhr (vp vs: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vp = 64 && Seq.length vs = 32 then K.dh_responder vp vs else None

fn dh_initiator (out sk: A.array S8.t)
                (#vo: erased (Seq.seq S8.t))
                (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to sk #ps vs **
  pure (Seq.length vo == 64 /\ Seq.length vs == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to sk #ps vs **
  pure (Seq.length wo == 64 /\ r == Some? (dhi vs) /\
        (r ==> wo == Some?.v (dhi vs)))
{
  A.pts_to_len out;
  let z = S64.zero;
  let mut a0 = [| z; 8sz |]; A.pts_to_len a0; let mut a1 = [| z; 8sz |]; A.pts_to_len a1; let mut a2 = [| z; 8sz |]; A.pts_to_len a2; let mut a3 = [| z; 8sz |]; A.pts_to_len a3; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;

  let ok = load_scalar a0 sk;
  if ok {
    point_mul_g a1 a2 a3 a0;
    store_point out a1 a2 a3;
    true
  } else {
    false
  }
}

fn dh_responder (out pk sk: A.array S8.t)
                (#vo: erased (Seq.seq S8.t))
                (#pp: perm) (#vp: erased (Seq.seq S8.t))
                (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to out vo ** A.pts_to pk #pp vp ** A.pts_to sk #ps vs **
  pure (Seq.length vo == 64 /\ Seq.length vp == 64 /\ Seq.length vs == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to pk #pp vp ** A.pts_to sk #ps vs **
  pure (Seq.length wo == 64 /\ r == Some? (dhr vp vs) /\
        (r ==> wo == Some?.v (dhr vp vs)))
{
  A.pts_to_len out;
  let z = S64.zero;
  let mut a0 = [| z; 8sz |]; A.pts_to_len a0; let mut a1 = [| z; 8sz |]; A.pts_to_len a1; let mut a2 = [| z; 8sz |]; A.pts_to_len a2; let mut a3 = [| z; 8sz |]; A.pts_to_len a3; let mut a4 = [| z; 8sz |]; A.pts_to_len a4; let mut a5 = [| z; 8sz |]; A.pts_to_len a5; let mut a6 = [| z; 8sz |]; A.pts_to_len a6; A.pts_to_len a0; A.pts_to_len a1; A.pts_to_len a2; A.pts_to_len a3;
  A.pts_to_len a4; A.pts_to_len a5; A.pts_to_len a6;

  let okq = load_point a1 a2 a3 pk;
  let okk = load_scalar a0 sk;
  if (okq && okk) {
    point_mul a4 a5 a6 a1 a2 a3 a0;
    let inf = fis_zero a6;
    if inf {
      false
    } else {
      store_point out a4 a5 a6;
      true
    }
  } else {
    false
  }
}

#pop-options
