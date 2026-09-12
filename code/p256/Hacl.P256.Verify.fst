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

(** ECDSA verification.

    Nothing here is secret -- the message, the signature and the public key
    are all published -- but the code is the same constant-time code
    anyway, because the alternative is a second implementation of every
    field operation. *)
module Hacl.P256.Verify

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Spec.Bytes
open Hacl.Impl.Limb
open Hacl.P256.Field
open Hacl.P256.Scalar
open Hacl.P256.Point
open Hacl.P256.PointMulD
open Hacl.P256.Encode

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** As elsewhere, an [ensures] cannot assume the [requires], so the lengths
    travel in a total wrapper. *)
let vfy (m: P.qelem) (vp vr vs: Seq.seq S8.t) : GTot bool =
  if Seq.length vp = 64 && Seq.length vr = 32 && Seq.length vs = 32
  then P.ecdsa_verify_msg_as_qelem m vp vr vs else false

fn verify (mq: S.slice S64.t) (pk sig_r sig_s: S.slice S8.t)
          (#pm: perm) (#vm: erased (Seq.seq S64.t))
          (#pp: perm) (#vp: erased (Seq.seq S8.t))
          (#pr: perm) (#vr: erased (Seq.seq S8.t))
          (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  S.pts_to mq #pm vm ** S.pts_to pk #pp vp **
  S.pts_to sig_r #pr vr ** S.pts_to sig_s #ps vs **
  pure (qelem vm /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures
  S.pts_to mq #pm vm ** S.pts_to pk #pp vp **
  S.pts_to sig_r #pr vr ** S.pts_to sig_s #ps vs **
  pure (res == vfy (qev vm) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; let rq = S.from_array c0 16sz;
  let mut c1 = [| z; 16sz |]; A.pts_to_len c1; let sq = S.from_array c1 16sz;
  let mut c2 = [| z; 16sz |]; A.pts_to_len c2; let t0 = S.from_array c2 16sz;
  let mut c3 = [| z; 16sz |]; A.pts_to_len c3; let u1 = S.from_array c3 16sz;
  let mut c4 = [| z; 16sz |]; A.pts_to_len c4; let u2 = S.from_array c4 16sz;
  let mut c5 = [| z; 16sz |]; A.pts_to_len c5; let l1 = S.from_array c5 16sz;
  let mut c6 = [| z; 16sz |]; A.pts_to_len c6; let l2 = S.from_array c6 16sz;
  let mut c7 = [| z; 16sz |]; A.pts_to_len c7; let qx = S.from_array c7 16sz;
  let mut c8 = [| z; 16sz |]; A.pts_to_len c8; let qy = S.from_array c8 16sz;
  let mut c9 = [| z; 16sz |]; A.pts_to_len c9; let qz = S.from_array c9 16sz;
  let mut ca = [| z; 16sz |]; A.pts_to_len ca; let rx = S.from_array ca 16sz;
  let mut cb = [| z; 16sz |]; A.pts_to_len cb; let ry = S.from_array cb 16sz;
  let mut cc = [| z; 16sz |]; A.pts_to_len cc; let rz = S.from_array cc 16sz;
  let mut cd = [| z; 16sz |]; A.pts_to_len cd; let ax = S.from_array cd 16sz;
  let mut ce = [| z; 16sz |]; A.pts_to_len ce; let ay = S.from_array ce 16sz;
  let mut cf = [| z; 16sz |]; A.pts_to_len cf; let cq = S.from_array cf 16sz;
  S.pts_to_len rq; S.pts_to_len sq; S.pts_to_len t0;
  S.pts_to_len u1; S.pts_to_len u2; S.pts_to_len l1; S.pts_to_len l2;
  S.pts_to_len qx; S.pts_to_len qy; S.pts_to_len qz;
  S.pts_to_len rx; S.pts_to_len ry; S.pts_to_len rz;
  S.pts_to_len ax; S.pts_to_len ay; S.pts_to_len cq;
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 32sz |]; A.pts_to_len d0; let xb = S.from_array d0 32sz;
  S.pts_to_len xb;

  let okr = qload rq sig_r;
  let oks = qload sq sig_s;
  let okq = load_point qx qy qz pk;
  if (okr && oks && okq) {
    qinv t0 sq;
    qmul u1 t0 mq;
    qmul u2 t0 rq;
    qfrom l1 u1;
    qfrom l2 u2;
    point_mul_double_g rx ry rz l1 l2 qx qy qz;
    let inf = fis_zero rz;
    if inf {
      S.to_array rq; S.to_array sq; S.to_array t0;
      S.to_array u1; S.to_array u2; S.to_array l1; S.to_array l2;
      S.to_array qx; S.to_array qy; S.to_array qz;
      S.to_array rx; S.to_array ry; S.to_array rz;
      S.to_array ax; S.to_array ay; S.to_array cq; S.to_array xb;
      false
    } else {
      to_aff_point ax ay rx ry rz;
      with wax. assert (S.pts_to ax wax);
      fstore xb ax;
      assert_norm (P.prime < pow2 256);
      be_nat_to_be 32 (fev wax);
      qload_mod cq xb;
      let eq = qeq cq rq;
      S.to_array rq; S.to_array sq; S.to_array t0;
      S.to_array u1; S.to_array u2; S.to_array l1; S.to_array l2;
      S.to_array qx; S.to_array qy; S.to_array qz;
      S.to_array rx; S.to_array ry; S.to_array rz;
      S.to_array ax; S.to_array ay; S.to_array cq; S.to_array xb;
      eq
    }
  } else {
    S.to_array rq; S.to_array sq; S.to_array t0;
    S.to_array u1; S.to_array u2; S.to_array l1; S.to_array l2;
    S.to_array qx; S.to_array qy; S.to_array qz;
    S.to_array rx; S.to_array ry; S.to_array rz;
    S.to_array ax; S.to_array ay; S.to_array cq; S.to_array xb;
    false
  }
}

#pop-options
