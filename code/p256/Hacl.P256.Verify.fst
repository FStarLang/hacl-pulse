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
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Spec.Bytes
open Hacl.Impl.Limb4
open Hacl.P256.Field
open Hacl.P256.Scalar
open Hacl.P256.Point
open Hacl.P256.PointMulD
open Hacl.P256.Encode

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module GR = Spec.P256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** As elsewhere, an [ensures] cannot assume the [requires], so the lengths
    travel in a total wrapper. *)
let vfy (m: P.qelem) (vp vr vs: Seq.seq S8.t) : GTot bool =
  if Seq.length vp = 64 && Seq.length vr = 32 && Seq.length vs = 32
  then P.ecdsa_verify_msg_as_qelem m vp vr vs else false

fn verify (mq: A.array S64.t) (pk sig_r sig_s: A.array S8.t)
          (#pm: perm) (#vm: erased (Seq.seq S64.t))
          (#pp: perm) (#vp: erased (Seq.seq S8.t))
          (#pr: perm) (#vr: erased (Seq.seq S8.t))
          (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  A.pts_to mq #pm vm ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (qelem vm /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures
  A.pts_to mq #pm vm ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (res == vfy (qev vm) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 4sz |]; A.pts_to_len c0; let mut c1 = [| z; 4sz |]; A.pts_to_len c1; let mut c2 = [| z; 4sz |]; A.pts_to_len c2; let mut c3 = [| z; 4sz |]; A.pts_to_len c3; let mut c4 = [| z; 4sz |]; A.pts_to_len c4; let mut c5 = [| z; 4sz |]; A.pts_to_len c5; let mut c6 = [| z; 4sz |]; A.pts_to_len c6; let mut c7 = [| z; 4sz |]; A.pts_to_len c7; let mut c8 = [| z; 4sz |]; A.pts_to_len c8; let mut c9 = [| z; 4sz |]; A.pts_to_len c9; let mut ca = [| z; 4sz |]; A.pts_to_len ca; let mut cb = [| z; 4sz |]; A.pts_to_len cb; let mut cc = [| z; 4sz |]; A.pts_to_len cc; let mut cd = [| z; 4sz |]; A.pts_to_len cd; let mut ce = [| z; 4sz |]; A.pts_to_len ce; let mut cf = [| z; 4sz |]; A.pts_to_len cf; A.pts_to_len c0; A.pts_to_len c1; A.pts_to_len c2;
  A.pts_to_len c3; A.pts_to_len c4; A.pts_to_len c5; A.pts_to_len c6;
  A.pts_to_len c7; A.pts_to_len c8; A.pts_to_len c9;
  A.pts_to_len ca; A.pts_to_len cb; A.pts_to_len cc;
  A.pts_to_len cd; A.pts_to_len ce; A.pts_to_len cf;
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 32sz |]; A.pts_to_len d0; A.pts_to_len d0;

  let okr = qload c0 sig_r;
  let oks = qload c1 sig_s;
  let okq = load_point c7 c8 c9 pk;
  if (okr && oks && okq) {
    qinv c2 c1;
    qmul c3 c2 mq;
    qmul c4 c2 c0;
    qfrom c5 c3;
    qfrom c6 c4;
    lpt_on_curve vp;
    with q0 q1 q2. assert (A.pts_to c7 q0 ** A.pts_to c8 q1 ** A.pts_to c9 q2);
    with w5 w6. assert (A.pts_to c5 w5 ** A.pts_to c6 w6);
    point_mul_double_g ca cb cc c5 c6 c7 c8 c9;
    with wx wy wz. assert (A.pts_to ca wx ** A.pts_to cb wy ** A.pts_to cc wz);
    GR.peq_is_point_at_infinity (pt wx wy wz)
      (P.point_mul_double_g (eval (vals w5)) (eval (vals w6)) (pt q0 q1 q2));
    GR.peq_to_aff_point (pt wx wy wz)
      (P.point_mul_double_g (eval (vals w5)) (eval (vals w6)) (pt q0 q1 q2));
    let inf = fis_zero cc;
    if inf {
      false
    } else {
      to_aff_point cd ce ca cb cc;
      with wax. assert (A.pts_to cd wax);
      fstore d0 cd;
      assert_norm (P.prime < pow2 256);
      be_nat_to_be 32 (fev wax);
      qload_mod cf d0;
      let eq = qeq cf c0;
      eq
    }
  } else {
    false
  }
}

#pop-options
