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

(** ECDSA signing.

    The nonce is an input.  HACL* does not implement RFC 6979 deterministic
    nonces and neither does this; a caller who reuses a nonce hands over
    the private key, and no amount of verification prevents that.

    The message arrives already reduced to a scalar.  Doing the hashing
    here would tie the signature to a hash function for no reason; the
    front ends in {!Hacl.K256} do that part. *)
module Hacl.K256.Sign

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum52
open Spec.K256.Field52
open Hacl.Spec.Bytes
open Hacl.Impl.Limb4
open Hacl.Impl.Copy
open Hacl.K256.Field52
open Hacl.K256.Scalar
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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** As elsewhere, an [ensures] cannot assume the [requires], so the lengths
    travel in a total wrapper. *)
let sgn (m: K.qelem) (vsk vn: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vsk = 32 && Seq.length vn = 32
  then K.ecdsa_sign_msg_as_qelem m vsk vn else None

fn sign (out: A.array S8.t) (mq: A.array S64.t) (sk nonce: A.array S8.t)
        (#vo: erased (Seq.seq S8.t))
        (#pm: perm) (#vm: erased (Seq.seq S64.t))
        (#pk: perm) (#vsk: erased (Seq.seq S8.t))
        (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to mq #pm vm **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ qelem vm /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to mq #pm vm **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (sgn (qev vm) vsk vn) /\
        (r ==> wo == Some?.v (sgn (qev vm) vsk vn)))
{
  A.pts_to_len out;
  let z = S64.zero;
  let mut c0 = [| z; 4sz |]; A.pts_to_len c0; let mut c1 = [| z; 4sz |]; A.pts_to_len c1; let mut c2 = [| z; 4sz |]; A.pts_to_len c2; let mut c3 = [| z; 4sz |]; A.pts_to_len c3; let mut c4 = [| z; 4sz |]; A.pts_to_len c4; let mut c5 = [| z; 4sz |]; A.pts_to_len c5; let mut c6 = [| z; 4sz |]; A.pts_to_len c6; let mut c7 = [| z; 4sz |]; A.pts_to_len c7; let mut c8 = [| z; 5sz |]; A.pts_to_len c8; let mut c9 = [| z; 5sz |]; A.pts_to_len c9; let mut ca = [| z; 5sz |]; A.pts_to_len ca; let mut cb = [| z; 5sz |]; A.pts_to_len cb; let mut cc = [| z; 5sz |]; A.pts_to_len cc; A.pts_to_len c0; A.pts_to_len c1; A.pts_to_len c2; A.pts_to_len c3;
  A.pts_to_len c4; A.pts_to_len c5; A.pts_to_len c6; A.pts_to_len c7;
  A.pts_to_len c8; A.pts_to_len c9; A.pts_to_len ca;
  A.pts_to_len cb; A.pts_to_len cc;
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 32sz |]; A.pts_to_len d0; let mut d1 = [| z8; 32sz |]; A.pts_to_len d1; let mut d2 = [| z8; 32sz |]; A.pts_to_len d2; A.pts_to_len d0; A.pts_to_len d1; A.pts_to_len d2;

  let okd = qload c2 sk;
  let okn = qload c1 nonce;
  let okl = load_scalar c0 nonce;
  if (okd && okn) {
    point_mul_g c8 c9 ca c0;
    to_aff_point cb cc c8 c9 ca;
    with wax. assert (A.pts_to cb wax);
    fstore d0 cb;
    assert_norm (K.prime < pow2 256);
    be_nat_to_be 32 (fev (vals wax));
    qload_mod c3 d0;
    qinv c5 c1;
    qmul c6 c3 c2;
    qadd c7 mq c6;
    qmul c4 c5 c7;
    let rz = qis_zero c3;
    let sz = qis_zero c4;
    if (rz || sz) {
      false
    } else {
      qstore d1 c3;
      qstore d2 c4;
      with wrb. assert (A.pts_to d1 wrb);
      with wsb. assert (A.pts_to d2 wsb);
      A.pts_to_len d1; A.pts_to_len d2;
      copy_at out 0sz d1 32sz;
      copy_at out 32sz d2 32sz;
      with wo. assert (A.pts_to out wo);
      A.pts_to_len out;
      assert (pure (Seq.equal wo (Seq.append wrb wsb)));
      true
    }
  } else {
    false
  }
}

#pop-options
