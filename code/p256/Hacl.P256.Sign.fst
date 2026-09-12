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
    front ends in {!Hacl.P256} do that part. *)
module Hacl.P256.Sign

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Spec.P256.Field
open Hacl.Spec.Bytes
open Hacl.Impl.Limb
open Hacl.Impl.Copy
open Hacl.P256.Field
open Hacl.P256.Scalar
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

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** As elsewhere, an [ensures] cannot assume the [requires], so the lengths
    travel in a total wrapper. *)
let sgn (m: P.qelem) (vsk vn: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vsk = 32 && Seq.length vn = 32
  then P.ecdsa_sign_msg_as_qelem m vsk vn else None

fn sign (out: S.slice S8.t) (mq: S.slice S64.t) (sk nonce: S.slice S8.t)
        (#vo: erased (Seq.seq S8.t))
        (#pm: perm) (#vm: erased (Seq.seq S64.t))
        (#pk: perm) (#vsk: erased (Seq.seq S8.t))
        (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  S.pts_to out vo ** S.pts_to mq #pm vm **
  S.pts_to sk #pk vsk ** S.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ qelem vm /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  S.pts_to out wo ** S.pts_to mq #pm vm **
  S.pts_to sk #pk vsk ** S.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (sgn (qev vm) vsk vn) /\
        (r ==> wo == Some?.v (sgn (qev vm) vsk vn)))
{
  S.pts_to_len out;
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; let kl = S.from_array c0 16sz;
  let mut c1 = [| z; 16sz |]; A.pts_to_len c1; let kq = S.from_array c1 16sz;
  let mut c2 = [| z; 16sz |]; A.pts_to_len c2; let dq = S.from_array c2 16sz;
  let mut c3 = [| z; 16sz |]; A.pts_to_len c3; let rq = S.from_array c3 16sz;
  let mut c4 = [| z; 16sz |]; A.pts_to_len c4; let sq = S.from_array c4 16sz;
  let mut c5 = [| z; 16sz |]; A.pts_to_len c5; let t0 = S.from_array c5 16sz;
  let mut c6 = [| z; 16sz |]; A.pts_to_len c6; let t1 = S.from_array c6 16sz;
  let mut c7 = [| z; 16sz |]; A.pts_to_len c7; let t2 = S.from_array c7 16sz;
  let mut c8 = [| z; 16sz |]; A.pts_to_len c8; let px = S.from_array c8 16sz;
  let mut c9 = [| z; 16sz |]; A.pts_to_len c9; let py = S.from_array c9 16sz;
  let mut ca = [| z; 16sz |]; A.pts_to_len ca; let pz = S.from_array ca 16sz;
  let mut cb = [| z; 16sz |]; A.pts_to_len cb; let ax = S.from_array cb 16sz;
  let mut cc = [| z; 16sz |]; A.pts_to_len cc; let ay = S.from_array cc 16sz;
  S.pts_to_len kl; S.pts_to_len kq; S.pts_to_len dq; S.pts_to_len rq;
  S.pts_to_len sq; S.pts_to_len t0; S.pts_to_len t1; S.pts_to_len t2;
  S.pts_to_len px; S.pts_to_len py; S.pts_to_len pz;
  S.pts_to_len ax; S.pts_to_len ay;
  let z8 = S8.classify 0uy;
  let mut d0 = [| z8; 32sz |]; A.pts_to_len d0; let xb = S.from_array d0 32sz;
  let mut d1 = [| z8; 32sz |]; A.pts_to_len d1; let rb = S.from_array d1 32sz;
  let mut d2 = [| z8; 32sz |]; A.pts_to_len d2; let sb = S.from_array d2 32sz;
  S.pts_to_len xb; S.pts_to_len rb; S.pts_to_len sb;

  let okd = qload dq sk;
  let okn = qload kq nonce;
  let okl = load_scalar kl nonce;
  if (okd && okn) {
    point_mul_g px py pz kl;
    to_aff_point ax ay px py pz;
    with wax. assert (S.pts_to ax wax);
    fstore xb ax;
    assert_norm (P.prime < pow2 256);
    be_nat_to_be 32 (fev wax);
    qload_mod rq xb;
    qinv t0 kq;
    qmul t1 rq dq;
    qadd t2 mq t1;
    qmul sq t0 t2;
    let rz = qis_zero rq;
    let sz = qis_zero sq;
    if (rz || sz) {
      S.to_array kl; S.to_array kq; S.to_array dq; S.to_array rq;
      S.to_array sq; S.to_array t0; S.to_array t1; S.to_array t2;
      S.to_array px; S.to_array py; S.to_array pz;
      S.to_array ax; S.to_array ay;
      S.to_array xb; S.to_array rb; S.to_array sb;
      false
    } else {
      qstore rb rq;
      qstore sb sq;
      with wrb. assert (S.pts_to rb wrb);
      with wsb. assert (S.pts_to sb wsb);
      S.pts_to_len rb; S.pts_to_len sb;
      copy_at out 0sz rb 32sz;
      copy_at out 32sz sb 32sz;
      with wo. assert (S.pts_to out wo);
      S.pts_to_len out;
      assert (pure (Seq.equal wo (Seq.append wrb wsb)));
      S.to_array kl; S.to_array kq; S.to_array dq; S.to_array rq;
      S.to_array sq; S.to_array t0; S.to_array t1; S.to_array t2;
      S.to_array px; S.to_array py; S.to_array pz;
      S.to_array ax; S.to_array ay;
      S.to_array xb; S.to_array rb; S.to_array sb;
      true
    }
  } else {
    S.to_array kl; S.to_array kq; S.to_array dq; S.to_array rq;
    S.to_array sq; S.to_array t0; S.to_array t1; S.to_array t2;
    S.to_array px; S.to_array py; S.to_array pz;
    S.to_array ax; S.to_array ay;
    S.to_array xb; S.to_array rb; S.to_array sb;
    false
  }
}

#pop-options
