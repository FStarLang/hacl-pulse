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

(** ECDSA signing on P-384.

    The nonce is an input, as for P-256: reusing one, or choosing it
    predictably, hands over the private key.  The message arrives already
    reduced to a scalar; {!Hacl.P384} does the hashing.

    The private key and the nonce are secret, so everything that touches
    them is constant time: the ladder selects with masks, and both
    inverses -- of [z] for the affine coordinate and of the nonce -- are
    the constant-time exponentiation.  What is declassified is only the
    validity of the inputs and whether [r] or [s] came out zero, which the
    return value reveals anyway. *)
module Hacl.P384.Sign

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Spec.Bytes
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.P384.Tables
open Hacl.P384.Lemmas
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

(** The signature on numbers, for keys already known to be in range. *)
let core_sig (m d k: nat) : GTot (option (Seq.lseq S8.t 96)) =
  if m < P.order && 0 < d && d < P.order && 0 < k && k < P.order then
    let (px, _) = P.to_aff_point (P.point_mul_g k) in
    let r : P.qelem = px % P.order in
    let s : P.qelem = P.qmul (P.qinv k) (P.qadd m (P.qmul r d)) in
    if r = 0 || s = 0 then None
    else Some (Seq.append (nat_to_be 48 r) (nat_to_be 48 s))
  else None

(** The same on bytes, total. *)
let sgn (m: nat) (vsk vn: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 96)) =
  if m < P.order && Seq.length vsk = 48 && Seq.length vn = 48
  then P.ecdsa_sign_msg_as_qelem m vsk vn else None

#push-options "--fuel 0 --ifuel 1 --z3rlimit 300"

fn sign_core (out: A.array S8.t) (mq d k: A.array S64.t)
             (#vo: erased (Seq.seq S8.t))
             (#pm: perm) (#vm: erased (Seq.seq S64.t))
             (#pd: perm) (#vd: erased (Seq.seq S64.t))
             (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires A.pts_to out vo ** A.pts_to mq #pm vm **
  A.pts_to d #pd vd ** A.pts_to k #pk vk **
  pure (Seq.length vo == 96 /\ Seq.length vm == 6 /\ num vm < P.order /\
        Seq.length vd == 6 /\ 0 < num vd /\ num vd < P.order /\
        Seq.length vk == 6 /\ 0 < num vk /\ num vk < P.order)
returns b: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to mq #pm vm **
  A.pts_to d #pd vd ** A.pts_to k #pk vk **
  pure (Seq.length wo == 96 /\
        b == Some? (core_sig (num vm) (num vd) (num vk)) /\
        (b ==> wo == Some?.v (core_sig (num vm) (num vd) (num vk))))
{
  facts ();
  let z = S64.zero;
  let mut rx = [| z; 6sz |];
  Mem.track rx; A.pts_to_len rx; let mut ry = [| z; 6sz |];
  Mem.track ry; A.pts_to_len ry; let mut rz = [| z; 6sz |];
  Mem.track rz; A.pts_to_len rz; let mut ax = [| z; 6sz |];
  Mem.track ax; A.pts_to_len ax; let mut ay = [| z; 6sz |];
  Mem.track ay; A.pts_to_len ay; let mut r = [| z; 6sz |];
  Mem.track r; A.pts_to_len r; let mut ki = [| z; 6sz |];
  Mem.track ki; A.pts_to_len ki; let mut t1 = [| z; 6sz |];
  Mem.track t1; A.pts_to_len t1; let mut t2 = [| z; 6sz |];
  Mem.track t2; A.pts_to_len t2; let mut s = [| z; 6sz |];
  Mem.track s; A.pts_to_len s;

  (* r = x([k] G) mod n *)
  point_mul_g rx ry rz k;
  with wx wy wz. assert (A.pts_to rx wx ** A.pts_to ry wy ** A.pts_to rz wz);
  peq_out (pt wx wy wz) (P.point_mul_g (num vk));
  to_aff ax ay rx ry rz;
  with vax. assert (A.pts_to ax vax);
  assert (pure (num vax == fst (P.to_aff_point (P.point_mul_g (num vk)))));
  let qm = qms ();
  let q2 = qr2 ();
  reduce r ax qm q2 qmu;
  with vr. assert (A.pts_to r vr);

  (* s = (m + r d) / k mod n *)
  invmod_ct ki k qm q2 qmu;
  with vki. assert (A.pts_to ki vki);
  pw_exp P.order (num vk) (P.order - 2);
  assert (pure (num vki == P.qinv (num vk)));
  mulmod t1 r d qm q2 qmu;
  add_mod t2 mq t1 qm 6sz;
  mulmod s ki t2 qm q2 qmu;
  with vs. assert (A.pts_to s vs);
  assert (pure (num vs ==
    P.qmul (P.qinv (num vk)) (P.qadd (num vm) (P.qmul (num vr) (num vd)))));
  drop_table q2;
  drop_table qm;

  let okr = scalar_ok r;
  let oks = scalar_ok s;
  if (okr && oks) {
    store_pair out r s;
    Mem.wipe s 6sz;
    Mem.wipe t2 6sz;
    Mem.wipe t1 6sz;
    Mem.wipe ki 6sz;
    Mem.wipe r 6sz;
    Mem.wipe ay 6sz;
    Mem.wipe ax 6sz;
    Mem.wipe rz 6sz;
    Mem.wipe ry 6sz;
    Mem.wipe rx 6sz;
    true
  } else {
    A.pts_to_len out;
    Mem.wipe s 6sz;
    Mem.wipe t2 6sz;
    Mem.wipe t1 6sz;
    Mem.wipe ki 6sz;
    Mem.wipe r 6sz;
    Mem.wipe ay 6sz;
    Mem.wipe ax 6sz;
    Mem.wipe rz 6sz;
    Mem.wipe ry 6sz;
    Mem.wipe rx 6sz;
    false
  }
}

(** [sign out m sk nonce] signs the message representative [m]. *)
fn sign (out: A.array S8.t) (mq: A.array S64.t) (sk nonce: A.array S8.t)
        (#vo: erased (Seq.seq S8.t))
        (#pm: perm) (#vm: erased (Seq.seq S64.t))
        (#pk: perm) (#vsk: erased (Seq.seq S8.t))
        (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to mq #pm vm **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 96 /\ Seq.length vm == 6 /\ num vm < P.order /\
        Seq.length vsk == 48 /\ Seq.length vn == 48)
returns b: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to mq #pm vm **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 96 /\ b == Some? (sgn (num vm) vsk vn) /\
        (b ==> wo == Some?.v (sgn (num vm) vsk vn)))
{
  A.pts_to_len out;
  let z = S64.zero;
  let mut d = [| z; 6sz |];
  Mem.track d; A.pts_to_len d; let mut k = [| z; 6sz |];
  Mem.track k; A.pts_to_len k;
  let okd = load_scalar d sk;
  let okk = load_scalar k nonce;
  if (okd && okk) {
    let b = sign_core out mq d k;
    Mem.wipe k 6sz;
    Mem.wipe d 6sz;
    b
  } else {
    Mem.wipe k 6sz;
    Mem.wipe d 6sz;
    false
  }
}

#pop-options
