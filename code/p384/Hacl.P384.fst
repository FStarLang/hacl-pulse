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

(** ECDSA over P-384 with SHA-384.

    The public key is the raw affine point [x || y] and the signature the
    raw pair [r || s], each ninety-six bytes of big-endian coordinates; a
    private key and a nonce are forty-eight.  Each function is the message
    representative of [Spec.P384.sha384_as_qelem] followed by
    {!Hacl.P384.Sign.sign} or {!Hacl.P384.Verify.verify}.  Key validation
    is in {!Hacl.P384.Key} and ECDH, which is also key generation, in
    {!Hacl.P384.Ecdh}. *)
module Hacl.P384

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Spec.Bytes
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.Bignum.Convert
open Hacl.P384.Tables
open Hacl.P384.Field
open Hacl.P384.Verify

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module Hash = Hacl.Hash.SHA2
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** As always, the total wrapper exists because an [ensures] is elaborated
    without the [requires] in scope, and the specification is refined. *)
let wverify (vb vp vs: Seq.seq S8.t) : GTot bool =
  if Seq.length vb < pow2 61 && Seq.length vp = 96 && Seq.length vs = 96
  then P.verify_sha384 vb vp vs else false

let wsign (vb vsk vn: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 96)) =
  if Seq.length vb < pow2 61 && Seq.length vsk = 48 && Seq.length vn = 48
  then P.sign_sha384 vb vsk vn else None

let s384 (vb: Seq.seq S8.t) : GTot nat =
  if Seq.length vb < pow2 61 then P.sha384_as_qelem vb else 0

(** The message representative: SHA-384, read big-endian, reduced mod [n]. *)
fn sha384_qelem (mq: A.array S64.t) (msg: A.array S8.t) (msg_len: SZ.t)
                (#vm: erased (Seq.seq S64.t))
                (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to mq vm ** A.pts_to msg #pb vb **
  pure (Seq.length vm == 6 /\ Seq.length vb < pow2 61)
         ** pure (SZ.v msg_len == Seq.length vb)
ensures exists* (wm: Seq.seq S64.t).
  A.pts_to mq wm ** A.pts_to msg #pb vb **
  pure (Seq.length wm == 6 /\ num wm < P.order /\ num wm == s384 vb)
{
  facts ();
  P.sha384_ok vb;
  let z8 = S8.classify 0uy;
  let mut d = [| z8; 48sz |];
  Mem.track d; A.pts_to_len d;
  Hash.sha384 d msg msg_len;
  with vd. assert (A.pts_to d vd);
  assert (pure (Seq.equal (Seq.slice vd 0 48) vd));
  let z = S64.zero;
  let mut t = [| z; 6sz |];
  Mem.track t; A.pts_to_len t;
  from_bytes_be t 6sz d;
  let qm = qms ();
  let q2 = qr2 ();
  reduce mq t qm q2 qmu;
  drop_table q2;
  drop_table qm;
  Mem.wipe t 6sz;
  Mem.wipe d 48sz;
  ()
}

(** [ecdsa_sign_sha384 out msg msg_len private_key nonce] writes the
    signature [r || s] (96 bytes) of the [msg_len] bytes at [msg] to [out]
    and returns [true], or returns [false] if the private key or the nonce
    is not in [1, n) or, with negligible probability, [r] or [s] is zero.
    The nonce must be secret, uniformly random, and never reused. *)
fn ecdsa_sign_sha384 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (private_key nonce: A.array S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to msg #pb vb **
  A.pts_to private_key #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 96 /\ Seq.length vb < pow2 61 /\
        Seq.length vsk == 48 /\ Seq.length vn == 48)
        ** pure (SZ.v msg_len == Seq.length vb)
returns res: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to msg #pb vb **
  A.pts_to private_key #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 96 /\ res == Some? (wsign vb vsk vn) /\
        (res ==> wo == Some?.v (wsign vb vsk vn)))
{
  let z = S64.zero;
  let mut m = [| z; 6sz |];
  Mem.track m; A.pts_to_len m;
  sha384_qelem m msg msg_len;
  let res = Hacl.P384.Sign.sign out m private_key nonce;
  Mem.wipe m 6sz;
  res
}

(** [ecdsa_verify_sha384 msg msg_len public_key signature] is [true] exactly
    when [signature] ([r || s], 96 bytes) is a valid ECDSA P-384/SHA-384
    signature of the [msg_len] bytes at [msg] under [public_key] ([x || y],
    96 bytes).  An invalid public key is rejected, not an error. *)
fn ecdsa_verify_sha384 (msg: A.array S8.t) (msg_len: SZ.t)
       (public_key signature: A.array S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  A.pts_to msg #pb vb ** A.pts_to public_key #pp vp ** A.pts_to signature #ps vs **
  pure (Seq.length vb < pow2 61 /\ Seq.length vp == 96 /\ Seq.length vs == 96)
        ** pure (SZ.v msg_len == Seq.length vb)
returns res: bool
ensures
  A.pts_to msg #pb vb ** A.pts_to public_key #pp vp ** A.pts_to signature #ps vs **
  pure (res == wverify vb vp vs)
{
  let z = S64.zero;
  let mut m = [| z; 6sz |];
  Mem.track m; A.pts_to_len m;
  sha384_qelem m msg msg_len;
  let res = verify m public_key signature;
  Mem.wipe m 6sz;
  res
}

#pop-options
