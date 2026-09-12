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

(** ECDSA over P-256, with the hash included.

    Four signing functions and four verifying ones, differing only in how
    the message is reduced to a scalar.  Each is the corresponding
    {!Hacl.P256.Msg} reduction followed by {!Hacl.P256.Sign.sign} or
    {!Hacl.P256.Verify.verify}. *)
module Hacl.P256

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum256
open Hacl.P256.Msg

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module P = Spec.P256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** As always, the total wrappers exist because an [ensures] is elaborated
    without the [requires] in scope, and the specifications are refined. *)

let ok_sig (vsk vn: Seq.seq S8.t) : prop =
  Seq.length vsk == 32 /\ Seq.length vn == 32

let wsign (m: P.qelem) (vsk vn: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if ok_sig vsk vn then P.ecdsa_sign_msg_as_qelem m vsk vn else None

let wverify (m: P.qelem) (vp vr vs: Seq.seq S8.t) : GTot bool =
  if Seq.length vp = 64 && Seq.length vr = 32 && Seq.length vs = 32
  then P.ecdsa_verify_msg_as_qelem m vp vr vs else false

(** {2 Signing}

    The message is reduced to a scalar, then signed.  The nonce is the
    caller's responsibility: reusing one reveals the private key. *)

fn ecdsa_sign_sha256 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (sk nonce: A.array S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb < pow2 61 /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
        ** pure (SZ.v msg_len == Seq.length vb)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (s256 vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (s256 vb) vsk vn)))
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; A.pts_to_len c0;
  sha256_qelem c0 msg msg_len;
  let r = Hacl.P256.Sign.sign out c0 sk nonce;
  r
}

fn ecdsa_sign_sha384 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (sk nonce: A.array S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb < pow2 61 /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
        ** pure (SZ.v msg_len == Seq.length vb)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (s384 vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (s384 vb) vsk vn)))
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; A.pts_to_len c0;
  sha384_qelem c0 msg msg_len;
  let r = Hacl.P256.Sign.sign out c0 sk nonce;
  r
}

fn ecdsa_sign_sha512 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
       (sk nonce: A.array S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb < pow2 61 /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
        ** pure (SZ.v msg_len == Seq.length vb)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (s512 vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (s512 vb) vsk vn)))
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; A.pts_to_len c0;
  sha512_qelem c0 msg msg_len;
  let r = Hacl.P256.Sign.sign out c0 sk nonce;
  r
}

fn ecdsa_sign_without_hash (out msg sk nonce: A.array S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ 32 <= Seq.length vb /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (mqe vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (mqe vb) vsk vn)))
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; A.pts_to_len c0;
  msg_qelem c0 msg;
  let r = Hacl.P256.Sign.sign out c0 sk nonce;
  r
}

(** {2 Verifying}

    Nothing here is secret, so these need not be constant time -- but they
    are anyway, since they share the code of the signing path. *)

fn ecdsa_verify_sha256 (msg: A.array S8.t) (msg_len: SZ.t)
       (pk sig_r sig_s: A.array S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (Seq.length vb < pow2 61 /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
        ** pure (SZ.v msg_len == Seq.length vb)
returns res: bool
ensures
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (res == wverify (s256 vb) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; A.pts_to_len c0;
  sha256_qelem c0 msg msg_len;
  let res = Hacl.P256.Verify.verify c0 pk sig_r sig_s;
  res
}

fn ecdsa_verify_sha384 (msg: A.array S8.t) (msg_len: SZ.t)
       (pk sig_r sig_s: A.array S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (Seq.length vb < pow2 61 /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
        ** pure (SZ.v msg_len == Seq.length vb)
returns res: bool
ensures
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (res == wverify (s384 vb) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; A.pts_to_len c0;
  sha384_qelem c0 msg msg_len;
  let res = Hacl.P256.Verify.verify c0 pk sig_r sig_s;
  res
}

fn ecdsa_verify_sha512 (msg: A.array S8.t) (msg_len: SZ.t)
       (pk sig_r sig_s: A.array S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (Seq.length vb < pow2 61 /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
        ** pure (SZ.v msg_len == Seq.length vb)
returns res: bool
ensures
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (res == wverify (s512 vb) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; A.pts_to_len c0;
  sha512_qelem c0 msg msg_len;
  let res = Hacl.P256.Verify.verify c0 pk sig_r sig_s;
  res
}

fn ecdsa_verify_without_hash (msg pk sig_r sig_s: A.array S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (32 <= Seq.length vb /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (res == wverify (mqe vb) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 16sz |]; A.pts_to_len c0; A.pts_to_len c0;
  msg_qelem c0 msg;
  let res = Hacl.P256.Verify.verify c0 pk sig_r sig_s;
  res
}

#pop-options
