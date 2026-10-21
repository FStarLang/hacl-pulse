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

(** ECDSA over secp256k1, with the hash included.

    Two families of four.  The [ecdsa_] functions are plain ECDSA; the
    [secp256k1_ecdsa_] ones additionally enforce the low-S rule that
    Bitcoin's consensus layer imposes, by normalising after signing and by
    rejecting a high [s] on verification.  Within each family the message
    is either a thirty-two byte hash the caller has already computed or a
    message this hashes with SHA2-256.

    Each is a reduction from {!Hacl.K256.Msg} followed by
    {!Hacl.K256.Sign.sign} or {!Hacl.K256.Verify.verify}, with at most one
    call into {!Hacl.K256.LowS} around it. *)
module Hacl.K256

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Hacl.K256.Msg

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** As always, the total wrappers exist because an [ensures] is elaborated
    without the [requires] in scope, and the specifications are refined. *)

let wsign (m: K.qelem) (vsk vn: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vsk = 32 && Seq.length vn = 32
  then K.ecdsa_sign_msg_as_qelem m vsk vn else None

let wsignl (m: K.qelem) (vsk vn: Seq.seq S8.t) : GTot (option (Seq.lseq S8.t 64)) =
  if Seq.length vsk = 32 && Seq.length vn = 32
  then K.secp256k1_ecdsa_sign_msg_as_qelem m vsk vn else None

let wverify (m: K.qelem) (vp vr vs: Seq.seq S8.t) : GTot bool =
  if Seq.length vp = 64 && Seq.length vr = 32 && Seq.length vs = 32
  then K.ecdsa_verify_msg_as_qelem m vp vr vs else false

let wverifyl (m: K.qelem) (vp vr vs: Seq.seq S8.t) : GTot bool =
  if Seq.length vp = 64 && Seq.length vr = 32 && Seq.length vs = 32
  then K.secp256k1_ecdsa_verify_msg_as_qelem m vp vr vs else false

(** {2 Signing}

    The nonce is the caller's responsibility: HACL* does not implement RFC
    6979 and neither does this, and reusing a nonce reveals the key. *)

fn ecdsa_sign_hashed_msg (out: A.array S8.t) (msg: A.array S8.t) (sk nonce: A.array S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb == 32 /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (mqe vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (mqe vb) vsk vn)))
{
  let z = S64.zero;
  let mut c0 = [| z; 4sz |];
  Mem.track c0; A.pts_to_len c0; A.pts_to_len c0;
  msg_qelem c0 msg;
  let r = Hacl.K256.Sign.sign out c0 sk nonce;
  Mem.wipe c0 4sz;
  r
}

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
  let mut c0 = [| z; 4sz |];
  Mem.track c0; A.pts_to_len c0; A.pts_to_len c0;
  sha256_qelem c0 msg msg_len;
  let r = Hacl.K256.Sign.sign out c0 sk nonce;
  Mem.wipe c0 4sz;
  r
}

(** {2 Signing, with the low-S rule}

    The same signature, then normalised.  Normalisation of a signature that
    was just produced cannot fail, but the specification is a composition of
    two partial functions and the code follows it. *)

fn secp256k1_ecdsa_sign_hashed_msg (out: A.array S8.t) (msg: A.array S8.t) (sk nonce: A.array S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires
  A.pts_to out vo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb == 32 /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  A.pts_to out wo ** A.pts_to msg #pb vb **
  A.pts_to sk #pk vsk ** A.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsignl (mqe vb) vsk vn) /\
        (r ==> wo == Some?.v (wsignl (mqe vb) vsk vn)))
{
  let z = S64.zero;
  let mut c0 = [| z; 4sz |];
  Mem.track c0; A.pts_to_len c0; A.pts_to_len c0;
  msg_qelem c0 msg;
  let r = Hacl.K256.Sign.sign out c0 sk nonce;
  if r {
    let rn = Hacl.K256.LowS.signature_normalize out;
    Mem.wipe c0 4sz;
    rn
  } else {
    Mem.wipe c0 4sz;
    false
  }
}

fn secp256k1_ecdsa_sign_sha256 (out: A.array S8.t) (msg: A.array S8.t) (msg_len: SZ.t)
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
  pure (Seq.length wo == 64 /\ r == Some? (wsignl (s256 vb) vsk vn) /\
        (r ==> wo == Some?.v (wsignl (s256 vb) vsk vn)))
{
  let z = S64.zero;
  let mut c0 = [| z; 4sz |];
  Mem.track c0; A.pts_to_len c0; A.pts_to_len c0;
  sha256_qelem c0 msg msg_len;
  let r = Hacl.K256.Sign.sign out c0 sk nonce;
  if r {
    let rn = Hacl.K256.LowS.signature_normalize out;
    Mem.wipe c0 4sz;
    rn
  } else {
    Mem.wipe c0 4sz;
    false
  }
}

(** {2 Verifying}

    Nothing here is secret, so these need not be constant time -- but they
    are anyway, since they share the code of the signing path. *)

fn ecdsa_verify_hashed_msg (msg: A.array S8.t) (pk sig_r sig_s: A.array S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (Seq.length vb == 32 /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (res == wverify (mqe vb) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 4sz |];
  Mem.track c0; A.pts_to_len c0; A.pts_to_len c0;
  msg_qelem c0 msg;
  let res = Hacl.K256.Verify.verify c0 pk sig_r sig_s;
  Mem.wipe c0 4sz;
  res
}

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
  let mut c0 = [| z; 4sz |];
  Mem.track c0; A.pts_to_len c0; A.pts_to_len c0;
  sha256_qelem c0 msg msg_len;
  let res = Hacl.K256.Verify.verify c0 pk sig_r sig_s;
  Mem.wipe c0 4sz;
  res
}

(** {2 Verifying, with the low-S rule}

    A high [s] is rejected before anything else is done. *)

fn secp256k1_ecdsa_verify_hashed_msg (msg: A.array S8.t) (pk sig_r sig_s: A.array S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (Seq.length vb == 32 /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures
  A.pts_to msg #pb vb ** A.pts_to pk #pp vp **
  A.pts_to sig_r #pr vr ** A.pts_to sig_s #ps vs **
  pure (res == wverifyl (mqe vb) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 4sz |];
  Mem.track c0; A.pts_to_len c0; A.pts_to_len c0;
  msg_qelem c0 msg;
  let lo = Hacl.K256.LowS.is_normalized sig_s;
  if lo {
    let res = Hacl.K256.Verify.verify c0 pk sig_r sig_s;
    Mem.wipe c0 4sz;
    res
  } else {
    Mem.wipe c0 4sz;
    false
  }
}

fn secp256k1_ecdsa_verify_sha256 (msg: A.array S8.t) (msg_len: SZ.t)
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
  pure (res == wverifyl (s256 vb) vp vr vs)
{
  let z = S64.zero;
  let mut c0 = [| z; 4sz |];
  Mem.track c0; A.pts_to_len c0; A.pts_to_len c0;
  sha256_qelem c0 msg msg_len;
  let lo = Hacl.K256.LowS.is_normalized sig_s;
  if lo {
    let res = Hacl.K256.Verify.verify c0 pk sig_r sig_s;
    Mem.wipe c0 4sz;
    res
  } else {
    Mem.wipe c0 4sz;
    false
  }
}

#pop-options
