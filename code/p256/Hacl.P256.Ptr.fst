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

(** The flat C interface to P-256.

      bool Hacl_P256_Ptr_ecdsa_sign_sha256(uint8_t *sig, uint8_t *msg,
                                           size_t msg_len, uint8_t *sk,
                                           uint8_t *nonce);
      bool Hacl_P256_Ptr_ecdsa_sign_sha384(...);
      bool Hacl_P256_Ptr_ecdsa_sign_sha512(...);
      bool Hacl_P256_Ptr_ecdsa_sign_without_hash(...);
      bool Hacl_P256_Ptr_ecdsa_verify_sha256(uint8_t *msg, size_t msg_len,
                                             uint8_t *pk, uint8_t *sig_r,
                                             uint8_t *sig_s);
      bool Hacl_P256_Ptr_ecdsa_verify_sha384(...);
      bool Hacl_P256_Ptr_ecdsa_verify_sha512(...);
      bool Hacl_P256_Ptr_ecdsa_verify_without_hash(...);
      bool Hacl_P256_Ptr_validate_private_key(uint8_t *sk);
      bool Hacl_P256_Ptr_validate_public_key(uint8_t *pk);
      void Hacl_P256_Ptr_raw_to_uncompressed(uint8_t *out, uint8_t *pk);
      void Hacl_P256_Ptr_raw_to_compressed(uint8_t *out, uint8_t *pk);
      bool Hacl_P256_Ptr_uncompressed_to_raw(uint8_t *out, uint8_t *pk);
      bool Hacl_P256_Ptr_compressed_to_raw(uint8_t *out, uint8_t *pk);
      bool Hacl_P256_Ptr_dh_initiator(uint8_t *pk, uint8_t *sk);
      bool Hacl_P256_Ptr_dh_responder(uint8_t *out, uint8_t *pk, uint8_t *sk);

    Scalars -- private keys, nonces, signature halves -- are thirty-two
    bytes big-endian.  A raw public key or shared secret is sixty-four,
    [x || y]; the SEC1 forms are sixty-five ([0x04 || x || y]) and
    thirty-three ([0x02] or [0x03], then [x]).  A signature is sixty-four,
    [r || s].  The [without_hash] variants take the message as the
    representative directly and so insist on at least thirty-two bytes;
    the hashed ones accept anything shorter than [2^61].

    Unlike Ed25519, this interface takes the nonce from the caller.
    HACL* has no RFC 6979 here and neither does this; reusing a nonce
    reveals the private key. *)
module Hacl.P256.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.P256.Msg
open Hacl.P256

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module P = Spec.P256

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 ECDSA} *)

fn ecdsa_sign_sha256 (sg: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
       (sk: AP.ptr S8.t) (nonce: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires AP.pts_to sg vo ** AP.pts_to msg #pb vb **
  AP.pts_to sk #pk vsk ** AP.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb == SZ.v msg_len /\ Seq.length vb < pow2 61 /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to sg wo ** AP.pts_to msg #pb vb **
  AP.pts_to sk #pk vsk ** AP.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (s256 vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (s256 vb) vsk vn)))
{
  let so = S.arrayptr_to_slice_intro sg 64sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let ss = S.arrayptr_to_slice_intro sk 32sz;
  let sn = S.arrayptr_to_slice_intro nonce 32sz;
  let r = sign_sha256 so sm ss sn;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim ss;
  S.arrayptr_to_slice_elim sn;
  r
}

fn ecdsa_sign_sha384 (sg: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
       (sk: AP.ptr S8.t) (nonce: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires AP.pts_to sg vo ** AP.pts_to msg #pb vb **
  AP.pts_to sk #pk vsk ** AP.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb == SZ.v msg_len /\ Seq.length vb < pow2 61 /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to sg wo ** AP.pts_to msg #pb vb **
  AP.pts_to sk #pk vsk ** AP.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (s384 vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (s384 vb) vsk vn)))
{
  let so = S.arrayptr_to_slice_intro sg 64sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let ss = S.arrayptr_to_slice_intro sk 32sz;
  let sn = S.arrayptr_to_slice_intro nonce 32sz;
  let r = sign_sha384 so sm ss sn;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim ss;
  S.arrayptr_to_slice_elim sn;
  r
}

fn ecdsa_sign_sha512 (sg: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
       (sk: AP.ptr S8.t) (nonce: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires AP.pts_to sg vo ** AP.pts_to msg #pb vb **
  AP.pts_to sk #pk vsk ** AP.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb == SZ.v msg_len /\ Seq.length vb < pow2 61 /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to sg wo ** AP.pts_to msg #pb vb **
  AP.pts_to sk #pk vsk ** AP.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (s512 vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (s512 vb) vsk vn)))
{
  let so = S.arrayptr_to_slice_intro sg 64sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let ss = S.arrayptr_to_slice_intro sk 32sz;
  let sn = S.arrayptr_to_slice_intro nonce 32sz;
  let r = sign_sha512 so sm ss sn;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim ss;
  S.arrayptr_to_slice_elim sn;
  r
}

fn ecdsa_sign_without_hash (sg: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
       (sk: AP.ptr S8.t) (nonce: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pk: perm) (#vsk: erased (Seq.seq S8.t))
       (#pn: perm) (#vn: erased (Seq.seq S8.t))
requires AP.pts_to sg vo ** AP.pts_to msg #pb vb **
  AP.pts_to sk #pk vsk ** AP.pts_to nonce #pn vn **
  pure (Seq.length vo == 64 /\ Seq.length vb == SZ.v msg_len /\ 32 <= Seq.length vb /\
        Seq.length vsk == 32 /\ Seq.length vn == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to sg wo ** AP.pts_to msg #pb vb **
  AP.pts_to sk #pk vsk ** AP.pts_to nonce #pn vn **
  pure (Seq.length wo == 64 /\ r == Some? (wsign (mqe vb) vsk vn) /\
        (r ==> wo == Some?.v (wsign (mqe vb) vsk vn)))
{
  let so = S.arrayptr_to_slice_intro sg 64sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let ss = S.arrayptr_to_slice_intro sk 32sz;
  let sn = S.arrayptr_to_slice_intro nonce 32sz;
  let r = sign_without_hash so sm ss sn;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim ss;
  S.arrayptr_to_slice_elim sn;
  r
}

fn ecdsa_verify_sha256 (msg: AP.ptr S8.t) (msg_len: SZ.t) (pk: AP.ptr S8.t)
       (sig_r: AP.ptr S8.t) (sig_s: AP.ptr S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires AP.pts_to msg #pb vb ** AP.pts_to pk #pp vp **
  AP.pts_to sig_r #pr vr ** AP.pts_to sig_s #ps vs **
  pure (Seq.length vb == SZ.v msg_len /\ Seq.length vb < pow2 61 /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures AP.pts_to msg #pb vb ** AP.pts_to pk #pp vp **
  AP.pts_to sig_r #pr vr ** AP.pts_to sig_s #ps vs **
  pure (res == wverify (s256 vb) vp vr vs)
{
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sp = S.arrayptr_to_slice_intro pk 64sz;
  let sr = S.arrayptr_to_slice_intro sig_r 32sz;
  let ss = S.arrayptr_to_slice_intro sig_s 32sz;
  let res = verify_sha256 sm sp sr ss;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim sr;
  S.arrayptr_to_slice_elim ss;
  res
}

fn ecdsa_verify_sha384 (msg: AP.ptr S8.t) (msg_len: SZ.t) (pk: AP.ptr S8.t)
       (sig_r: AP.ptr S8.t) (sig_s: AP.ptr S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires AP.pts_to msg #pb vb ** AP.pts_to pk #pp vp **
  AP.pts_to sig_r #pr vr ** AP.pts_to sig_s #ps vs **
  pure (Seq.length vb == SZ.v msg_len /\ Seq.length vb < pow2 61 /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures AP.pts_to msg #pb vb ** AP.pts_to pk #pp vp **
  AP.pts_to sig_r #pr vr ** AP.pts_to sig_s #ps vs **
  pure (res == wverify (s384 vb) vp vr vs)
{
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sp = S.arrayptr_to_slice_intro pk 64sz;
  let sr = S.arrayptr_to_slice_intro sig_r 32sz;
  let ss = S.arrayptr_to_slice_intro sig_s 32sz;
  let res = verify_sha384 sm sp sr ss;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim sr;
  S.arrayptr_to_slice_elim ss;
  res
}

fn ecdsa_verify_sha512 (msg: AP.ptr S8.t) (msg_len: SZ.t) (pk: AP.ptr S8.t)
       (sig_r: AP.ptr S8.t) (sig_s: AP.ptr S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires AP.pts_to msg #pb vb ** AP.pts_to pk #pp vp **
  AP.pts_to sig_r #pr vr ** AP.pts_to sig_s #ps vs **
  pure (Seq.length vb == SZ.v msg_len /\ Seq.length vb < pow2 61 /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures AP.pts_to msg #pb vb ** AP.pts_to pk #pp vp **
  AP.pts_to sig_r #pr vr ** AP.pts_to sig_s #ps vs **
  pure (res == wverify (s512 vb) vp vr vs)
{
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sp = S.arrayptr_to_slice_intro pk 64sz;
  let sr = S.arrayptr_to_slice_intro sig_r 32sz;
  let ss = S.arrayptr_to_slice_intro sig_s 32sz;
  let res = verify_sha512 sm sp sr ss;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim sr;
  S.arrayptr_to_slice_elim ss;
  res
}

fn ecdsa_verify_without_hash (msg: AP.ptr S8.t) (msg_len: SZ.t) (pk: AP.ptr S8.t)
       (sig_r: AP.ptr S8.t) (sig_s: AP.ptr S8.t)
       (#pb: perm) (#vb: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#pr: perm) (#vr: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires AP.pts_to msg #pb vb ** AP.pts_to pk #pp vp **
  AP.pts_to sig_r #pr vr ** AP.pts_to sig_s #ps vs **
  pure (Seq.length vb == SZ.v msg_len /\ 32 <= Seq.length vb /\ Seq.length vp == 64 /\
        Seq.length vr == 32 /\ Seq.length vs == 32)
returns res: bool
ensures AP.pts_to msg #pb vb ** AP.pts_to pk #pp vp **
  AP.pts_to sig_r #pr vr ** AP.pts_to sig_s #ps vs **
  pure (res == wverify (mqe vb) vp vr vs)
{
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sp = S.arrayptr_to_slice_intro pk 64sz;
  let sr = S.arrayptr_to_slice_intro sig_r 32sz;
  let ss = S.arrayptr_to_slice_intro sig_s 32sz;
  let res = verify_without_hash sm sp sr ss;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim sr;
  S.arrayptr_to_slice_elim ss;
  res
}

(** {2 Key validation} *)

fn validate_private_key (b: AP.ptr S8.t) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires AP.pts_to b #pb vb ** pure (Seq.length vb == 32)
returns r: bool
ensures AP.pts_to b #pb vb ** pure (r == (0 < Hacl.Spec.Bytes.be_nat vb && Hacl.Spec.Bytes.be_nat vb < P.order))
{
  let s = S.arrayptr_to_slice_intro b 32sz;
  let r = Hacl.P256.Key.validate_private_key s;
  S.arrayptr_to_slice_elim s;
  r
}

fn validate_public_key (b: AP.ptr S8.t) (#pb: perm) (#vb: erased (Seq.seq S8.t))
requires AP.pts_to b #pb vb ** pure (Seq.length vb == 64)
returns r: bool
ensures AP.pts_to b #pb vb ** pure (r == Some? (Hacl.P256.Encode.lpt vb))
{
  let s = S.arrayptr_to_slice_intro b 64sz;
  let r = Hacl.P256.Key.Public.validate_public_key s;
  S.arrayptr_to_slice_elim s;
  r
}

(** {2 SEC1 conversions} *)

fn raw_to_uncompressed (out: AP.ptr S8.t) (pk: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires AP.pts_to out vo ** AP.pts_to pk #pp vp **
  pure (Seq.length vo == 65 /\ Seq.length vp == 64)
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to out wo ** AP.pts_to pk #pp vp **
  pure (Seq.length wo == 65 /\ wo == Hacl.P256.Sec1.r2u vp)
{
  let so = S.arrayptr_to_slice_intro out 65sz;
  let sp = S.arrayptr_to_slice_intro pk 64sz;
  Hacl.P256.Sec1.raw_to_uncompressed so sp;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sp;
  }

fn raw_to_compressed (out: AP.ptr S8.t) (pk: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires AP.pts_to out vo ** AP.pts_to pk #pp vp **
  pure (Seq.length vo == 33 /\ Seq.length vp == 64)
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to out wo ** AP.pts_to pk #pp vp **
  pure (Seq.length wo == 33 /\ wo == Hacl.P256.Sec1.r2c vp)
{
  let so = S.arrayptr_to_slice_intro out 33sz;
  let sp = S.arrayptr_to_slice_intro pk 64sz;
  Hacl.P256.Sec1.raw_to_compressed so sp;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sp;
  }

fn uncompressed_to_raw (out: AP.ptr S8.t) (pk: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires AP.pts_to out vo ** AP.pts_to pk #pp vp **
  pure (Seq.length vo == 64 /\ Seq.length vp == 65)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to out wo ** AP.pts_to pk #pp vp **
  pure (Seq.length wo == 64 /\ r == Some? (Hacl.P256.Sec1.u2r vp) /\
        (r ==> wo == Some?.v (Hacl.P256.Sec1.u2r vp)))
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let sp = S.arrayptr_to_slice_intro pk 65sz;
  let r = Hacl.P256.Sec1.uncompressed_to_raw so sp;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sp;
  r
}

fn compressed_to_raw (out: AP.ptr S8.t) (pk: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires AP.pts_to out vo ** AP.pts_to pk #pp vp **
  pure (Seq.length vo == 64 /\ Seq.length vp == 33)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to out wo ** AP.pts_to pk #pp vp **
  pure (Seq.length wo == 64 /\ r == Some? (Hacl.P256.Sec1.c2r vp) /\
        (r ==> wo == Some?.v (Hacl.P256.Sec1.c2r vp)))
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let sp = S.arrayptr_to_slice_intro pk 33sz;
  let r = Hacl.P256.Sec1.compressed_to_raw so sp;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sp;
  r
}

(** {2 ECDH} *)

fn dh_initiator (out: AP.ptr S8.t) (sk: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires AP.pts_to out vo ** AP.pts_to sk #ps vs **
  pure (Seq.length vo == 64 /\ Seq.length vs == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to out wo ** AP.pts_to sk #ps vs **
  pure (Seq.length wo == 64 /\ r == Some? (Hacl.P256.Ecdh.dhi vs) /\
        (r ==> wo == Some?.v (Hacl.P256.Ecdh.dhi vs)))
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let ss = S.arrayptr_to_slice_intro sk 32sz;
  let r = Hacl.P256.Ecdh.dh_initiator so ss;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim ss;
  r
}

fn dh_responder (out: AP.ptr S8.t) (pk: AP.ptr S8.t) (sk: AP.ptr S8.t)
       (#vo: erased (Seq.seq S8.t))
       (#pp: perm) (#vp: erased (Seq.seq S8.t))
       (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires AP.pts_to out vo ** AP.pts_to pk #pp vp ** AP.pts_to sk #ps vs **
  pure (Seq.length vo == 64 /\ Seq.length vp == 64 /\ Seq.length vs == 32)
returns r: bool
ensures exists* (wo: Seq.seq S8.t).
  AP.pts_to out wo ** AP.pts_to pk #pp vp ** AP.pts_to sk #ps vs **
  pure (Seq.length wo == 64 /\ r == Some? (Hacl.P256.Ecdh.dhr vp vs) /\
        (r ==> wo == Some?.v (Hacl.P256.Ecdh.dhr vp vs)))
{
  let so = S.arrayptr_to_slice_intro out 64sz;
  let sp = S.arrayptr_to_slice_intro pk 64sz;
  let ss = S.arrayptr_to_slice_intro sk 32sz;
  let r = Hacl.P256.Ecdh.dh_responder so sp ss;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sp;
  S.arrayptr_to_slice_elim ss;
  r
}

#pop-options
