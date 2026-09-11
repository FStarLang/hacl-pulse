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

(** The flat C interface to Ed25519.

      void Hacl_Ed25519_Ptr_secret_to_public(uint8_t *pub, uint8_t *secret);
      void Hacl_Ed25519_Ptr_expand_keys(uint8_t *keys, uint8_t *secret);
      void Hacl_Ed25519_Ptr_sign(uint8_t *sig, uint8_t *secret,
                                 uint8_t *msg, size_t msg_len);
      void Hacl_Ed25519_Ptr_sign_expanded(uint8_t *sig, uint8_t *pub,
                                          uint8_t *priv, uint8_t *prefix,
                                          uint8_t *msg, size_t msg_len);
      bool Hacl_Ed25519_Ptr_verify(uint8_t *pub, uint8_t *msg, size_t msg_len,
                                   uint8_t *sig);

    [secret] and [pub] are thirty-two bytes, [sig] is sixty-four, [keys] is
    ninety-six (the public key, then the clamped scalar, then the nonce
    prefix).  [sign_expanded] takes those last three pieces separately so
    that a caller who has kept them can sign without hashing the seed
    again.  Messages must be shorter than [2^32] bytes. *)
module Hacl.Ed25519.Ptr

#lang-pulse

open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module E = Spec.Ed25519

fn secret_to_public (pub: AP.ptr S8.t) (secret: AP.ptr S8.t)
                    (#vout: erased (Seq.seq S8.t))
                    (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires AP.pts_to pub vout ** AP.pts_to secret #ps vs **
  pure (Seq.length vout == 32)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to pub vout' ** AP.pts_to secret #ps vs **
  pure (vout' == E.secret_to_public vs)
{
  let so = S.arrayptr_to_slice_intro pub 32sz;
  let sk = S.arrayptr_to_slice_intro secret 32sz;
  Hacl.Ed25519.secret_to_public so sk;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sk;
}

fn expand_keys (keys: AP.ptr S8.t) (secret: AP.ptr S8.t)
               (#vout: erased (Seq.seq S8.t))
               (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
requires AP.pts_to keys vout ** AP.pts_to secret #ps vs **
  pure (Seq.length vout == 96)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to keys vout' ** AP.pts_to secret #ps vs **
  pure (vout' == E.expand_keys vs)
{
  let so = S.arrayptr_to_slice_intro keys 96sz;
  let sk = S.arrayptr_to_slice_intro secret 32sz;
  Hacl.Ed25519.expand_keys so sk;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sk;
}

fn sign (sg: AP.ptr S8.t) (secret: AP.ptr S8.t)
        (msg: AP.ptr S8.t) (msg_len: SZ.t)
        (#vsg: erased (Seq.seq S8.t))
        (#ps: perm) (#vs: erased (Seq.lseq S8.t 32))
        (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires AP.pts_to sg vsg ** AP.pts_to secret #ps vs ** AP.pts_to msg #pm vm **
  pure (Seq.length vsg == 64 /\ Seq.length vm == SZ.v msg_len /\
        SZ.fits (64 + Seq.length vm))
ensures exists* (vsg': Seq.seq S8.t).
  AP.pts_to sg vsg' ** AP.pts_to secret #ps vs ** AP.pts_to msg #pm vm **
  pure (vsg' == E.sign vs vm)
{
  let so = S.arrayptr_to_slice_intro sg 64sz;
  let sk = S.arrayptr_to_slice_intro secret 32sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Ed25519.sign so sk sm;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim sm;
}

fn sign_expanded (sg: AP.ptr S8.t) (pub: AP.ptr S8.t) (priv: AP.ptr S8.t)
                 (prefix: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
                 (#vsg: erased (Seq.seq S8.t))
                 (#ppub: perm) (#vpub: erased (Seq.lseq S8.t 32))
                 (#ppriv: perm) (#vpriv: erased (Seq.lseq S8.t 32))
                 (#ppre: perm) (#vpre: erased (Seq.lseq S8.t 32))
                 (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
requires AP.pts_to sg vsg ** AP.pts_to pub #ppub vpub **
  AP.pts_to priv #ppriv vpriv ** AP.pts_to prefix #ppre vpre **
  AP.pts_to msg #pm vm **
  pure (Seq.length vsg == 64 /\ Seq.length vm == SZ.v msg_len /\
        SZ.fits (64 + Seq.length vm))
ensures exists* (vsg': Seq.seq S8.t).
  AP.pts_to sg vsg' ** AP.pts_to pub #ppub vpub **
  AP.pts_to priv #ppriv vpriv ** AP.pts_to prefix #ppre vpre **
  AP.pts_to msg #pm vm **
  pure (vsg' == E.sign_expanded vpub vpriv vpre vm)
{
  let so = S.arrayptr_to_slice_intro sg 64sz;
  let sa = S.arrayptr_to_slice_intro pub 32sz;
  let sb = S.arrayptr_to_slice_intro priv 32sz;
  let sc = S.arrayptr_to_slice_intro prefix 32sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  Hacl.Ed25519.sign_expanded so sa sb sc sm;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim sb;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim sm;
}

fn verify (pub: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
          (sg: AP.ptr S8.t)
          (#ppub: perm) (#vpub: erased (Seq.lseq S8.t 32))
          (#pm: perm) (#vm: erased (m: Seq.seq S8.t { E.msg_ok m }))
          (#psg: perm) (#vsg: erased (Seq.lseq S8.t 64))
requires AP.pts_to pub #ppub vpub ** AP.pts_to msg #pm vm **
  AP.pts_to sg #psg vsg **
  pure (Seq.length vm == SZ.v msg_len /\ SZ.fits (64 + Seq.length vm))
returns r: bool
ensures AP.pts_to pub #ppub vpub ** AP.pts_to msg #pm vm **
  AP.pts_to sg #psg vsg **
  pure (r == E.verify vpub vm vsg)
{
  let sa = S.arrayptr_to_slice_intro pub 32sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let ss = S.arrayptr_to_slice_intro sg 64sz;
  let r = Hacl.Ed25519.verify sa sm ss;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim ss;
  r
}
