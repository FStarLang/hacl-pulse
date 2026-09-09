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

(** The flat C interface to ChaCha20.

      void Hacl_Chacha20_Ptr_encrypt(uint8_t *out,
                                     uint8_t *msg, size_t msg_len,
                                     uint8_t *key, uint8_t *nonce,
                                     uint32_t ctr);

    [out] and [msg] must not overlap, [key] is 32 bytes and [nonce] is 12.
    The message length is bounded by [(2^32 - ctr) * 64], which is what it
    takes for the 32-bit block counter not to wrap; on any real platform the
    bound is only reachable with [ctr] very close to [2^32].

    Decryption is the same function -- ChaCha20 is additive -- and is exported
    under its own name so that callers read the way they mean. *)
module Hacl.Chacha20.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Chacha20

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8

fn encrypt (out: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
           (key: AP.ptr S8.t) (nonce: AP.ptr S8.t) (ctr: U32.t)
           (#vout: erased (Seq.seq S8.t))
           (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to msg #pm vmsg **
         AP.pts_to key #pk vkey ** AP.pts_to nonce #pn vnon **
         pure (Seq.length vout == SZ.v msg_len /\ Seq.length vmsg == SZ.v msg_len /\
               Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
               Seq.length vmsg <= max_len ctr)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to msg #pm vmsg **
  AP.pts_to key #pk vkey ** AP.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vmsg <= max_len ctr /\
        vout' == chacha20 vkey vnon ctr vmsg)
{
  let so = S.arrayptr_to_slice_intro out msg_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sk = S.arrayptr_to_slice_intro key 32sz;
  let sn = S.arrayptr_to_slice_intro nonce 12sz;
  Hacl.Chacha20.chacha20_impl so sm sk sn ctr;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim sn;
}

(** Decryption. *)
fn decrypt (out: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
           (key: AP.ptr S8.t) (nonce: AP.ptr S8.t) (ctr: U32.t)
           (#vout: erased (Seq.seq S8.t))
           (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to msg #pm vmsg **
         AP.pts_to key #pk vkey ** AP.pts_to nonce #pn vnon **
         pure (Seq.length vout == SZ.v msg_len /\ Seq.length vmsg == SZ.v msg_len /\
               Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
               Seq.length vmsg <= max_len ctr)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to msg #pm vmsg **
  AP.pts_to key #pk vkey ** AP.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vmsg <= max_len ctr /\
        vout' == chacha20 vkey vnon ctr vmsg)
{
  let so = S.arrayptr_to_slice_intro out msg_len;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sk = S.arrayptr_to_slice_intro key 32sz;
  let sn = S.arrayptr_to_slice_intro nonce 12sz;
  Hacl.Chacha20.chacha20_impl so sm sk sn ctr;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim sn;
}
