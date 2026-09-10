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

(** The flat C interface to ChaCha20-Poly1305.

      void Hacl_Chacha20Poly1305_Ptr_encrypt(uint8_t *ct, uint8_t *tag,
                                             uint8_t *msg, size_t msg_len,
                                             uint8_t *aad, size_t aad_len,
                                             uint8_t *key, uint8_t *nonce);

      bool Hacl_Chacha20Poly1305_Ptr_decrypt(uint8_t *msg,
                                             uint8_t *ct, size_t ct_len,
                                             uint8_t *tag,
                                             uint8_t *aad, size_t aad_len,
                                             uint8_t *key, uint8_t *nonce);

    [key] is thirty-two bytes, [nonce] twelve and [tag] sixteen.  [ct] and
    [msg] have the same length and may alias nothing.  Decryption returns
    false and leaves [msg] untouched when the tag does not match.

    A (key, nonce) pair must never be reused: doing so leaks the exclusive-or
    of the two plaintexts and, worse, the Poly1305 one-time key. *)
module Hacl.Chacha20Poly1305.Ptr

#lang-pulse

open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module C = Spec.Chacha20
module Spec = Spec.Chacha20Poly1305

fn encrypt (ct: AP.ptr S8.t) (tag: AP.ptr S8.t)
           (msg: AP.ptr S8.t) (msg_len: SZ.t)
           (aad: AP.ptr S8.t) (aad_len: SZ.t)
           (key: AP.ptr S8.t) (nonce: AP.ptr S8.t)
           (#vct: erased (Seq.seq S8.t)) (#vtag: erased (Seq.seq S8.t))
           (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires AP.pts_to ct vct ** AP.pts_to tag vtag ** AP.pts_to msg #pm vmsg **
         AP.pts_to aad #pa vaad ** AP.pts_to key #pk vkey **
         AP.pts_to nonce #pn vnon **
         pure (Seq.length vct == SZ.v msg_len /\ Seq.length vmsg == SZ.v msg_len /\
               Seq.length vaad == SZ.v aad_len /\ Seq.length vtag == 16 /\
               Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
               SZ.v msg_len <= C.max_len 1ul)
ensures exists* (vct': Seq.seq S8.t) (vtag': Seq.seq S8.t).
  AP.pts_to ct vct' ** AP.pts_to tag vtag' ** AP.pts_to msg #pm vmsg **
  AP.pts_to aad #pa vaad ** AP.pts_to key #pk vkey ** AP.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vmsg <= C.max_len 1ul /\
        Seq.length vct' == Seq.length vmsg /\ Seq.length vtag' == 16 /\
        (vct', vtag') == Spec.encrypt vkey vnon vaad vmsg)
{
  let sc = S.arrayptr_to_slice_intro ct msg_len;
  let st = S.arrayptr_to_slice_intro tag 16sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sa = S.arrayptr_to_slice_intro aad aad_len;
  let sk = S.arrayptr_to_slice_intro key 32sz;
  let sn = S.arrayptr_to_slice_intro nonce 12sz;
  Hacl.Chacha20Poly1305.encrypt sc st sm sa sk sn;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim sn;
}

fn decrypt (msg: AP.ptr S8.t)
           (ct: AP.ptr S8.t) (ct_len: SZ.t)
           (tag: AP.ptr S8.t)
           (aad: AP.ptr S8.t) (aad_len: SZ.t)
           (key: AP.ptr S8.t) (nonce: AP.ptr S8.t)
           (#vmsg: erased (Seq.seq S8.t))
           (#pc: perm) (#vct: erased (Seq.seq S8.t))
           (#pt: perm) (#vtag: erased (Seq.seq S8.t))
           (#pa: perm) (#vaad: erased (Seq.seq S8.t))
           (#pk: perm) (#vkey: erased (Seq.seq S8.t))
           (#pn: perm) (#vnon: erased (Seq.seq S8.t))
requires AP.pts_to msg vmsg ** AP.pts_to ct #pc vct ** AP.pts_to tag #pt vtag **
         AP.pts_to aad #pa vaad ** AP.pts_to key #pk vkey **
         AP.pts_to nonce #pn vnon **
         pure (Seq.length vmsg == SZ.v ct_len /\ Seq.length vct == SZ.v ct_len /\
               Seq.length vaad == SZ.v aad_len /\ Seq.length vtag == 16 /\
               Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
               SZ.v ct_len <= C.max_len 1ul)
returns res: bool
ensures exists* (vmsg': Seq.seq S8.t).
  AP.pts_to msg vmsg' ** AP.pts_to ct #pc vct ** AP.pts_to tag #pt vtag **
  AP.pts_to aad #pa vaad ** AP.pts_to key #pk vkey ** AP.pts_to nonce #pn vnon **
  pure (Seq.length vkey == 32 /\ Seq.length vnon == 12 /\
        Seq.length vtag == 16 /\
        Seq.length vct <= C.max_len 1ul /\
        Seq.length vmsg' == Seq.length vct /\
        (res <==> Spec.decrypt_ok vkey vnon vaad vct vtag) /\
        (if res then vmsg' == Spec.decrypted vkey vnon vct else vmsg' == vmsg))
{
  let sm = S.arrayptr_to_slice_intro msg ct_len;
  let sc = S.arrayptr_to_slice_intro ct ct_len;
  let st = S.arrayptr_to_slice_intro tag 16sz;
  let sa = S.arrayptr_to_slice_intro aad aad_len;
  let sk = S.arrayptr_to_slice_intro key 32sz;
  let sn = S.arrayptr_to_slice_intro nonce 12sz;
  let res = Hacl.Chacha20Poly1305.decrypt sm sc st sa sk sn;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sc;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sa;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim sn;
  res
}
