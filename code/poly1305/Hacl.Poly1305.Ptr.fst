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

(** The flat C interface to Poly1305.

      void Hacl_Poly1305_Ptr_mac(uint8_t *tag,
                                 uint8_t *msg, size_t msg_len,
                                 uint8_t *key);

    [tag] is sixteen bytes and [key] is thirty-two; the message may be any
    length, including zero.  The key is a one-time key: using it for two
    different messages destroys the security of both. *)
module Hacl.Poly1305.Ptr

#lang-pulse

open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Spec = Spec.Poly1305

fn mac (tag: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t) (key: AP.ptr S8.t)
       (#vtag: erased (Seq.seq S8.t))
       (#pm: perm) (#vmsg: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
requires AP.pts_to tag vtag ** AP.pts_to msg #pm vmsg ** AP.pts_to key #pk vkey **
         pure (Seq.length vtag == 16 /\ Seq.length vmsg == SZ.v msg_len /\
               Seq.length vkey == 32)
ensures exists* (vtag': Seq.seq S8.t).
  AP.pts_to tag vtag' ** AP.pts_to msg #pm vmsg ** AP.pts_to key #pk vkey **
  pure (Seq.length vkey == 32 /\ Seq.length vtag' == 16 /\
        vtag' == Spec.poly1305 vmsg vkey)
{
  let st = S.arrayptr_to_slice_intro tag 16sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sk = S.arrayptr_to_slice_intro key 32sz;
  Hacl.Poly1305.poly1305_mac st sm sk;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
}
