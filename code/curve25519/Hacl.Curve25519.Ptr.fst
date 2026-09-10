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

(** The flat C interface to X25519.

      void Hacl_Curve25519_Ptr_scalarmult(uint8_t *out,
                                          uint8_t *scalar, uint8_t *point);
      void Hacl_Curve25519_Ptr_secret_to_public(uint8_t *out, uint8_t *priv);
      bool Hacl_Curve25519_Ptr_ecdh(uint8_t *out,
                                    uint8_t *priv, uint8_t *pub);

    Every buffer is thirty-two bytes.  [scalarmult] is RFC 7748's X25519
    exactly, clamping included, and accepts any input point, including a
    non-canonical encoding and one of small order.  [ecdh] is [scalarmult]
    plus the one check a key agreement owes its caller: it returns [false],
    and the output must not be used, when the shared secret is zero. *)
module Hacl.Curve25519.Ptr

#lang-pulse

open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Spec = Spec.Curve25519

fn scalarmult (out: AP.ptr S8.t) (scalar: AP.ptr S8.t) (point: AP.ptr S8.t)
              (#vout: erased (Seq.seq S8.t))
              (#pk: perm) (#vk: erased (Seq.seq S8.t))
              (#pu: perm) (#vu: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to scalar #pk vk ** AP.pts_to point #pu vu **
  pure (Seq.length vout == 32 /\ Seq.length vk == 32 /\ Seq.length vu == 32)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to scalar #pk vk ** AP.pts_to point #pu vu **
  pure (Seq.length vk == 32 /\ Seq.length vu == 32 /\
        vout' == Spec.scalarmult vk vu)
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let sk = S.arrayptr_to_slice_intro scalar 32sz;
  let su = S.arrayptr_to_slice_intro point 32sz;
  Hacl.Curve25519.scalarmult so sk su;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim su;
}

fn secret_to_public (out: AP.ptr S8.t) (priv: AP.ptr S8.t)
                    (#vout: erased (Seq.seq S8.t))
                    (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to priv #pk vk **
  pure (Seq.length vout == 32 /\ Seq.length vk == 32)
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to priv #pk vk **
  pure (Seq.length vk == 32 /\ vout' == Spec.secret_to_public vk)
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let sk = S.arrayptr_to_slice_intro priv 32sz;
  Hacl.Curve25519.secret_to_public so sk;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sk;
}

fn ecdh (out: AP.ptr S8.t) (priv: AP.ptr S8.t) (pub: AP.ptr S8.t)
        (#vout: erased (Seq.seq S8.t))
        (#pk: perm) (#vk: erased (Seq.seq S8.t))
        (#pu: perm) (#vu: erased (Seq.seq S8.t))
requires AP.pts_to out vout ** AP.pts_to priv #pk vk ** AP.pts_to pub #pu vu **
  pure (Seq.length vout == 32 /\ Seq.length vk == 32 /\ Seq.length vu == 32)
returns ok: bool
ensures exists* (vout': Seq.seq S8.t).
  AP.pts_to out vout' ** AP.pts_to priv #pk vk ** AP.pts_to pub #pu vu **
  pure (Seq.length vk == 32 /\ Seq.length vu == 32 /\
        vout' == fst (Spec.ecdh vk vu) /\ ok == snd (Spec.ecdh vk vu))
{
  let so = S.arrayptr_to_slice_intro out 32sz;
  let sk = S.arrayptr_to_slice_intro priv 32sz;
  let su = S.arrayptr_to_slice_intro pub 32sz;
  let ok = Hacl.Curve25519.ecdh so sk su;
  S.arrayptr_to_slice_elim so;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim su;
  ok
}
