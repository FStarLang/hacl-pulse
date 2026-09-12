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

(** The flat C interface to AES-GCM.

      void Hacl_AES_GCM_Ptr_aes128_encrypt(uint8_t *tag, uint8_t *msg,
                                           size_t msg_len, uint8_t *key,
                                           uint8_t *iv, size_t iv_len,
                                           uint8_t *aad, size_t aad_len);
      bool Hacl_AES_GCM_Ptr_aes128_decrypt(uint8_t *msg, size_t msg_len,
                                           uint8_t *tag, uint8_t *key,
                                           uint8_t *iv, size_t iv_len,
                                           uint8_t *aad, size_t aad_len);
      void Hacl_AES_GCM_Ptr_aes256_encrypt(...);
      bool Hacl_AES_GCM_Ptr_aes256_decrypt(...);

    The key is sixteen or thirty-two bytes, the tag is sixteen, and the
    nonce may be any non-empty length -- twelve is the one every protocol
    uses and the only one with a short path.  Encryption is in place:
    [msg] goes in as the plaintext and comes out as the ciphertext.
    Decryption is in place as well, but writes nothing at all unless the
    tag verifies, and returns false when it does not.

    {b A nonce must never repeat under one key.}  Two messages sharing a
    nonce leak the xor of the plaintexts and enough of the hash subkey to
    forge arbitrary messages. *)
module Hacl.AES.GCM.Ptr

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Spec.GCM
open Hacl.AES.GCM

module S = Pulse.Lib.Slice
module AP = Pulse.Lib.ArrayPtr
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

fn aes128_encrypt (tag: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
       (key: AP.ptr S8.t) (iv: AP.ptr S8.t) (iv_len: SZ.t)
       (aad: AP.ptr S8.t) (aad_len: SZ.t)
       (#vt0 #vm0: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires AP.pts_to tag vt0 ** AP.pts_to msg vm0 ** AP.pts_to key #pk vkey **
  AP.pts_to iv #pi viv ** AP.pts_to aad #pa vaad ** pure (
  Seq.length vt0 == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vkey == 16 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
ensures exists* (vt1 vm1: Seq.seq S8.t).
  AP.pts_to tag vt1 ** AP.pts_to msg vm1 ** AP.pts_to key #pk vkey **
  AP.pts_to iv #pi viv ** AP.pts_to aad #pa vaad ** pure (
  Seq.length vt1 == 16 /\ Seq.length vm1 == SZ.v msg_len /\
  Seq.length vkey == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vm1, vals vt1) == gcm_encrypt AES128 (vals vkey) (vals viv)
                                      (vals vaad) (vals vm0))
{
  let st = S.arrayptr_to_slice_intro tag 16sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sk = S.arrayptr_to_slice_intro key 16sz;
  let si = S.arrayptr_to_slice_intro iv iv_len;
  let sa = S.arrayptr_to_slice_intro aad aad_len;
  encrypt params128 sk si sa sm st;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim sa;
}

fn aes128_decrypt (msg: AP.ptr S8.t) (msg_len: SZ.t) (tag: AP.ptr S8.t)
       (key: AP.ptr S8.t) (iv: AP.ptr S8.t) (iv_len: SZ.t)
       (aad: AP.ptr S8.t) (aad_len: SZ.t)
       (#vm0: erased (Seq.seq S8.t))
       (#pt: perm) (#vtag: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires AP.pts_to msg vm0 ** AP.pts_to tag #pt vtag ** AP.pts_to key #pk vkey **
  AP.pts_to iv #pi viv ** AP.pts_to aad #pa vaad ** pure (
  Seq.length vtag == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vkey == 16 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
returns r: bool
ensures exists* (vm1: Seq.seq S8.t).
  AP.pts_to msg vm1 ** AP.pts_to tag #pt vtag ** AP.pts_to key #pk vkey **
  AP.pts_to iv #pi viv ** AP.pts_to aad #pa vaad ** pure (
  Seq.length vm1 == SZ.v msg_len /\
  Seq.length vkey == 16 /\ Seq.length vtag == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt AES128 (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vm1 == Some?.v d) /\
   ((~r) ==> None? d /\ vm1 == reveal vm0)))
{
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let st = S.arrayptr_to_slice_intro tag 16sz;
  let sk = S.arrayptr_to_slice_intro key 16sz;
  let si = S.arrayptr_to_slice_intro iv iv_len;
  let sa = S.arrayptr_to_slice_intro aad aad_len;
  let r = decrypt params128 sk si sa sm st;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim sa;
  r
}

fn aes256_encrypt (tag: AP.ptr S8.t) (msg: AP.ptr S8.t) (msg_len: SZ.t)
       (key: AP.ptr S8.t) (iv: AP.ptr S8.t) (iv_len: SZ.t)
       (aad: AP.ptr S8.t) (aad_len: SZ.t)
       (#vt0 #vm0: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires AP.pts_to tag vt0 ** AP.pts_to msg vm0 ** AP.pts_to key #pk vkey **
  AP.pts_to iv #pi viv ** AP.pts_to aad #pa vaad ** pure (
  Seq.length vt0 == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vkey == 32 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
ensures exists* (vt1 vm1: Seq.seq S8.t).
  AP.pts_to tag vt1 ** AP.pts_to msg vm1 ** AP.pts_to key #pk vkey **
  AP.pts_to iv #pi viv ** AP.pts_to aad #pa vaad ** pure (
  Seq.length vt1 == 16 /\ Seq.length vm1 == SZ.v msg_len /\
  Seq.length vkey == 32 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (vals vm1, vals vt1) == gcm_encrypt AES256 (vals vkey) (vals viv)
                                      (vals vaad) (vals vm0))
{
  let st = S.arrayptr_to_slice_intro tag 16sz;
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let sk = S.arrayptr_to_slice_intro key 32sz;
  let si = S.arrayptr_to_slice_intro iv iv_len;
  let sa = S.arrayptr_to_slice_intro aad aad_len;
  encrypt params256 sk si sa sm st;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim sa;
}

fn aes256_decrypt (msg: AP.ptr S8.t) (msg_len: SZ.t) (tag: AP.ptr S8.t)
       (key: AP.ptr S8.t) (iv: AP.ptr S8.t) (iv_len: SZ.t)
       (aad: AP.ptr S8.t) (aad_len: SZ.t)
       (#vm0: erased (Seq.seq S8.t))
       (#pt: perm) (#vtag: erased (Seq.seq S8.t))
       (#pk: perm) (#vkey: erased (Seq.seq S8.t))
       (#pi: perm) (#viv: erased (Seq.seq S8.t))
       (#pa: perm) (#vaad: erased (Seq.seq S8.t))
requires AP.pts_to msg vm0 ** AP.pts_to tag #pt vtag ** AP.pts_to key #pk vkey **
  AP.pts_to iv #pi viv ** AP.pts_to aad #pa vaad ** pure (
  Seq.length vtag == 16 /\ Seq.length vm0 == SZ.v msg_len /\
  Seq.length vkey == 32 /\ Seq.length viv == SZ.v iv_len /\
  Seq.length vaad == SZ.v aad_len /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  SZ.fits (SZ.v iv_len + 16) /\ SZ.fits (SZ.v aad_len + 16) /\
  SZ.fits (SZ.v msg_len + 16))
returns r: bool
ensures exists* (vm1: Seq.seq S8.t).
  AP.pts_to msg vm1 ** AP.pts_to tag #pt vtag ** AP.pts_to key #pk vkey **
  AP.pts_to iv #pi viv ** AP.pts_to aad #pa vaad ** pure (
  Seq.length vm1 == SZ.v msg_len /\
  Seq.length vkey == 32 /\ Seq.length vtag == 16 /\
  iv_ok (vals viv) /\ aad_ok (vals vaad) /\ msg_ok (vals vm0) /\
  (let d = gcm_decrypt AES256 (vals vkey) (vals viv) (vals vaad)
                       (vals vm0) (vals vtag) in
   (r ==> Some? d /\ vals vm1 == Some?.v d) /\
   ((~r) ==> None? d /\ vm1 == reveal vm0)))
{
  let sm = S.arrayptr_to_slice_intro msg msg_len;
  let st = S.arrayptr_to_slice_intro tag 16sz;
  let sk = S.arrayptr_to_slice_intro key 32sz;
  let si = S.arrayptr_to_slice_intro iv iv_len;
  let sa = S.arrayptr_to_slice_intro aad aad_len;
  let r = decrypt params256 sk si sa sm st;
  S.arrayptr_to_slice_elim sm;
  S.arrayptr_to_slice_elim st;
  S.arrayptr_to_slice_elim sk;
  S.arrayptr_to_slice_elim si;
  S.arrayptr_to_slice_elim sa;
  r
}

#pop-options
