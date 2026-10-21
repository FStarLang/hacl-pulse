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


(** Keys, signatures and the masking vector, as seen by key generation,
    signing and verification.

    Each operation writes or reads one whole encoding, so its caller sees
    the encoding functions of {!Spec.MLDSA.Encode} directly and none of the
    per-field offset arithmetic.  The fixed-size byte fields of a key
    ([rho], [K], [tr]) and of a signature ([c~]) are not copied: the
    encoders take them already in place in the output, and the decoders
    leave them for the caller to read in place. *)
module Hacl.Impl.MLDSA.Pack

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Encode
open Spec.MLDSA.Sample
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Hint

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq

(** [pk <- pkEncode(pk[0..32], t1)]: the first thirty-two bytes, [rho],
    are already in place. *)
val pk_encode_impl (p: erased params) (pk: A.array S8.t) (t1: A.array zqt)
                   ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   (#vp: erased (Seq.seq S8.t)) (#pt: perm) (#vt: erased (Seq.seq zqt))
  : stt unit
      (A.pts_to pk vp ** A.pts_to t1 #pt vt **
       pure (SZ.v k == p.k /\ Seq.length vp == pk_len p /\ Seq.length vt == p.k * n))
      (fun _ -> exists* (v: Seq.seq S8.t). A.pts_to pk v ** A.pts_to t1 #pt vt **
        pure (Seq.length vp == pk_len p /\ Seq.length vt == p.k * n /\
              v == pk_encode p (Seq.slice vp 0 32) (as_ints vt)))

(** [t1] of [pkDecode(pk)]; [rho] is [pk[0..32]]. *)
val pk_decode_impl (p: erased params) (t1: A.array zqt) (pk: A.array S8.t)
                   ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   (#vt: erased (Seq.seq zqt)) (#pp: perm) (#vp: erased (Seq.seq S8.t))
  : stt unit
      (A.pts_to t1 vt ** A.pts_to pk #pp vp **
       pure (SZ.v k == p.k /\ Seq.length vp == pk_len p /\ Seq.length vt == p.k * n))
      (fun _ -> exists* (v: Seq.seq zqt). A.pts_to t1 v ** A.pts_to pk #pp vp **
        pure (Seq.length vp == pk_len p /\ Seq.length v == p.k * n /\
              as_ints v == snd (pk_decode p vp) /\
              (forall (i: nat). i < p.k * n ==> S32.v (Seq.index v i) < 1024)))

(** [sk <- skEncode(rho, K, tr, s1, s2, t0)]: the first 128 bytes ([rho],
    [K], [tr]) are already in place. *)
val sk_encode_impl (p: erased params) (sk: A.array S8.t) (s1 s2 t0: A.array zqt)
                   ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                   (#vk: erased (Seq.seq S8.t)) (#p1 #p2 #p0: perm)
                   (#v1 #v2 #v0: erased (Seq.seq zqt))
  : stt unit
      (A.pts_to sk vk ** A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 ** A.pts_to t0 #p0 v0 **
       pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
             Seq.length vk == sk_len p /\ Seq.length v1 == p.l * n /\
             Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n))
      (fun _ -> exists* (v: Seq.seq S8.t).
        A.pts_to sk v ** A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 ** A.pts_to t0 #p0 v0 **
        pure (Seq.length vk == sk_len p /\ Seq.length v1 == p.l * n /\
              Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
              v == sk_encode p (Seq.slice vk 0 32) (Seq.slice vk 32 64) (Seq.slice vk 64 128)
                             (as_zqs v1) (as_zqs v2) (as_zqs v0)))

(** [s1], [s2] and [t0] of [skDecode(sk)]; [rho], [K] and [tr] are
    [sk[0..32]], [sk[32..64]] and [sk[64..128]]. *)
val sk_decode_impl (p: erased params) (s1 s2 t0: A.array zqt) (sk: A.array S8.t)
                   ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                   (#v1 #v2 #v0: erased (Seq.seq zqt)) (#pk: perm) (#vk: erased (Seq.seq S8.t))
  : stt unit
      (A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to t0 v0 ** A.pts_to sk #pk vk **
       pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
             Seq.length vk == sk_len p /\ Seq.length v1 == p.l * n /\
             Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n))
      (fun _ -> exists* (w1 w2 w0: Seq.seq zqt).
        A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to t0 w0 ** A.pts_to sk #pk vk **
        pure (Seq.length vk == sk_len p /\ Seq.length w1 == p.l * n /\
              Seq.length w2 == p.k * n /\ Seq.length w0 == p.k * n /\
              as_zqs w1 == (sk_decode p vk).sk_s1 /\
              as_zqs w2 == (sk_decode p vk).sk_s2 /\
              as_zqs w0 == (sk_decode p vk).sk_t0))

(** [sg <- sigEncode(c~, z, h)]: the first [ct_len] bytes, [c~], are
    already in place. *)
val sig_encode_impl (p: erased params) (sg: A.array S8.t) (z: A.array zqt) (h: A.array S32.t)
                    ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                    (#vs: erased (Seq.seq S8.t)) (#pz #ph: perm)
                    (#vz: erased (Seq.seq zqt)) (#vh: erased (Seq.seq S32.t))
  : stt unit
      (A.pts_to sg vs ** A.pts_to z #pz vz ** A.pts_to h #ph vh **
       pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v ctl == ct_len p /\
             SZ.v g1bits == p.gamma1_bits /\ SZ.v omega == p.omega /\
             Seq.length vs == sig_len p /\ Seq.length vz == p.l * n /\
             Seq.length vh == p.k * n))
      (fun _ -> exists* (v: Seq.seq S8.t).
        A.pts_to sg v ** A.pts_to z #pz vz ** A.pts_to h #ph vh **
        pure (Seq.length vs == sig_len p /\ Seq.length vz == p.l * n /\
              Seq.length vh == p.k * n /\
              v == sig_encode p (Seq.slice vs 0 (ct_len p)) (as_zqs vz) (hint_view vh)))

(** [z] and [h] of [sigDecode(sg)]; [c~] is [sg[0..ct_len]].  The result
    is [false] exactly when the hint does not decode. *)
val sig_decode_impl (p: erased params) (z: A.array zqt) (h: A.array S32.t) (sg: A.array S8.t)
                    ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                    (#vz: erased (Seq.seq zqt)) (#vh: erased (Seq.seq S32.t))
                    (#ps: perm) (#vs: erased (Seq.seq S8.t))
  : stt bool
      (A.pts_to z vz ** A.pts_to h vh ** A.pts_to sg #ps vs **
       pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v ctl == ct_len p /\
             SZ.v g1bits == p.gamma1_bits /\ SZ.v omega == p.omega /\
             Seq.length vs == sig_len p /\ Seq.length vz == p.l * n /\
             Seq.length vh == p.k * n))
      (fun ok -> exists* (wz: Seq.seq zqt) (wh: Seq.seq S32.t).
        A.pts_to z wz ** A.pts_to h wh ** A.pts_to sg #ps vs **
        pure (Seq.length vs == sig_len p /\ Seq.length wz == p.l * n /\
              Seq.length wh == p.k * n /\ hint_bits wh /\
              (let (_, zs, ho) = sig_decode p vs in
               as_zqs wz == zs /\
               ho == (if ok then Some (hint_view wh) else None))))

(** [out <- w1Encode(w1)]. *)
val w1_encode_impl (p: erased params) (out: A.array S8.t) (w1: A.array zqt)
                   ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   (gd: U32.t)
                   (#vo: erased (Seq.seq S8.t)) (#pw: perm) (#vw: erased (Seq.seq zqt))
  : stt unit
      (A.pts_to out vo ** A.pts_to w1 #pw vw **
       pure (SZ.v k == p.k /\ U32.v gd == p.gamma2_div /\
             Seq.length vo == p.k * (32 * w1_bits p) /\ Seq.length vw == p.k * n))
      (fun _ -> exists* (v: Seq.seq S8.t). A.pts_to out v ** A.pts_to w1 #pw vw **
        pure (Seq.length vw == p.k * n /\ v == w1_encode p (as_ints vw)))

