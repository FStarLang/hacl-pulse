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

(** The SHA-2 block function chosen at run time, at the type
    [Hacl.Hash.SHA2.Core.blocks_t].

    The one-shot hash, HMAC and HKDF dispatch once per call, on whole
    specialized copies.  Code that takes the block function as an argument
    -- the streaming hash and HMAC, HMAC-DRBG, HPKE's labeled extract and
    expand -- is given [blocks_dispatch32] or [blocks_dispatch64] instead,
    which checks the CPU (a cached flag) every time it is handed some
    blocks.  That is one predictable branch per call into the hash, against
    hundreds of cycles per block saved. *)
module Hacl.Hash.SHA2.Dispatch

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Loops
open Spec.SHA2
open Hacl.Hash.SHA2.Core
open Spec.SHANI

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Vec = Hacl.Vec128
module V256 = Hacl.Vec256
module NI = Hacl.Hash.SHA2.NI
module AVX2 = Hacl.Hash.SHA2.AVX2

(** [NI.blocks_ni] behind the x86-64 guard, so that the copies it reaches
    exist only where the instructions do. *)
[@@custard_c_closure_prologue "";
  custard_c_closure_guard "defined(__x86_64__)"]
fn blocks_ni_g ([@@@FStar.Attributes.monomorphize] p: params S32.t { is_sha256 p })
               (kt: A.array S32.t) (wsb: A.array S32.t) (st: A.array S32.t) (input: A.array S8.t)
               (nprev: SZ.t) (nfull: SZ.t) (pre: erased (Seq.seq S8.t))
               (#pk: perm) (#vk: erased (Seq.seq S32.t))
               (#vw0: erased (Seq.seq S32.t)) (#vst0: erased (Seq.lseq S32.t 8))
               (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq S32.t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #S32.t /\
               Seq.length pre + Seq.length vin < max_input #S32.t /\
               SZ.v nfull == Seq.length vin / block_len #S32.t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #S32.t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #S32.t /\ Seq.length vw == (rounds p) /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #S32.t (Seq.append pre vin))) (reveal p.iv))
{
  NI.blocks_ni p kt wsb st input nprev nfull pre
}

(** SHA-224/256 blocks: the SHA instructions if the CPU has them. *)
fn blocks_dispatch32 ([@@@FStar.Attributes.monomorphize] p: params S32.t { is_sha256 p })
                     (kt: A.array S32.t) (wsb: A.array S32.t) (st: A.array S32.t) (input: A.array S8.t)
                     (nprev: SZ.t) (nfull: SZ.t) (pre: erased (Seq.seq S8.t))
                     (#pk: perm) (#vk: erased (Seq.seq S32.t))
                     (#vw0: erased (Seq.seq S32.t)) (#vst0: erased (Seq.lseq S32.t 8))
                     (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq S32.t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #S32.t /\
               Seq.length pre + Seq.length vin < max_input #S32.t /\
               SZ.v nfull == Seq.length vin / block_len #S32.t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #S32.t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq S32.t) (vst: Seq.lseq S32.t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #S32.t /\ Seq.length vw == (rounds p) /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #S32.t (Seq.append pre vin))) (reveal p.iv))
{
  if (Hacl.X64.x86_64)
  {
    if (Vec.sha_supported ())
    {
      blocks_ni_g p kt wsb st input nprev nfull pre
    } else {
      blocks_scalar p kt wsb st input nprev nfull pre
    }
  } else {
    blocks_scalar p kt wsb st input nprev nfull pre
  }
}

(** [AVX2.blocks_avx2] behind the x86-64 guard. *)
[@@custard_c_closure_prologue "";
  custard_c_closure_guard "defined(__x86_64__)"]
fn blocks_avx2_g ([@@@FStar.Attributes.monomorphize] p: params S64.t { AVX2.is_sha512 p })
                 (kt: A.array S64.t) (wsb: A.array S64.t) (st: A.array S64.t) (input: A.array S8.t)
                 (nprev: SZ.t) (nfull: SZ.t) (pre: erased (Seq.seq S8.t))
                 (#pk: perm) (#vk: erased (Seq.seq S64.t))
                 (#vw0: erased (Seq.seq S64.t)) (#vst0: erased (Seq.lseq S64.t 8))
                 (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq S64.t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #S64.t /\
               Seq.length pre + Seq.length vin < max_input #S64.t /\
               SZ.v nfull == Seq.length vin / block_len #S64.t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq S64.t) (vst: Seq.lseq S64.t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #S64.t /\ Seq.length vw == (rounds p) /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv))
{
  AVX2.blocks_avx2 p kt wsb st input nprev nfull pre
}

(** SHA-384/512 blocks: the AVX2 message schedule if the CPU has AVX2. *)
fn blocks_dispatch64 ([@@@FStar.Attributes.monomorphize] p: params S64.t { AVX2.is_sha512 p })
                     (kt: A.array S64.t) (wsb: A.array S64.t) (st: A.array S64.t) (input: A.array S8.t)
                     (nprev: SZ.t) (nfull: SZ.t) (pre: erased (Seq.seq S8.t))
                     (#pk: perm) (#vk: erased (Seq.seq S64.t))
                     (#vw0: erased (Seq.seq S64.t)) (#vst0: erased (Seq.lseq S64.t 8))
                     (#pin: perm) (#vin: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to wsb vw0 ** A.pts_to st vst0 ** A.pts_to input #pin vin **
         pure (reveal vk == (reveal p.k <: Seq.seq S64.t) /\ Seq.length vw0 == (rounds p) /\
               Seq.length pre == SZ.v nprev * block_len #S64.t /\
               Seq.length pre + Seq.length vin < max_input #S64.t /\
               SZ.v nfull == Seq.length vin / block_len #S64.t /\
               reveal vst0 == repeati_g (SZ.v nprev)
                                (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv))
ensures exists* (vw: Seq.seq S64.t) (vst: Seq.lseq S64.t 8).
  A.pts_to kt #pk vk ** A.pts_to wsb vw ** A.pts_to st vst ** A.pts_to input #pin vin **
  pure (Seq.length pre + Seq.length vin < max_input #S64.t /\ Seq.length vw == (rounds p) /\
        vst == repeati_g (SZ.v nprev + SZ.v nfull)
                 (update_step p (padded #S64.t (Seq.append pre vin))) (reveal p.iv))
{
  if (Hacl.X64.x86_64)
  {
    if (V256.supported ())
    {
      blocks_avx2_g p kt wsb st input nprev nfull pre
    } else {
      blocks_scalar p kt wsb st input nprev nfull pre
    }
  } else {
    blocks_scalar p kt wsb st input nprev nfull pre
  }
}
