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


(** The polynomial coders, as seen by their callers.

    {!Hacl.Impl.MLKEM.Encode} carries the bit-level loops and all their
    reasoning with it, and every definition in it lands in the solver's
    context of any module that opens it.  K-PKE needs four operations out
    of it -- the message is one polynomial at one bit, the second
    ciphertext component one polynomial at [dv] -- so it goes through this
    interface instead.  See {!Hacl.Impl.MLKEM.Poly} for the same argument
    about the transform. *)
module Hacl.Impl.MLKEM.Codec

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM.Zq
open Spec.MLKEM.Encode
open Hacl.Impl.MLKEM.Zq

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module Seq = FStar.Seq

(** [ByteEncode_d] on one polynomial. *)
val encode_poly (out: A.array S8.t) (f: A.array zqt) ([@@@FStar.Attributes.monomorphize] d: SZ.t)
                (#vo: erased (Seq.seq S8.t)) (#p: perm) (#vf: erased (Seq.seq zqt))
  : stt unit
    (requires A.pts_to out vo ** A.pts_to f #p vf **
              pure (1 <= SZ.v d /\ SZ.v d <= 12 /\
                    Seq.length vf == n /\ Seq.length vo == 32 * SZ.v d))
    (ensures fun _ -> exists* (v: Seq.seq S8.t).
       A.pts_to out v ** A.pts_to f #p vf **
       pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length vf == n /\
             Seq.length v == 32 * SZ.v d /\ v == byte_encode (SZ.v d) (as_nats vf)))

(** [ByteDecode_d] on one polynomial. *)
val decode_poly (dst: A.array zqt) (b: A.array S8.t) ([@@@FStar.Attributes.monomorphize] d: SZ.t)
                (#vd: erased (Seq.seq zqt)) (#p: perm) (#vb: erased (Seq.seq S8.t))
  : stt unit
    (requires A.pts_to dst vd ** A.pts_to b #p vb **
              pure (1 <= SZ.v d /\ SZ.v d <= 12 /\
                    Seq.length vd == n /\ Seq.length vb == 32 * SZ.v d))
    (ensures fun _ -> exists* (v: Seq.seq zqt).
       A.pts_to dst v ** A.pts_to b #p vb **
       pure (1 <= SZ.v d /\ SZ.v d <= 12 /\ Seq.length v == n /\
             Seq.length vb == 32 * SZ.v d /\ as_poly v == byte_decode (SZ.v d) vb))

(** [Compress_d] on one polynomial. *)
val compress_poly (dst src: A.array zqt) ([@@@FStar.Attributes.monomorphize] d: SZ.t)
                  (#p: perm) (#vd #vs: erased (Seq.seq zqt))
  : stt unit
    (requires A.pts_to dst vd ** A.pts_to src #p vs **
              pure (1 <= SZ.v d /\ SZ.v d <= 11 /\
                    Seq.length vd == n /\ Seq.length vs == n))
    (ensures fun _ -> exists* (v: Seq.seq zqt).
       A.pts_to dst v ** A.pts_to src #p vs **
       pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ Seq.length v == n /\ Seq.length vs == n /\
             as_nats v == poly_compress (SZ.v d) (as_poly vs)))

(** [Decompress_d] on one polynomial.  The guard is what the decoder's
    bound establishes. *)
val decompress_poly (dst src: A.array zqt) ([@@@FStar.Attributes.monomorphize] d: SZ.t)
                    (#p: perm) (#vd #vs: erased (Seq.seq zqt))
  : stt unit
    (requires A.pts_to dst vd ** A.pts_to src #p vs **
              pure (1 <= SZ.v d /\ SZ.v d <= 11 /\
                    Seq.length vd == n /\ Seq.length vs == n /\
                    (forall (t: nat). t < n ==> S16.v (Seq.index vs t) < pow2 (SZ.v d))))
    (ensures fun _ -> exists* (v: Seq.seq zqt).
       A.pts_to dst v ** A.pts_to src #p vs **
       pure (1 <= SZ.v d /\ SZ.v d <= 11 /\ Seq.length v == n /\ Seq.length vs == n /\
             as_poly v == poly_decompress (SZ.v d) (as_nats vs)))
