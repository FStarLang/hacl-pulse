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

(** Bit packing.

    Frodo transmits matrices with [d] bits per entry rather than sixteen,
    eight entries at a time so that the packing never straddles a byte
    boundary awkwardly.  [pack] and [unpack] are inverse in the sense the
    specification states; here they are simply each equal to their
    specification, and the bit shuffling that gets there is
    [Hacl.Frodo.Pack]'s business. *)
module Hacl.Frodo.Pack

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module F = Spec.Frodo

(** [out <- pack d len m]: [len] entries of [d] bits each, into
    [d * (len / 8)] bytes. *)
val pack (out: A.array S8.t) (m: A.array S16.t) (d: SZ.t { 0 < SZ.v d /\ SZ.v d <= 16 })
         (len: SZ.t { SZ.v len % 8 == 0 })
         (#p: perm) (#vo: erased (Seq.seq S8.t))
         (#vm: erased (Seq.lseq S16.t (SZ.v len)))
  : stt unit
    (requires A.pts_to out vo ** A.pts_to m #p vm **
              pure (Seq.length vo == SZ.v d * (SZ.v len / 8) /\
                    SZ.v d * SZ.v len < pow2 32))
    (ensures fun _ -> exists* v. A.pts_to out v ** A.pts_to m #p vm **
             pure (v == F.pack (SZ.v d) (SZ.v len) vm))

(** [m <- unpack d len b]: the inverse, [len] entries out of
    [d * (len / 8)] bytes. *)
val unpack (m: A.array S16.t) (b: A.array S8.t) (d: SZ.t { 0 < SZ.v d /\ SZ.v d <= 16 })
           (len: SZ.t { SZ.v len % 8 == 0 })
           (#p: perm) (#vm: erased (Seq.seq S16.t))
           (#vb: erased (Seq.lseq S8.t (SZ.v d * (SZ.v len / 8))))
  : stt unit
    (requires A.pts_to m vm ** A.pts_to b #p vb **
              pure (Seq.length vm == SZ.v len /\ SZ.v d * SZ.v len < pow2 32))
    (ensures fun _ -> exists* v. A.pts_to m v ** A.pts_to b #p vb **
             pure (v == F.unpack (SZ.v d) (SZ.v len) vb))
