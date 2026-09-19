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

(** HPKE's KEM: encapsulation and decapsulation.

    Each of these runs a Diffie-Hellman over the suite's curve and feeds the
    shared secret and the two public keys through the labeled KDF.  The
    scratch buffers, the serialisation and the key-schedule context are all
    internal. *)
module Hacl.HPKE.KEM

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.SHA2.Constants
open Spec.HPKE
open Hacl.Hash.SHA2.Tables
open Hacl.HPKE.Tables
open Hacl.HPKE.Labeled
open Hacl.Impl.Copy
open Hacl.Impl.Table

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module C = Hacl.Curve25519
module PE = Hacl.P256.Ecdh
module PS = Hacl.P256.Sec1
module B = Hacl.Spec.Bytes

val encap_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
              (shared: A.array S8.t) (enc: A.array S8.t)
              (skE: A.array S8.t) (pkR: A.array S8.t)
              (#vsh: erased (Seq.seq S8.t)) (#ve: erased (Seq.seq S8.t))
              (#pe: perm) (#vskE: erased (Seq.seq S8.t))
              (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
  : stt bool
    (requires A.pts_to shared vsh ** A.pts_to enc ve **
             A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
             pure (Seq.length vsh == 32 /\ Seq.length ve == size_dh_public k /\
                   Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public k))
    (ensures fun r -> exists* wsh we.
      A.pts_to shared wsh ** A.pts_to enc we **
      A.pts_to skE #pe vskE ** A.pts_to pkR #pr vpkR **
      pure (Seq.length wsh == 32 /\ Seq.length we == size_dh_public k /\
            Seq.length vskE == 32 /\ Seq.length vpkR == size_dh_public k /\
            r == Some? (encap k vskE vpkR) /\
            (r ==> (wsh, we) == Some?.v (encap k vskE vpkR))))

val decap_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
              (shared: A.array S8.t) (enc: A.array S8.t) (skR: A.array S8.t)
              (#vsh: erased (Seq.seq S8.t))
              (#pn: perm) (#ve: erased (Seq.seq S8.t))
              (#pr: perm) (#vskR: erased (Seq.seq S8.t))
  : stt bool
    (requires A.pts_to shared vsh ** A.pts_to enc #pn ve ** A.pts_to skR #pr vskR **
             pure (Seq.length vsh == 32 /\ Seq.length ve == size_dh_public k /\
                   Seq.length vskR == 32))
    (ensures fun r -> exists* wsh.
      A.pts_to shared wsh ** A.pts_to enc #pn ve ** A.pts_to skR #pr vskR **
      pure (Seq.length wsh == 32 /\ Seq.length ve == size_dh_public k /\
            Seq.length vskR == 32 /\
            r == Some? (decap k ve vskR) /\
            (r ==> wsh == Some?.v (decap k ve vskR))))

val auth_encap_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
                   (shared: A.array S8.t) (enc: A.array S8.t)
                   (skE: A.array S8.t) (skS: A.array S8.t) (pkR: A.array S8.t)
                   (#vsh: erased (Seq.seq S8.t)) (#ve: erased (Seq.seq S8.t))
                   (#pe: perm) (#vskE: erased (Seq.seq S8.t))
                   (#pss: perm) (#vskS: erased (Seq.seq S8.t))
                   (#pr: perm) (#vpkR: erased (Seq.seq S8.t))
  : stt bool
    (requires A.pts_to shared vsh ** A.pts_to enc ve **
             A.pts_to skE #pe vskE ** A.pts_to skS #pss vskS ** A.pts_to pkR #pr vpkR **
             pure (Seq.length vsh == 32 /\ Seq.length ve == size_dh_public k /\
                   Seq.length vskE == 32 /\ Seq.length vskS == 32 /\
                   Seq.length vpkR == size_dh_public k))
    (ensures fun r -> exists* wsh we.
      A.pts_to shared wsh ** A.pts_to enc we **
      A.pts_to skE #pe vskE ** A.pts_to skS #pss vskS ** A.pts_to pkR #pr vpkR **
      pure (Seq.length wsh == 32 /\ Seq.length we == size_dh_public k /\
            Seq.length vskE == 32 /\ Seq.length vskS == 32 /\
            Seq.length vpkR == size_dh_public k /\
            r == Some? (auth_encap k vskE vskS vpkR) /\
            (r ==> (wsh, we) == Some?.v (auth_encap k vskE vskS vpkR))))

val auth_decap_impl ([@@@FStar.Attributes.monomorphize] k: kem_alg)
                   (shared: A.array S8.t) (enc: A.array S8.t)
                   (skR: A.array S8.t) (pkS: A.array S8.t)
                   (#vsh: erased (Seq.seq S8.t))
                   (#pn: perm) (#ve: erased (Seq.seq S8.t))
                   (#pr: perm) (#vskR: erased (Seq.seq S8.t))
                   (#pS: perm) (#vpkS: erased (Seq.seq S8.t))
  : stt bool
    (requires A.pts_to shared vsh ** A.pts_to enc #pn ve **
             A.pts_to skR #pr vskR ** A.pts_to pkS #pS vpkS **
             pure (Seq.length vsh == 32 /\ Seq.length ve == size_dh_public k /\
                   Seq.length vskR == 32 /\ Seq.length vpkS == size_dh_public k))
    (ensures fun r -> exists* wsh.
      A.pts_to shared wsh ** A.pts_to enc #pn ve **
      A.pts_to skR #pr vskR ** A.pts_to pkS #pS vpkS **
      pure (Seq.length wsh == 32 /\ Seq.length ve == size_dh_public k /\
            Seq.length vskR == 32 /\ Seq.length vpkS == size_dh_public k /\
            r == Some? (auth_decap k ve vskR vpkS) /\
            (r ==> wsh == Some?.v (auth_decap k ve vskR vpkS))))

