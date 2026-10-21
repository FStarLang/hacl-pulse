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


(** The message representative [mu = H(tr || M', 64)], absorbed
    incrementally so that the message is never copied.  For the pure
    variant [M' = 0 || |ctx| || ctx || M] (Algorithms 2 and 3). *)
module Hacl.Impl.MLDSA.Mu

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.SHA3.Streaming
open Hacl.Hash.SHA3.Streaming
open Hacl.Streaming.SHA3

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Seq = FStar.Seq
module M = Spec.MLDSA
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let hdr_eq (v: Seq.seq S8.t) (ctx msg: Seq.seq S8.t)
  : Lemma (requires Seq.length v == 2 /\ Seq.length ctx < 256 /\
                    S8.v (Seq.index v 0) == 0 /\ S8.v (Seq.index v 1) == Seq.length ctx)
          (ensures M.format_msg msg ctx == Seq.append v (Seq.append ctx msg))
  = let f = M.format_msg msg ctx in
    let r = Seq.append v (Seq.append ctx msg) in
    assert (Seq.length f == Seq.length r);
    S8.v_extensional (Seq.index v 0) (Seq.index f 0);
    S8.v_extensional (Seq.index v 1) (Seq.index f 1);
    Seq.lemma_eq_intro f r

let fmt_eq (tr hd ctx msg: Seq.seq S8.t)
  : Lemma (Seq.append (Seq.append (Seq.append tr hd) ctx) msg ==
           Seq.append tr (Seq.append hd (Seq.append ctx msg)))
  = Seq.append_assoc tr hd ctx;
    Seq.append_assoc (Seq.append tr hd) ctx msg;
    Seq.append_assoc hd ctx msg;
    Seq.append_assoc tr hd (Seq.append ctx msg)

(** [mu <- H(tr || msg, 64)]. *)
fn mu_impl (mu tr msg: A.array S8.t) (msg_len: SZ.t)
           (#vm0: erased (Seq.seq S8.t)) (#pt #pm: perm) (#vt #vm: erased (Seq.seq S8.t))
requires A.pts_to mu vm0 ** A.pts_to tr #pt vt ** A.pts_to msg #pm vm **
         pure (Seq.length vm0 == 64 /\ Seq.length vt == 64 /\ SZ.v msg_len == Seq.length vm /\
               SZ.fits (64 + Seq.length vm))
ensures exists* (v: Seq.seq S8.t).
  A.pts_to mu v ** A.pts_to tr #pt vt ** A.pts_to msg #pm vm **
  pure (Seq.length v == 64 /\ v == M.message_rep vt vm)
{
  let mut st = [| (S64.zero <: S64.t); 25sz |];
  Mem.track st;
  let mut buf = [| (S8.zero <: S8.t); 136sz |];
  Mem.track buf;
  let mut tot = [| 0sz; 1sz |];
  Mem.track tot;
  shake256_init st buf tot;
  shake256_update st buf tot tr 64sz (Seq.empty #S8.t);
  Seq.append_empty_l vt;
  shake256_update st buf tot msg msg_len vt;
  shake256_digest st buf tot mu 64sz (Seq.append vt vm);
  Mem.wipe tot 1sz;
  Mem.wipe buf 136sz;
  Mem.wipe st 25sz;
  ()
}

(** [mu <- H(tr || 0 || |ctx| || ctx || msg, 64)]. *)
fn mu_ctx_impl (mu tr msg: A.array S8.t) (msg_len: SZ.t) (ctx: A.array S8.t) (ctx_len: SZ.t)
               (#vm0: erased (Seq.seq S8.t)) (#pt #pm #pc: perm)
               (#vt #vm #vc: erased (Seq.seq S8.t))
requires A.pts_to mu vm0 ** A.pts_to tr #pt vt ** A.pts_to msg #pm vm ** A.pts_to ctx #pc vc **
         pure (Seq.length vm0 == 64 /\ Seq.length vt == 64 /\ SZ.v msg_len == Seq.length vm /\
               SZ.v ctx_len == Seq.length vc /\ Seq.length vc < 256 /\
               SZ.fits (66 + Seq.length vc + Seq.length vm))
ensures exists* (v: Seq.seq S8.t).
  A.pts_to mu v ** A.pts_to tr #pt vt ** A.pts_to msg #pm vm ** A.pts_to ctx #pc vc **
  pure (Seq.length v == 64 /\ Seq.length vc < 256 /\
        v == M.message_rep vt (M.format_msg vm vc))
{
  let mut st = [| (S64.zero <: S64.t); 25sz |];
  Mem.track st;
  let mut buf = [| (S8.zero <: S8.t); 136sz |];
  Mem.track buf;
  let mut tot = [| 0sz; 1sz |];
  Mem.track tot;
  let mut hd = [| (S8.zero <: S8.t); 2sz |];
  Mem.track hd;
  A.(hd.(1sz) <- S8.classify (FStar.Int.Cast.uint32_to_uint8 (SZ.sizet_to_uint32 ctx_len)));
  with vh. assert (A.pts_to hd vh);
  FStar.Math.Lemmas.small_mod (SZ.v ctx_len) 256;
  hdr_eq vh vc vm;
  shake256_init st buf tot;
  shake256_update st buf tot tr 64sz (Seq.empty #S8.t);
  Seq.append_empty_l vt;
  shake256_update st buf tot hd 2sz vt;
  shake256_update st buf tot ctx ctx_len (Seq.append vt vh);
  shake256_update st buf tot msg msg_len (Seq.append (Seq.append vt vh) vc);
  shake256_digest st buf tot mu 64sz (Seq.append (Seq.append (Seq.append vt vh) vc) vm);
  fmt_eq vt vh vc vm;
  Mem.wipe hd 2sz;
  Mem.wipe tot 1sz;
  Mem.wipe buf 136sz;
  Mem.wipe st 25sz;
  ()
}

#pop-options
