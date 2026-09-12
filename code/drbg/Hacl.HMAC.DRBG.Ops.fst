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

(** Instantiate, reseed and generate: SP 800-90A 10.1.2.3 to 10.1.2.5.

    The state is three caller-owned buffers, [k] and [v] of one digest each
    and a one-element [ctr].  [update] takes its data in three pieces, so
    [reseed] and [generate], which have fewer, pass zero-length slices;
    those extract to a one-byte local that is never read. *)
module Hacl.HMAC.DRBG.Ops

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HMAC
open Spec.HMAC_DRBG
open Hacl.Impl.Copy
open Hacl.SizeT
open Hacl.HMAC.DRBG.Core
open Hacl.HMAC.DRBG.Gen

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8

(** The counter is one machine word, so that the state is three pointers and
    nothing else. *)
let ctr_val (vctr: Seq.seq SZ.t) : nat =
  if Seq.length vctr = 0 then 0 else SZ.v (Seq.index vctr 0)

unfold let ctr_ok (vctr: Seq.seq SZ.t) (c: nat) : prop =
  Seq.length vctr == 1 /\ ctr_val vctr == c

(** {2 Instantiation, 10.1.2.3} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn instantiate (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
               (kt: A.array t) (ivt: A.array t)
               (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
               (entropy: A.array S8.t) (elen: SZ.t) (nonce: A.array S8.t) (nlen: SZ.t)
               (personal: A.array S8.t) (plen: SZ.t)
               (#pk: perm) (#vk: erased (Seq.seq t))
               (#pi: perm) (#vi: erased (Seq.seq t))
               (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
               (#vctr: erased (Seq.seq SZ.t))
               (#p1: perm) (#ve: erased (Seq.seq S8.t))
               (#p2: perm) (#vn: erased (Seq.seq S8.t))
               (#p3: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to entropy #p1 ve ** A.pts_to nonce #p2 vn ** A.pts_to personal #p3 vp **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vval == (hash_bytes p) /\
               Seq.length vctr == 1 /\
               data_ok p (seed_material ve vn vp) /\
               SZ.fits (block_len #t + (hash_bytes p) + 1 + Seq.length (seed_material ve vn vp)))
         ** pure (SZ.v elen == Seq.length ve /\ SZ.v nlen == Seq.length vn /\
                  SZ.v plen == Seq.length vp)
ensures exists* vkey' vval' vctr'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to entropy #p1 ve ** A.pts_to nonce #p2 vn ** A.pts_to personal #p3 vp **
  pure ((vkey', vval') == upd p (initial p).k (initial p).v (seed_material ve vn vp) /\
        ctr_ok vctr' 1)
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len entropy; A.pts_to_len nonce; A.pts_to_len personal;
  let hb = p.nhash_bytes;
  fill k (S8.classify 0x00uy) hb;
  fill v (S8.classify 0x01uy) hb;
  A.((ctr.(0sz) <- 1sz));
  Hacl.HMAC.DRBG.Core.update p kt ivt k v entropy elen nonce nlen personal plen;
}

#pop-options

(** {2 Reseeding, 10.1.2.4} *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn reseed (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
          (kt: A.array t) (ivt: A.array t)
          (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
          (entropy: A.array S8.t) (elen: SZ.t) (additional: A.array S8.t) (alen: SZ.t)
          (#pk: perm) (#vk: erased (Seq.seq t))
          (#pi: perm) (#vi: erased (Seq.seq t))
          (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
          (#vctr: erased (Seq.seq SZ.t))
          (#p1: perm) (#ve: erased (Seq.seq S8.t))
          (#p2: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to entropy #p1 ve ** A.pts_to additional #p2 va **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vval == (hash_bytes p) /\
               Seq.length vctr == 1 /\
               data_ok p (Seq.append ve va) /\
               SZ.fits (block_len #t + (hash_bytes p) + 1 + Seq.length ve + Seq.length va))
         ** pure (SZ.v elen == Seq.length ve /\ SZ.v alen == Seq.length va)
ensures exists* vkey' vval' vctr'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to entropy #p1 ve ** A.pts_to additional #p2 va **
  pure ((vkey', vval') == upd p vkey vval (Seq.append ve va) /\ ctr_ok vctr' 1)
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len entropy; A.pts_to_len additional;
  let mut earr = [| (S8.classify 0uy <: S8.t); 0sz |]; A.pts_to_len earr;
  A.pts_to_len earr;
  with vempty. assert (A.pts_to earr vempty);
  assert (pure (Seq.equal (dcat ve va vempty) (Seq.append ve va)));
  Hacl.HMAC.DRBG.Core.update p kt ivt k v entropy elen additional alen earr 0sz;
  A.((ctr.(0sz) <- 1sz));
  ()
}

#pop-options

(** {2 Generation, 10.1.2.5} *)

(** Step 2: an update only if there is additional input. *)

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

fn maybe_update (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
                (kt: A.array t) (ivt: A.array t)
                (k: A.array S8.t) (v: A.array S8.t)
                (additional: A.array S8.t) (n: SZ.t) (e1: A.array S8.t) (e2: A.array S8.t)
                (#pk: perm) (#vk: erased (Seq.seq t))
                (#pi: perm) (#vi: erased (Seq.seq t))
                (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
                (#p1: perm) (#va: erased (Seq.seq S8.t))
                (#p2: perm) (#v1: erased (Seq.seq S8.t))
                (#p3: perm) (#v2: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to k vkey ** A.pts_to v vval **
         A.pts_to additional #p1 va ** A.pts_to e1 #p2 v1 ** A.pts_to e2 #p3 v2 **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vval == (hash_bytes p) /\
               Seq.length v1 == 0 /\ Seq.length v2 == 0 /\
               data_ok p va /\
               SZ.fits (block_len #t + (hash_bytes p) + 1 + Seq.length va))
         ** pure (SZ.v n == Seq.length va)
ensures exists* vkey' vval'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to k vkey' ** A.pts_to v vval' **
  A.pts_to additional #p1 va ** A.pts_to e1 #p2 v1 ** A.pts_to e2 #p3 v2 **
  pure ((vkey', vval') ==
          (if Seq.length va = 0 then (reveal vkey, reveal vval) else upd p vkey vval va))
{
  A.pts_to_len k; A.pts_to_len v;
  A.pts_to_len additional; A.pts_to_len e1; A.pts_to_len e2;
  assert (pure (Seq.equal (dcat va v1 v2) va));
  if (SZ.gt n 0sz) {
    Hacl.HMAC.DRBG.Core.update p kt ivt k v additional n e1 0sz e2 0sz;
  } else {
    ()
  }
}

#pop-options

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

fn generate (#t: Type0) {| w: word t |} ([@@@FStar.Attributes.monomorphize] p: params t)
            (kt: A.array t) (ivt: A.array t)
            (k: A.array S8.t) (v: A.array S8.t) (ctr: A.array SZ.t)
            (out: A.array S8.t) (n: SZ.t) (additional: A.array S8.t) (alen: SZ.t)
            (#pk: perm) (#vk: erased (Seq.seq t))
            (#pi: perm) (#vi: erased (Seq.seq t))
            (#vkey: erased (Seq.seq S8.t)) (#vval: erased (Seq.seq S8.t))
            (#vctr: erased (Seq.seq SZ.t)) (#vout: erased (Seq.seq S8.t))
            (#p1: perm) (#va: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to k vkey ** A.pts_to v vval ** A.pts_to ctr vctr **
         A.pts_to out vout ** A.pts_to additional #p1 va **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vval == (hash_bytes p) /\
               Seq.length vctr == 1 /\
               data_ok p va /\
               SZ.fits (block_len #t + (hash_bytes p) + 1 + Seq.length va))
         ** pure (SZ.v n == Seq.length vout)
         ** pure (SZ.v alen == Seq.length va)
returns ok: bool
ensures exists* vkey' vval' vctr' vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to k vkey' ** A.pts_to v vval' ** A.pts_to ctr vctr' **
  A.pts_to out vout' ** A.pts_to additional #p1 va **
  pure (Seq.length vctr' == 1 /\
        (if ok
         then gene p vkey vval (ctr_val vctr) (Seq.length vout) va ==
                Some (vout', reveal vkey', reveal vval', ctr_val vctr')
         else gene p vkey vval (ctr_val vctr) (Seq.length vout) va == None /\
              vkey' == reveal vkey /\ vval' == reveal vval /\
              vctr' == reveal vctr /\ vout' == reveal vout))
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len ctr;
  A.pts_to_len out; A.pts_to_len additional;
  let c = A.(ctr.(0sz));
  if (SZ.gt c 1024sz || SZ.gt n (big max_output_length)) {
    false
  } else {
    let mut e1a = [| (S8.classify 0uy <: S8.t); 0sz |]; A.pts_to_len e1a;
    A.pts_to_len e1a;
    let mut e2a = [| (S8.classify 0uy <: S8.t); 0sz |]; A.pts_to_len e2a;
    A.pts_to_len e2a;
    with ve1. assert (A.pts_to e1a ve1);
    with ve2. assert (A.pts_to e2a ve2);
    assert (pure (Seq.equal (dcat va ve1 ve2) va));
    gene_def p (reveal vkey) (reveal vval) (SZ.v c) (SZ.v n) (reveal va);
    maybe_update p kt ivt k v additional alen e1a e2a;
    gen_loop p kt ivt k v out n;
    Hacl.HMAC.DRBG.Core.update p kt ivt k v additional alen e1a 0sz e2a 0sz;
    A.((ctr.(0sz) <- SZ.add c 1sz));
    with vctr'. assert (A.pts_to ctr vctr');
    assert (pure (ctr_val vctr' == SZ.v c + 1));
    true
  }
}

#pop-options
