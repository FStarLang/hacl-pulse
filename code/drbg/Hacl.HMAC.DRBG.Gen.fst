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

(** The output loop of HMAC_DRBG, SP 800-90A 10.1.2.5 step 4.

    [V := HMAC(K, V)] over and over, each result appended to the output
    until it is full; the last block may be used only in part, but [V] is
    still advanced past it in full.

    The whole-block case and the partial last block are separate functions.
    Written as one [if] inside the loop they make a single verification
    condition that takes almost four minutes; apart they take seconds. *)
module Hacl.HMAC.DRBG.Gen

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Spec.SHA2
open Spec.HMAC
open Spec.HMAC_DRBG
open Hacl.Impl.Copy
open Hacl.HMAC.Core
open Hacl.HMAC.Cat

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module Mem = Hacl.Mem

(** [out] holds the first [i] bytes of the answer, and running the rest of
    the generation from [vcur] produces exactly what is missing. *)
unfold let inv (#t: Type0) {| word t |} (p: params t)
               (vkey: Seq.seq S8.t) (vval: Seq.seq S8.t)
               (vout: Seq.seq S8.t) (i: nat) (vcur: Seq.seq S8.t) : prop =
  i <= Seq.length vout /\ Seq.length vcur == (hash_bytes p) /\
  fst (gen p vkey vval (Seq.length vout)) ==
    Seq.append (Seq.slice vout 0 i) (fst (gen p vkey vcur (Seq.length vout - i))) /\
  snd (gen p vkey vval (Seq.length vout)) ==
    snd (gen p vkey vcur (Seq.length vout - i))

(** {2 One whole block} *)

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"

fn gen_full (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
    ([@@@FStar.Attributes.monomorphize] blocks: Hacl.Hash.SHA2.Core.blocks_t p)
            (kt: A.array t) (ivt: A.array t)
            (k: A.array S8.t) (v: A.array S8.t) (v1: A.array S8.t) (out: A.array S8.t)
            (ix: SZ.t) (vval: erased (Seq.seq S8.t))
            (#pk: perm) (#vk: erased (Seq.seq t))
            (#pi: perm) (#vi: erased (Seq.seq t))
            (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
            (#vcur: erased (Seq.seq S8.t)) (#vv0: erased (Seq.seq S8.t))
            (#vout: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to k #pkey vkey **
         A.pts_to v vcur ** A.pts_to v1 vv0 ** A.pts_to out vout **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vv0 == (hash_bytes p) /\
               SZ.v ix + (hash_bytes p) < Seq.length vout /\
               inv p vkey vval vout (SZ.v ix) vcur)
ensures exists* vcur' vv1 vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to k #pkey vkey **
  A.pts_to v vcur' ** A.pts_to v1 vv1 ** A.pts_to out vout' **
  pure (Seq.length vout' == Seq.length vout /\ Seq.length vv1 == (hash_bytes p) /\
        inv p vkey vval vout' (SZ.v ix + (hash_bytes p)) vcur')
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len v1; A.pts_to_len out;
  let hb = p.nhash_bytes;
  outer_fits #t p;
  sizes #t p;
  hmac_one p blocks kt ivt v1 k hb v hb;
  hm_def p (reveal vkey) (reveal vcur);
  with vv1. assert (A.pts_to v1 vv1);
  copy_exact v v1 hb;
  gen_step p (reveal vkey) (reveal vcur) (Seq.length vout - SZ.v ix);
  copy_at out ix v1 hb;
  with vout'. assert (A.pts_to out vout');
  slice_copy_at (reveal vout) vout' (reveal vv1) (SZ.v ix) (hash_bytes p);
  Seq.append_assoc (Seq.slice vout 0 (SZ.v ix)) (reveal vv1)
                   (fst (gen p vkey vv1 (Seq.length vout - SZ.v ix - (hash_bytes p))));
  assert (pure (reveal vv1 == hm p vkey vcur));
  assert (pure (Seq.slice vout' 0 (SZ.v ix + (hash_bytes p)) ==
                Seq.append (Seq.slice vout 0 (SZ.v ix)) vv1));
  assert (pure (fst (gen p vkey vcur (Seq.length vout - SZ.v ix)) ==
                Seq.append vv1 (fst (gen p vkey vv1
                  (Seq.length vout - SZ.v ix - (hash_bytes p))))));
  assert (pure (snd (gen p vkey vcur (Seq.length vout - SZ.v ix)) ==
                snd (gen p vkey vv1 (Seq.length vout - SZ.v ix - (hash_bytes p)))));
}

#pop-options

(** {2 The last, possibly partial, block} *)

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"

fn gen_tail (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
    ([@@@FStar.Attributes.monomorphize] blocks: Hacl.Hash.SHA2.Core.blocks_t p)
            (kt: A.array t) (ivt: A.array t)
            (k: A.array S8.t) (v: A.array S8.t) (v1: A.array S8.t) (out: A.array S8.t) (n: SZ.t)
            (ix: SZ.t) (vval: erased (Seq.seq S8.t))
            (#pk: perm) (#vk: erased (Seq.seq t))
            (#pi: perm) (#vi: erased (Seq.seq t))
            (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
            (#vcur: erased (Seq.seq S8.t)) (#vv0: erased (Seq.seq S8.t))
            (#vout: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to k #pkey vkey **
         A.pts_to v vcur ** A.pts_to v1 vv0 ** A.pts_to out vout **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vv0 == (hash_bytes p) /\
               SZ.v ix < Seq.length vout /\
               Seq.length vout <= SZ.v ix + (hash_bytes p) /\
               inv p vkey vval vout (SZ.v ix) vcur)
         ** pure (SZ.v n == Seq.length vout)
ensures exists* vcur' vv1 vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to k #pkey vkey **
  A.pts_to v vcur' ** A.pts_to v1 vv1 ** A.pts_to out vout' **
  pure (Seq.length vout' == Seq.length vout /\ Seq.length vv1 == (hash_bytes p) /\
        inv p vkey vval vout' (Seq.length vout) vcur')
{
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len v1; A.pts_to_len out;
  let hb = p.nhash_bytes;
  let rem = SZ.sub n ix;
  outer_fits #t p;
  sizes #t p;
  hmac_one p blocks kt ivt v1 k hb v hb;
  hm_def p (reveal vkey) (reveal vcur);
  with vv1. assert (A.pts_to v1 vv1);
  copy_exact v v1 hb;
  gen_last p (reveal vkey) (reveal vcur) (SZ.v rem);
  gen_zero p (reveal vkey) (reveal vv1);
  copy_at out ix v1 rem;
  with vout'. assert (A.pts_to out vout');
  slice_copy_at (reveal vout) vout' (Seq.slice vv1 0 (SZ.v rem)) (SZ.v ix) (SZ.v rem);
  Seq.append_empty_r (Seq.slice vout' 0 (SZ.v n));
  assert (pure (reveal vv1 == hm p vkey vcur));
  assert (pure (fst (gen p vkey vcur (SZ.v rem)) == Seq.slice vv1 0 (SZ.v rem)));
  assert (pure (snd (gen p vkey vcur (SZ.v rem)) == reveal vv1));
  assert (pure (Seq.slice vout' 0 (SZ.v n) ==
                Seq.append (Seq.slice vout 0 (SZ.v ix)) (Seq.slice vv1 0 (SZ.v rem))));
  assert (pure (fst (gen p vkey vv1 0) == Seq.empty #S8.t));
  assert (pure (Seq.append (Seq.slice vout' 0 (SZ.v n)) (Seq.empty #S8.t) ==
                Seq.slice vout' 0 (SZ.v n)));
}

#pop-options

(** {2 The loop} *)

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"

fn gen_loop (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
    ([@@@FStar.Attributes.monomorphize] blocks: Hacl.Hash.SHA2.Core.blocks_t p)
            (kt: A.array t) (ivt: A.array t)
            (k: A.array S8.t) (v: A.array S8.t) (out: A.array S8.t) (n: SZ.t)
            (#pk: perm) (#vk: erased (Seq.seq t))
            (#pi: perm) (#vi: erased (Seq.seq t))
            (#pkey: perm) (#vkey: erased (Seq.seq S8.t))
            (#vval: erased (Seq.seq S8.t)) (#vout: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
         A.pts_to k #pkey vkey ** A.pts_to v vval ** A.pts_to out vout **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vkey == (hash_bytes p) /\ Seq.length vval == (hash_bytes p))
         ** pure (SZ.v n == Seq.length vout)
ensures exists* vval' vout'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
  A.pts_to k #pkey vkey ** A.pts_to v vval' ** A.pts_to out vout' **
  pure ((vout', vval') == gen p vkey vval (Seq.length vout))
{
  A.pts_to_len kt; A.pts_to_len ivt;
  A.pts_to_len k; A.pts_to_len v; A.pts_to_len out;
  let hb = p.nhash_bytes;
  let z8 = S8.classify 0uy;

  let mut v1arr = [| z8; hb |];
  Mem.track v1arr; A.pts_to_len v1arr;
  A.pts_to_len v1arr;

  let mut i = 0sz;
  gen_len p (reveal vkey) (reveal vval) (SZ.v n);
  Seq.append_empty_l (fst (gen p vkey vval (SZ.v n)));
  assert (pure (Seq.equal (Seq.slice vout 0 0) (Seq.empty #S8.t)));
  while (let ix = !i; SZ.lt ix n)
  invariant exists* (ix: SZ.t) (vcur: Seq.seq S8.t) (vv1: Seq.seq S8.t) (vout': Seq.seq S8.t).
    pts_to i ix ** A.pts_to kt #pk vk ** A.pts_to ivt #pi vi **
    A.pts_to k #pkey vkey ** A.pts_to v vcur ** A.pts_to v1arr vv1 ** A.pts_to out vout' **
    pure (Seq.length vout' == SZ.v n /\ Seq.length vv1 == (hash_bytes p) /\
          inv p vkey vval vout' (SZ.v ix) vcur)
  decreases (SZ.v n - SZ.v (!i))
  {
    let ix = !i;
    let rem = SZ.sub n ix;
    if (SZ.gt rem hb) {
      gen_full p blocks kt ivt k v v1arr out ix vval;
      i := SZ.add ix hb;
    } else {
      gen_tail p blocks kt ivt k v v1arr out n ix vval;
      i := n;
    }
  };
  with vout'. assert (A.pts_to out vout');
  with vcur. assert (A.pts_to v vcur);
  gen_zero p (reveal vkey) (reveal vcur);
  Seq.append_empty_r (Seq.slice vout' 0 (SZ.v n));
  assert (pure (Seq.equal (Seq.slice vout' 0 (SZ.v n)) vout'));
  Mem.wipe v1arr hb;
  ()
}

#pop-options
