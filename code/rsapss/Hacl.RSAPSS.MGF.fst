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

(** MGF1, the PKCS #1 mask generation function.

    One scratch buffer holds [seed | counter].  The seed is written once; each
    round overwrites the four counter bytes and hashes the whole thing into a
    digest buffer, which is then copied -- truncated on the last round -- into
    the output.  That is the same loop as HKDF's expand without the chaining,
    and the invariant is the same too: the output agrees with
    [mgf_all p seed nb] wherever it has been written, for the [nb] that the
    final round count will turn out to be. *)
module Hacl.RSAPSS.MGF

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.SHA2
open Spec.RSAPSS
open Hacl.Spec.Bytes
open Hacl.Hash.SHA2.Core
open Hacl.Impl.Copy
open Hacl.Impl.Bytes

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Mem = Hacl.Mem

(** {2 One round}

    The buffer already holds the seed; this writes the counter and hashes. *)

#push-options "--z3rlimit 200 --fuel 0 --ifuel 0"

(** The buffer is the seed followed by four bytes of anything. *)
unfold let buf_ok (seed: Seq.seq S8.t) (m: Seq.seq S8.t) =
  Seq.length m == Seq.length seed + 4 /\
  (forall (k: nat). k < Seq.length seed ==> Seq.index m k == Seq.index seed k)

(** The counter fits in four bytes, so the whole block is determined by the
    seed and the round index; this is the only thing the round needs to say. *)
let buf_is_block (seed: Seq.seq S8.t) (m: Seq.seq S8.t) (i: nat)
  : Lemma (requires buf_ok seed m /\
                    (forall (k: nat). k < 4 ==>
                       S8.v (Seq.index m (Seq.length seed + k)) ==
                         (i / pow2 (8 * (4 - 1 - k))) % 256))
          (ensures m == Seq.append seed (counter i))
  = let r = Seq.append seed (counter i) in
    Seq.lemma_len_append seed (counter i);
    let aux (k: nat { k < Seq.length m })
      : Lemma (Seq.index m k == Seq.index r k)
      = if k < Seq.length seed
        then Seq.lemma_index_app1 seed (counter i) k
        else begin
          Seq.lemma_index_app2 seed (counter i) k;
          nat_to_be_index 4 i (k - Seq.length seed);
          S8.v_extensional (Seq.index m k) (Seq.index (counter i) (k - Seq.length seed))
        end
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro m r

fn round (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
         (kt: A.array t) (ivt: A.array t)
         (dg: A.array S8.t) (m: A.array S8.t) (ml: SZ.t) (i: U32.t)
         (#seed: erased (seed_t t))
         (#pk: perm) (#vk: erased (Seq.seq t))
         (#pi: perm) (#vi: erased (Seq.seq t))
         (#vdg: erased (Seq.seq S8.t)) (#vm: erased (Seq.seq S8.t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg ** A.pts_to m vm **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               Seq.length vdg == (hash_bytes p) /\
               seed_ok #t (reveal seed) /\ Seq.length seed + 4 < pow2 61 /\
               buf_ok (reveal seed) (reveal vm) /\ SZ.v ml == Seq.length vm)
ensures exists* (vdg': Seq.seq S8.t) (vm': Seq.seq S8.t).
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to dg vdg' ** A.pts_to m vm' **
  pure (Seq.length vdg' == (hash_bytes p) /\ buf_ok (reveal seed) vm' /\
        Seq.length vm' == Seq.length vm /\
        vdg' == mgf_block p (reveal seed) (U32.v i))
{
  A.pts_to_len dg;
  A.pts_to_len m;
  let sl = SZ.sub ml 4sz;
  store_be #S32.t m sl (S32.classify i);
  with vm1. assert (A.pts_to m vm1);
  buf_is_block (reveal seed) (reveal vm1) (U32.v i);
  hash_impl p kt ivt dg m ml;
}

#pop-options

(** {2 The loop} *)

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"

(** [res] receives the first [maskLen] bytes of MGF1 over [seed].

    [maskLen] is public -- it is derived from the modulus size -- so the
    number of rounds may and does depend on it. *)
fn mgf_impl (#t: Type0) {| w: word t |} {| Hacl.Zeroable.zeroable t |} ([@@@FStar.Attributes.monomorphize] p: params t)
            (kt: A.array t) (ivt: A.array t)
            (res: A.array S8.t) (maskLen: SZ.t)
            (seed: A.array S8.t) (slen: SZ.t)
            (#pk: perm) (#vk: erased (Seq.seq t))
            (#pi: perm) (#vi: erased (Seq.seq t))
            (#vres: erased (Seq.seq S8.t))
            (#ps: perm) (#vseed: erased (seed_t t))
requires A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to res vres **
         A.pts_to seed #ps vseed **
         pure (reveal vk == (reveal p.k <: Seq.seq t) /\ reveal vi == (reveal p.iv <: Seq.seq t) /\
               seed_ok #t (reveal vseed) /\ Seq.length vseed + 4 < pow2 61 /\
               SZ.fits (Seq.length vseed + 4) /\
               SZ.fits (Seq.length vres + (hash_bytes p)) /\
               Seq.length vres < pow2 32 /\
               SZ.v maskLen == Seq.length vres /\ SZ.v slen == Seq.length vseed)
ensures exists* vres'.
  A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to res vres' **
  A.pts_to seed #ps vseed **
  pure (seed_ok #t (reveal vseed) /\
        Seq.length vres' == Seq.length vres /\
        vres' == mgf p (reveal vseed) (Seq.length vres))
{
  A.pts_to_len kt;
  A.pts_to_len ivt;
  A.pts_to_len res;
  A.pts_to_len seed;
  let hb = p.nhash_bytes;
  let z8 = S8.classify 0uy;
  let ml = SZ.add slen 4sz;

  let marr = Mem.alloc z8 ml;
  A.pts_to_len marr;
  let mut darr = [| z8; hb |];
  Mem.track darr;
  A.pts_to_len darr;

  copy_at marr 0sz seed slen;

  (* The block count, once, as a machine value.  Everything below is stated
     against it and never against [nblocks]: a [params] and a division in a
     Pulse query cost more than the entire loop. *)
  let n = SZ.div (SZ.add maskLen (SZ.sub hb 1sz)) hb;
  div_ceil_ok (SZ.v maskLen) (hash_bytes p);
  div_ceil_le (SZ.v maskLen) (hash_bytes p);

  let mut base = 0sz;
  let mut ci = 0ul;
  while (let vb = !base; SZ.lt vb maskLen)
  invariant exists* (vb: SZ.t) (vc: U32.t) (vres': Seq.seq S8.t)
                    (vdg': Seq.seq S8.t) (vm': Seq.seq S8.t).
    pts_to base vb ** pts_to ci vc **
    A.pts_to kt #pk vk ** A.pts_to ivt #pi vi ** A.pts_to res vres' **
    A.pts_to seed #ps vseed ** A.pts_to darr vdg' ** A.pts_to marr vm' **
    pure (seed_ok #t (reveal vseed) /\
          Seq.length vres' == Seq.length vres /\ Seq.length vres' == SZ.v maskLen /\
          Seq.length vdg' == (hash_bytes p) /\
          buf_ok (reveal vseed) vm' /\ Seq.length vm' == SZ.v ml /\
          SZ.v maskLen <= SZ.v n * (hash_bytes p) /\ SZ.v n <= SZ.v maskLen /\
          U32.v vc <= SZ.v n /\ SZ.v vb == U32.v vc * (hash_bytes p) /\
          (forall (k: nat). k < Seq.length vres' /\ k < SZ.v vb ==>
             k < SZ.v n * (hash_bytes p) /\
             Seq.index vres' k == Seq.index (mgf_all p (reveal vseed) (SZ.v n)) k))
  decreases (SZ.v n - U32.v (!ci))
  {
    let vb = !base;
    let vc = !ci;
    (* [vb = vc * hb < maskLen <= n * hb], so there is another block. *)
    mult_lt_cancel (U32.v vc) (SZ.v n) (hash_bytes p);
    with vold. assert (A.pts_to res vold);
    round p kt ivt darr marr ml vc #(hide #(seed_t t) (reveal vseed));
    write_chunk res maskLen vb darr hb;
    with vnew. assert (A.pts_to res vnew);
    with vdg. assert (A.pts_to darr vdg);
    mgf_round_index p (reveal vseed) (SZ.v maskLen) (SZ.v n) (U32.v vc) vold vnew vdg;
    Math.distributivity_add_left (U32.v vc) 1 (hash_bytes p);
    SZ.fits_lte (SZ.v vb + SZ.v hb) (Seq.length vres + (hash_bytes p));
    base := SZ.add vb hb;
    ci := U32.add vc 1ul;
  };

  with vres'. assert (A.pts_to res vres');
  mgf_index p (reveal vseed) (Seq.length vres) (SZ.v n);
  Seq.lemma_eq_intro (reveal vres') (mgf p (reveal vseed) (Seq.length vres));
  Mem.wipe darr hb;
  Mem.free marr ml;
  ()
}

#pop-options
