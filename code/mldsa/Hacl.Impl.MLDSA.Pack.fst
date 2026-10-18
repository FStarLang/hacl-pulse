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


(** Keys, signatures and the masking vector: the field layout of
    {!Spec.MLDSA.Encode} over the vector codecs of
    {!Hacl.Impl.MLDSA.VecCodec} and the hint codec of
    {!Hacl.Impl.MLDSA.Hint}.  Each field is packed into, or unpacked from,
    a window of the encoding; the lemmas below turn the windows back into
    the specification's concatenations. *)
module Hacl.Impl.MLDSA.Pack

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Encode
open Spec.MLDSA.Sample
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Encode
open Hacl.Impl.MLDSA.VecCodec
open Hacl.Impl.MLDSA.Hint
open Hacl.Impl.MLDSA.SampleLemmas

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module HSZ = Hacl.SizeT
module Sub = Hacl.Impl.Sub
module Copy = Hacl.Impl.Copy
module KZ = Spec.MLKEM.Zq
module KE = Spec.MLKEM.Encode
module SHA3 = Spec.SHA3
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Windows} *)

(** [w] is [v] with [[i, j)] replaced by [b]: what {!Sub.unsub} leaves. *)
let spliced (#t: Type) (w v: Seq.seq t) (i j: nat) (b: Seq.seq t) : prop
  = Seq.length w == Seq.length v /\ i <= j /\ Seq.length b == j - i /\
    (forall (k: nat). k < Seq.length w ==>
       Seq.index w k == (if i <= k && k < j then Seq.index b (k - i) else Seq.index v k))

let glue2 (#t: Type) (w v: Seq.seq t) (i: nat) (b: Seq.seq t)
  : Lemma (requires i <= Seq.length v /\ Seq.length b == Seq.length v - i /\
                    spliced w v i (Seq.length v) b)
          (ensures w == Seq.append (Seq.slice v 0 i) b)
  = Seq.lemma_eq_intro w (Seq.append (Seq.slice v 0 i) b)

let glue3 (#t: Type) (w2 w1 v: Seq.seq t) (i j: nat) (b1 b2: Seq.seq t)
  : Lemma (requires i <= j /\ j <= Seq.length v /\
                    Seq.length b1 == j - i /\ Seq.length b2 == Seq.length v - j /\
                    spliced w1 v i j b1 /\ spliced w2 w1 j (Seq.length v) b2)
          (ensures w2 == Seq.append (Seq.slice v 0 i) (Seq.append b1 b2))
  = Seq.lemma_eq_intro w2 (Seq.append (Seq.slice v 0 i) (Seq.append b1 b2))

let glue4 (#t: Type) (w3 w2 w1 v: Seq.seq t) (i j m: nat) (b1 b2 b3: Seq.seq t)
  : Lemma (requires i <= j /\ j <= m /\ m <= Seq.length v /\
                    Seq.length b1 == j - i /\ Seq.length b2 == m - j /\
                    Seq.length b3 == Seq.length v - m /\
                    spliced w1 v i j b1 /\ spliced w2 w1 j m b2 /\
                    spliced w3 w2 m (Seq.length v) b3)
          (ensures w3 == Seq.append (Seq.slice v 0 i) (Seq.append b1 (Seq.append b2 b3)))
  = Seq.lemma_eq_intro w3 (Seq.append (Seq.slice v 0 i) (Seq.append b1 (Seq.append b2 b3)))

(** The 128-byte head of a private key is its three fixed fields. *)
let sk_head (v: Seq.seq S8.t) (rest: Seq.seq S8.t)
  : Lemma (requires Seq.length v >= 128)
          (ensures Seq.append (Seq.slice v 0 128) rest ==
                   Seq.append (Seq.slice v 0 32) (Seq.append (Seq.slice v 32 64)
                     (Seq.append (Seq.slice v 64 128) rest)))
  = Seq.lemma_eq_intro (Seq.append (Seq.slice v 0 128) rest)
                       (Seq.append (Seq.slice v 0 32) (Seq.append (Seq.slice v 32 64)
                         (Seq.append (Seq.slice v 64 128) rest)))

let t1_bound (k: pos) (s: Seq.lseq S8.t (k * (32 * 10))) (v: Seq.seq zqt { Seq.length v == k * n })
  : Lemma (requires as_ints v == vec_simple_bit_unpack 10 k s)
          (ensures forall (i: nat). i < k * n ==> S32.v (Seq.index v i) < 1024)
  = assert_norm (pow2 10 == 1024);
    let aux (i: nat { i < k * n }) : Lemma (S32.v (Seq.index v i) < 1024)
      = as_ints_index v i;
        KZ.div_lt i k n;
        let blk = KZ.flat_at k (32 * 10) s (i / n) in
        assert (Seq.index (vec_simple_bit_unpack 10 k s) i ==
                Seq.index (simple_bit_unpack 10 blk) (i % n))
    in
    Classical.forall_intro aux

let gamma1_val (p: params) : Lemma (gamma1 p == (if p.gamma1_bits = 17 then 131072 else 524288))
  = assert_norm (pow2 17 == 131072);
    assert_norm (pow2 19 == 524288)

(** {2 Public keys} *)

fn pk_encode_impl (p: erased params) (pk: A.array S8.t) (t1: A.array zqt)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  (#vp: erased (Seq.seq S8.t)) (#pt: perm) (#vt: erased (Seq.seq zqt))
requires A.pts_to pk vp ** A.pts_to t1 #pt vt **
         pure (SZ.v k == p.k /\ Seq.length vp == pk_len p /\ Seq.length vt == p.k * n)
ensures exists* (v: Seq.seq S8.t). A.pts_to pk v ** A.pts_to t1 #pt vt **
  pure (Seq.length vp == pk_len p /\ Seq.length vt == p.k * n /\
        v == pk_encode p (Seq.slice vp 0 32) (as_ints vt))
{
  A.pts_to_len pk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (pk_len p);
  let len = SZ.add 32sz (SZ.mul 320sz k);
  let w = Sub.sub pk 32sz len;
  vec_pack w t1 10sz false S32.zero k;
  with b. assert (A.pts_to w b);
  vpack_simple 10 p.k 0 vt;
  assert (pure (b == vec_simple_bit_pack 10 p.k (as_ints vt)));
  Sub.unsub pk 32 (SZ.v len) w;
  with v. assert (A.pts_to pk v);
  assert (pure (spliced v vp 32 (pk_len p) b));
  glue2 v vp 32 b;
  assert (pure (v == Seq.append (Seq.slice vp 0 32) (vec_simple_bit_pack 10 p.k (as_ints vt))));
}

fn pk_decode_impl (p: erased params) (t1: A.array zqt) (pk: A.array S8.t)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  (#vt: erased (Seq.seq zqt)) (#pp: perm) (#vp: erased (Seq.seq S8.t))
requires A.pts_to t1 vt ** A.pts_to pk #pp vp **
         pure (SZ.v k == p.k /\ Seq.length vp == pk_len p /\ Seq.length vt == p.k * n)
ensures exists* (v: Seq.seq zqt). A.pts_to t1 v ** A.pts_to pk #pp vp **
  pure (Seq.length vp == pk_len p /\ Seq.length v == p.k * n /\
        as_ints v == snd (pk_decode p vp) /\
        (forall (i: nat). i < p.k * n ==> S32.v (Seq.index v i) < 1024))
{
  A.pts_to_len pk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (pk_len p);
  let len = SZ.add 32sz (SZ.mul 320sz k);
  let w = Sub.sub pk 32sz len;
  vec_unpack t1 w 10sz false S32.zero k;
  Sub.unsub_id pk 32 (SZ.v len) w;
  with v. assert (A.pts_to t1 v);
  t1_bound p.k (Seq.slice vp 32 (pk_len p)) v;
  ()
}

(** {2 Private keys} *)

inline_for_extraction
let eta_bits_impl (eta: SZ.t { SZ.v eta == 2 \/ SZ.v eta == 4 })
  : r: SZ.t { SZ.v r == (if SZ.v eta = 2 then 3 else 4) }
  = if eta = 2sz then 3sz else 4sz

inline_for_extraction
let eta_zq (eta: SZ.t { SZ.v eta == 2 \/ SZ.v eta == 4 })
  : r: zqt { S32.v r == SZ.v eta }
  = if eta = 2sz then S32.classify 2ul else S32.classify 4ul

inline_for_extraction
let t0_b : r: zqt { S32.v r == pow2 12 } =
  assert_norm (pow2 12 == 4096);
  S32.classify 4096ul

fn sk_encode_impl (p: erased params) (sk: A.array S8.t) (s1 s2 t0: A.array zqt)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                  (#vk: erased (Seq.seq S8.t)) (#p1 #p2 #p0: perm)
                  (#v1 #v2 #v0: erased (Seq.seq zqt))
requires A.pts_to sk vk ** A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 ** A.pts_to t0 #p0 v0 **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
               Seq.length vk == sk_len p /\ Seq.length v1 == p.l * n /\
               Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to sk v ** A.pts_to s1 #p1 v1 ** A.pts_to s2 #p2 v2 ** A.pts_to t0 #p0 v0 **
  pure (Seq.length vk == sk_len p /\ Seq.length v1 == p.l * n /\
        Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n /\
        v == sk_encode p (Seq.slice vk 0 32) (Seq.slice vk 32 64) (Seq.slice vk 64 128)
                       (as_zqs v1) (as_zqs v2) (as_zqs v0))
{
  A.pts_to_len sk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sk_len p);
  assert_norm (pow2 12 == 4096);
  sk_layout p;
  let eb = eta_bits_impl eta;
  let be = eta_zq eta;
  let o1 = SZ.add 128sz (SZ.mul l (SZ.mul 32sz eb));
  let o2 = SZ.add o1 (SZ.mul k (SZ.mul 32sz eb));
  let o3 = SZ.add o2 (SZ.mul k 416sz);
  let w1 = Sub.sub sk 128sz o1;
  vec_pack w1 s1 eb true be l;
  with b1. assert (A.pts_to w1 b1);
  vpack_signed (eta_bits p) p.l p.eta v1;
  Sub.unsub sk 128 (SZ.v o1) w1;
  with u1. assert (A.pts_to sk u1);
  assert (pure (spliced u1 vk 128 (SZ.v o1) b1));
  let w2 = Sub.sub sk o1 o2;
  vec_pack w2 s2 eb true be k;
  with b2. assert (A.pts_to w2 b2);
  vpack_signed (eta_bits p) p.k p.eta v2;
  Sub.unsub sk (SZ.v o1) (SZ.v o2) w2;
  with u2. assert (A.pts_to sk u2);
  assert (pure (spliced u2 u1 (SZ.v o1) (SZ.v o2) b2));
  let w3 = Sub.sub sk o2 o3;
  vec_pack w3 t0 13sz true t0_b k;
  with b3. assert (A.pts_to w3 b3);
  vpack_signed 13 p.k (pow2 12) v0;
  Sub.unsub sk (SZ.v o2) (SZ.v o3) w3;
  with u3. assert (A.pts_to sk u3);
  assert (pure (spliced u3 u2 (SZ.v o2) (sk_len p) b3));
  glue4 u3 u2 u1 vk 128 (SZ.v o1) (SZ.v o2) b1 b2 b3;
  sk_head vk (Seq.append b1 (Seq.append b2 b3));
  ()
}

fn sk_decode_impl (p: erased params) (s1 s2 t0: A.array zqt) (sk: A.array S8.t)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                  ([@@@FStar.Attributes.monomorphize] eta: SZ.t)
                  (#v1 #v2 #v0: erased (Seq.seq zqt)) (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to s1 v1 ** A.pts_to s2 v2 ** A.pts_to t0 v0 ** A.pts_to sk #pk vk **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v eta == p.eta /\
               Seq.length vk == sk_len p /\ Seq.length v1 == p.l * n /\
               Seq.length v2 == p.k * n /\ Seq.length v0 == p.k * n)
ensures exists* (w1 w2 w0: Seq.seq zqt).
  A.pts_to s1 w1 ** A.pts_to s2 w2 ** A.pts_to t0 w0 ** A.pts_to sk #pk vk **
  pure (Seq.length vk == sk_len p /\ Seq.length w1 == p.l * n /\
        Seq.length w2 == p.k * n /\ Seq.length w0 == p.k * n /\
        as_zqs w1 == (sk_decode p vk).sk_s1 /\
        as_zqs w2 == (sk_decode p vk).sk_s2 /\
        as_zqs w0 == (sk_decode p vk).sk_t0)
{
  A.pts_to_len sk;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sk_len p);
  assert_norm (pow2 12 == 4096);
  sk_layout p;
  let eb = eta_bits_impl eta;
  let be = eta_zq eta;
  let o1 = SZ.add 128sz (SZ.mul l (SZ.mul 32sz eb));
  let o2 = SZ.add o1 (SZ.mul k (SZ.mul 32sz eb));
  let o3 = SZ.add o2 (SZ.mul k 416sz);
  let w1 = Sub.sub sk 128sz o1;
  vec_unpack s1 w1 eb true be l;
  Sub.unsub_id sk 128 (SZ.v o1) w1;
  let w2 = Sub.sub sk o1 o2;
  vec_unpack s2 w2 eb true be k;
  Sub.unsub_id sk (SZ.v o1) (SZ.v o2) w2;
  let w3 = Sub.sub sk o2 o3;
  vec_unpack t0 w3 13sz true t0_b k;
  Sub.unsub_id sk (SZ.v o2) (SZ.v o3) w3;
  ()
}

(** {2 Signatures} *)

inline_for_extraction
let gamma1_zq (g1bits: SZ.t { SZ.v g1bits == 17 \/ SZ.v g1bits == 19 })
  : r: zqt { S32.v r == pow2 (SZ.v g1bits) }
  = assert_norm (pow2 17 == 131072);
    assert_norm (pow2 19 == 524288);
    if g1bits = 17sz then S32.classify 131072ul else S32.classify 524288ul

fn sig_encode_impl (p: erased params) (sg: A.array S8.t) (z: A.array zqt) (h: A.array S32.t)
                   ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                   (#vs: erased (Seq.seq S8.t)) (#pz #ph: perm)
                   (#vz: erased (Seq.seq zqt)) (#vh: erased (Seq.seq S32.t))
requires A.pts_to sg vs ** A.pts_to z #pz vz ** A.pts_to h #ph vh **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v ctl == ct_len p /\
               SZ.v g1bits == p.gamma1_bits /\ SZ.v omega == p.omega /\
               Seq.length vs == sig_len p /\ Seq.length vz == p.l * n /\
               Seq.length vh == p.k * n)
ensures exists* (v: Seq.seq S8.t).
  A.pts_to sg v ** A.pts_to z #pz vz ** A.pts_to h #ph vh **
  pure (Seq.length vs == sig_len p /\ Seq.length vz == p.l * n /\
        Seq.length vh == p.k * n /\
        v == sig_encode p (Seq.slice vs 0 (ct_len p)) (as_zqs vz) (hint_view vh))
{
  A.pts_to_len sg;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sig_len p);
  Math.pow2_lt_compat 20 p.gamma1_bits;
  assert_norm (pow2 20 < q);
  sig_layout p;
  let zb = SZ.add g1bits 1sz;
  let gb = gamma1_zq g1bits;
  let o1 = SZ.add ctl (SZ.mul l (SZ.mul 32sz zb));
  let o2 = SZ.add o1 (SZ.add omega k);
  let w1 = Sub.sub sg ctl o1;
  vec_pack w1 z zb true gb l;
  with b1. assert (A.pts_to w1 b1);
  vpack_signed (z_bits p) p.l (gamma1 p) vz;
  Sub.unsub sg (SZ.v ctl) (SZ.v o1) w1;
  with u1. assert (A.pts_to sg u1);
  assert (pure (spliced u1 vs (SZ.v ctl) (SZ.v o1) b1));
  let w2 = Sub.sub sg o1 o2;
  hint_pack_impl w2 h p k omega;
  with b2. assert (A.pts_to w2 b2);
  Sub.unsub sg (SZ.v o1) (SZ.v o2) w2;
  with u2. assert (A.pts_to sg u2);
  assert (pure (spliced u2 u1 (SZ.v o1) (sig_len p) b2));
  glue3 u2 u1 vs (ct_len p) (SZ.v o1) b1 b2;
  ()
}

fn sig_decode_impl (p: erased params) (z: A.array zqt) (h: A.array S32.t) (sg: A.array S8.t)
                   ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] ctl: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                   ([@@@FStar.Attributes.monomorphize] omega: SZ.t)
                   (#vz: erased (Seq.seq zqt)) (#vh: erased (Seq.seq S32.t))
                   (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires A.pts_to z vz ** A.pts_to h vh ** A.pts_to sg #ps vs **
         pure (SZ.v k == p.k /\ SZ.v l == p.l /\ SZ.v ctl == ct_len p /\
               SZ.v g1bits == p.gamma1_bits /\ SZ.v omega == p.omega /\
               Seq.length vs == sig_len p /\ Seq.length vz == p.l * n /\
               Seq.length vh == p.k * n)
returns ok: bool
ensures exists* (wz: Seq.seq zqt) (wh: Seq.seq S32.t).
  A.pts_to z wz ** A.pts_to h wh ** A.pts_to sg #ps vs **
  pure (Seq.length vs == sig_len p /\ Seq.length wz == p.l * n /\
        Seq.length wh == p.k * n /\ hint_bits wh /\
        (let (_, zs, ho) = sig_decode p vs in
         as_zqs wz == zs /\
         ho == (if ok then Some (hint_view wh) else None)))
{
  A.pts_to_len sg;
  HSZ.fits32 ();
  SZ.fits_u32_implies_fits (sig_len p);
  Math.pow2_lt_compat 20 p.gamma1_bits;
  assert_norm (pow2 20 < q);
  sig_layout p;
  let zb = SZ.add g1bits 1sz;
  let gb = gamma1_zq g1bits;
  let o1 = SZ.add ctl (SZ.mul l (SZ.mul 32sz zb));
  let o2 = SZ.add o1 (SZ.add omega k);
  let w1 = Sub.sub sg ctl o1;
  vec_unpack z w1 zb true gb l;
  Sub.unsub_id sg (SZ.v ctl) (SZ.v o1) w1;
  let w2 = Sub.sub sg o1 o2;
  let ok = hint_unpack_impl h w2 p k omega;
  Sub.unsub_id sg (SZ.v o1) (SZ.v o2) w2;
  ok
}

(** {2 The commitment} *)

fn w1_encode_impl (p: erased params) (out: A.array S8.t) (w1: A.array zqt)
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  (gd: U32.t)
                  (#vo: erased (Seq.seq S8.t)) (#pw: perm) (#vw: erased (Seq.seq zqt))
requires A.pts_to out vo ** A.pts_to w1 #pw vw **
         pure (SZ.v k == p.k /\ U32.v gd == p.gamma2_div /\
               Seq.length vo == p.k * (32 * w1_bits p) /\ Seq.length vw == p.k * n)
ensures exists* (v: Seq.seq S8.t). A.pts_to out v ** A.pts_to w1 #pw vw **
  pure (Seq.length vw == p.k * n /\ v == w1_encode p (as_ints vw))
{
  let wb = (if gd = 88ul then 6sz else 4sz);
  vec_pack out w1 wb false S32.zero k;
  vpack_simple (w1_bits p) p.k 0 vw;
  ()
}

(** {2 ExpandMask} *)

let seed_16_full (rho: Seq.seq S8.t) (x: nat { x < pow2 16 }) (v: Seq.seq S8.t)
  : Lemma (requires Seq.length v == Seq.length rho + 2 /\
                    (forall (t: nat). t < Seq.length rho ==> Seq.index v t == Seq.index rho t) /\
                    S8.v (Seq.index v (Seq.length rho)) == x % 256 /\
                    S8.v (Seq.index v (Seq.length rho + 1)) == x / 256)
          (ensures v == seed_16 rho x)
  = assert_norm (pow2 16 == 65536);
    let s = seed_16 rho x in
    let aux (t: nat { t < Seq.length v }) : Lemma (Seq.index v t == Seq.index s t)
      = if t < Seq.length rho then ()
        else S8.v_extensional (Seq.index v t) (Seq.index s t)
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro v s

let expand_mask_at (p: params) (rho: Seq.lseq S8.t 64) (a: nat { a < max_attempts })
                   (r: nat { r < p.l })
  : Lemma (kappa_bound p a r;
           KZ.flat_at p.l n (expand_mask p rho a) r == expand_mask_poly p rho (a * p.l + r))
  = vec_at_of_fun_g p.l (fun r ->
      kappa_bound p a r;
      expand_mask_poly p rho (a * p.l + r)) r

let seed_bytes (k: SZ.t) (kv: nat)
  : Lemma (requires SZ.v k == kv /\ kv < pow2 16)
          (ensures (let x = SZ.sizet_to_uint32 k in
                    U32.v x == kv /\
                    S8.v (S8.classify (Cast.uint32_to_uint8 (U32.rem x 256ul))) == kv % 256 /\
                    S8.v (S8.classify (Cast.uint32_to_uint8 (U32.div x 256ul))) == kv / 256))
  = assert_norm (pow2 16 == 65536);
    assert_norm (pow2 32 == 4294967296);
    assert_norm (pow2 8 == 256);
    Math.small_mod kv (pow2 32);
    Math.small_mod (kv % 256) 256;
    Math.small_mod (kv / 256) 256

let mask_step (p: params) (rho: Seq.lseq S8.t 64) (a: nat { a < max_attempts })
              (r: nat { r < p.l })
              (w0 w1: Seq.seq zqt) (b: Seq.seq zqt) (sd: Seq.seq S8.t) (buf: Seq.seq S8.t)
  : Lemma (requires
      Seq.length w0 == p.l * n /\ Seq.length w1 == p.l * n /\ Seq.length b == n /\
      (forall (i: nat). i < p.l * n ==>
         Seq.index w1 i == (if r * n <= i && i < r * n + n
                            then Seq.index b (i - r * n) else Seq.index w0 i)) /\
      prefix_eq w0 (expand_mask p rho a) (r * n) /\
      Seq.length sd == 66 /\
      (forall (i: nat). i < 64 ==> Seq.index sd i == Seq.index rho i) /\
      a * p.l + r < pow2 16 /\
      S8.v (Seq.index sd 64) == (a * p.l + r) % 256 /\
      S8.v (Seq.index sd 65) == (a * p.l + r) / 256 /\
      (mask_bound p;
       Seq.length buf == 32 * z_bits p /\
       buf == SHA3.shake256 sd (32 * z_bits p) /\
       as_poly b == bit_unpack (gamma1 p) (z_bits p) buf))
    (ensures prefix_eq w1 (expand_mask p rho a) ((r + 1) * n))
  = reveal_opaque (`%prefix_eq) (prefix_eq w0 (expand_mask p rho a) (r * n));
    reveal_opaque (`%prefix_eq) (prefix_eq w1 (expand_mask p rho a) ((r + 1) * n));
    seed_16_full rho (a * p.l + r) sd;
    expand_mask_at p rho a r;
    Math.lemma_mult_le_right n r p.l;
    introduce forall (i: nat). i < r * n ==>
                S32.v (Seq.index w0 i) == Seq.index (expand_mask p rho a) i
    with introduce _ ==> _ with assert (i < p.l * n);
    flat_step p.l r w0 w1 b (expand_mask p rho a)

fn expand_mask_impl (p: erased params) (y: A.array zqt) (rho: A.array S8.t)
                    ([@@@FStar.Attributes.monomorphize] l: SZ.t)
                    ([@@@FStar.Attributes.monomorphize] g1bits: SZ.t)
                    (kappa: SZ.t) (a: erased (x: nat { x < max_attempts }))
                    (#vy: erased (Seq.seq zqt)) (#pr: perm) (#vr: erased (Seq.seq S8.t))
requires A.pts_to y vy ** A.pts_to rho #pr vr **
         pure (SZ.v l == p.l /\ SZ.v g1bits == p.gamma1_bits /\
               SZ.v kappa == a * p.l /\
               Seq.length vr == 64 /\ Seq.length vy == p.l * n)
ensures exists* (v: Seq.seq zqt). A.pts_to y v ** A.pts_to rho #pr vr **
  pure (Seq.length vr == 64 /\ Seq.length v == p.l * n /\
        as_zqs v == expand_mask p vr a)
{
  A.pts_to_len y;
  A.pts_to_len rho;
  HSZ.fits32 ();
  assert_norm (8 * n < pow2 32);
  assert_norm (pow2 32 == 4294967296);
  assert_norm (pow2 8 == 256);
  assert_norm (pow2 16 == 65536);
  mask_bound p;
  let zb = SZ.add g1bits 1sz;
  let gb = gamma1_zq g1bits;
  let blen = SZ.mul 32sz zb;
  let z8 = S8.classify 0uy;
  let mut sd = [| z8; 66sz |];
  Mem.track sd;
  let mut buf = [| z8; 640sz |];
  Mem.track buf;
  A.pts_to_len sd;
  A.pts_to_len buf;
  Copy.copy_prefix sd rho 64sz;
  prefix_zero vy (expand_mask p vr a);
  let mut c = 0sz;
  while (let vc = !c; SZ.lt vc l)
  invariant exists* (vc: SZ.t) (v: Seq.seq zqt) (vsd: Seq.seq S8.t) (vb: Seq.seq S8.t).
    pts_to c vc ** A.pts_to y v ** A.pts_to rho #pr vr ** A.pts_to sd vsd ** A.pts_to buf vb **
    pure (SZ.v vc <= p.l /\ SZ.v l == p.l /\ SZ.v kappa == a * p.l /\
          Seq.length v == p.l * n /\ Seq.length vr == 64 /\
          Seq.length vsd == 66 /\ Seq.length vb == 640 /\
          (forall (t: nat). t < 64 ==> Seq.index vsd t == Seq.index vr t) /\
          prefix_eq v (expand_mask p vr a) (SZ.v vc * n))
  decreases (SZ.v l - SZ.v (!c))
  {
    let vc = !c;
    Math.lemma_mult_le_right n (SZ.v vc + 1) p.l;
    Math.distributivity_add_left (SZ.v vc) 1 n;
    Math.lemma_mult_le_right n p.l 8;
    kappa_bound p a (SZ.v vc);
    SZ.fits_u32_implies_fits (SZ.v vc * n + n);
    let lo = SZ.mul vc 256sz;
    let hi = SZ.add lo 256sz;
    let x = SZ.sizet_to_uint32 (SZ.add kappa vc);
    seed_bytes (SZ.add kappa vc) (a * p.l + SZ.v vc);
    let b0 = Cast.uint32_to_uint8 (U32.rem x 256ul);
    let b1 = Cast.uint32_to_uint8 (U32.div x 256ul);
    Math.small_mod (U32.v x % 256) 256;
    Math.small_mod (U32.v x / 256) 256;
    A.((sd.(64sz) <- S8.classify b0));
    A.((sd.(65sz) <- S8.classify b1));
    with vsd. assert (A.pts_to sd vsd);
    assert (pure (S8.v (Seq.index vsd 64) == (a * p.l + SZ.v vc) % 256));
    assert (pure (S8.v (Seq.index vsd 65) == (a * p.l + SZ.v vc) / 256));
    let ob = Sub.sub buf 0sz blen;
    Hacl.Hash.SHA3.shake256 ob blen sd 66sz;
    with vo. assert (A.pts_to ob vo);
    with w0. assert (A.pts_to y w0);
    let blk = Sub.sub y lo hi;
    unpack_poly blk ob zb true gb;
    with bk. assert (A.pts_to blk bk);
    Sub.unsub y (SZ.v lo) (SZ.v hi) blk;
    with w1. assert (A.pts_to y w1);
    mask_step p vr a (SZ.v vc) w0 w1 bk vsd vo;
    Sub.unsub buf 0 (SZ.v blen) ob;
    c := SZ.add vc 1sz;
  };
  with v. assert (A.pts_to y v);
  prefix_done p.l v (expand_mask p vr a);
  Mem.wipe buf 640sz;
  Mem.wipe sd 66sz;
  ()
}

#pop-options
