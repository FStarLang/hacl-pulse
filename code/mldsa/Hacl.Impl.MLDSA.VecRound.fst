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


(** The coefficient-wise steps of key generation, signing and verification
    over whole vectors: rounding, hints and the norm checks.

    The norm checks and the hint count are the rejection tests of
    signing.  Each loop accumulates its result in secret arithmetic and
    declassifies only the final verdict (or count): which coefficient
    failed is never revealed, only that one did. *)
module Hacl.Impl.MLDSA.VecRound

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Rounding
open Hacl.Impl.MLDSA.Zq
open Hacl.Impl.MLDSA.Round
open Hacl.Impl.MLDSA.Hint

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S32 = Hacl.Secret.UInt32
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module HSZ = Hacl.SizeT
module Declassify = Hacl.Secret.Declassify

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let vlen_ok (k: SZ.t) : prop = 1 <= SZ.v k /\ SZ.v k <= 8

let vlen_fits (k: SZ.t)
  : Lemma (requires vlen_ok k) (ensures SZ.fits (SZ.v k * n) /\ SZ.v k * n <= 8 * n)
  = HSZ.fits32 ();
    assert_norm (8 * n < pow2 32);
    SZ.fits_u32_implies_fits (SZ.v k * n)

(** {2 Counting} *)

#push-options "--fuel 1 --ifuel 1"
let rec count_true_append (a b: Seq.seq bool)
  : Lemma (ensures count_true (Seq.append a b) == count_true a + count_true b)
          (decreases Seq.length a)
  = if Seq.length a = 0 then Seq.lemma_eq_intro (Seq.append a b) b
    else begin
      Seq.lemma_eq_intro (Seq.tail (Seq.append a b)) (Seq.append (Seq.tail a) b);
      count_true_append (Seq.tail a) b
    end

#pop-options

#push-options "--fuel 2 --ifuel 1"
let count_one (b: bool)
  : Lemma (count_true (Seq.create 1 b) == (if b then 1 else 0))
  = Seq.lemma_eq_intro (Seq.tail (Seq.create 1 b)) Seq.empty

let count_zero (s: Seq.seq bool)
  : Lemma (count_true (Seq.slice s 0 0) == 0)
  = Seq.lemma_eq_intro (Seq.slice s 0 0) Seq.empty
#pop-options

let count_step (s: Seq.seq bool) (m: nat { m < Seq.length s })
  : Lemma (count_true (Seq.slice s 0 (m + 1)) ==
           count_true (Seq.slice s 0 m) + (if Seq.index s m then 1 else 0))
  = Seq.lemma_eq_intro (Seq.slice s 0 (m + 1))
                       (Seq.append (Seq.slice s 0 m) (Seq.create 1 (Seq.index s m)));
    count_true_append (Seq.slice s 0 m) (Seq.create 1 (Seq.index s m));
    count_one (Seq.index s m)

let count_full (s: Seq.seq bool)
  : Lemma (count_true (Seq.slice s 0 (Seq.length s)) == count_true s)
  = Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s

(** {2 Rounding} *)

let ints_intro (#m: nat) (w: Seq.seq zqt { Seq.length w == m }) (r: Seq.lseq nat m)
  : Lemma (requires forall (t: nat). t < m ==> S32.v (Seq.index w t) == Seq.index r t)
          (ensures as_ints w == r)
  = as_ints_intro w r

let zqs_intro (#m: nat) (w: Seq.seq zqt { Seq.length w == m }) (r: Seq.lseq zq m)
  : Lemma (requires forall (t: nat). t < m ==> S32.v (Seq.index w t) == Seq.index r t)
          (ensures as_zqs w == r)
  = as_zqs_intro w r

let p2r_inv (vt w0 w1: Seq.seq zqt) (m: nat) : prop
  = m <= Seq.length vt /\ Seq.length w0 == Seq.length vt /\ Seq.length w1 == Seq.length vt /\
    (forall (u: nat). u < m ==>
       S32.v (Seq.index w0 u) == power2round_lo (S32.v (Seq.index vt u)) /\
       S32.v (Seq.index w1 u) == power2round_hi (S32.v (Seq.index vt u)) /\
       S32.v (Seq.index w1 u) < 1024) /\
    (forall (u: nat). m <= u /\ u < Seq.length vt ==> Seq.index w0 u == Seq.index vt u)

let p2r_step (vt w0 w1: Seq.seq zqt) (m: nat) (lo hi: zqt)
  : Lemma (requires p2r_inv vt w0 w1 m /\ m < Seq.length vt /\
                    S32.v lo == power2round_lo (S32.v (Seq.index w0 m)) /\
                    S32.v hi == power2round_hi (S32.v (Seq.index w0 m)) /\ S32.v hi < 1024)
          (ensures p2r_inv vt (Seq.upd w0 m lo) (Seq.upd w1 m hi) (m + 1))
  = ()

(** [t <- t0], [t1 <- t1]: Power2Round on every coefficient. *)
fn power2round_impl (t t1: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                    (#vt #v1: erased (Seq.seq zqt))
requires A.pts_to t vt ** A.pts_to t1 v1 **
         pure (vlen_ok k /\ Seq.length vt == SZ.v k * n /\ Seq.length v1 == SZ.v k * n)
ensures exists* w0 w1. A.pts_to t w0 ** A.pts_to t1 w1 **
  pure (vlen_ok k /\ Seq.length vt == SZ.v k * n /\
        Seq.length w0 == SZ.v k * n /\ Seq.length w1 == SZ.v k * n /\
        as_zqs w0 == vec_power2round_lo #(SZ.v k) (as_zqs vt) /\
        as_ints w1 == vec_power2round_hi #(SZ.v k) (as_zqs vt) /\
        (forall (i: nat). i < SZ.v k * n ==> S32.v (Seq.index w1 i) < 1024))
{
  A.pts_to_len t;
  A.pts_to_len t1;
  vlen_fits k;
  let len = SZ.mul k 256sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (w0 w1: Seq.seq zqt).
    pts_to i vi ** A.pts_to t w0 ** A.pts_to t1 w1 **
    pure (SZ.v vi <= SZ.v len /\ SZ.v len == SZ.v k * n /\ vlen_ok k /\
          Seq.length vt == SZ.v len /\ p2r_inv vt w0 w1 (SZ.v vi))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    with w0 w1. assert (A.pts_to t w0 ** A.pts_to t1 w1);
    let x = A.(t.(vi));
    let hi = p2r_hi x;
    let lo = p2r_lo x;
    assert_norm (1024 < q);
    p2r_step vt w0 w1 (SZ.v vi) lo hi;
    A.(t1.(vi) <- (hi <: zqt));
    A.(t.(vi) <- lo);
    i := SZ.add vi 1sz;
  };
  with w0 w1. assert (A.pts_to t w0 ** A.pts_to t1 w1);
  zqs_intro w0 (vec_power2round_lo #(SZ.v k) (as_zqs vt));
  ints_intro w1 (vec_power2round_hi #(SZ.v k) (as_zqs vt));
  ()
}

(** Coefficients below [m] of [w] agree with [r]. *)
let pw_inv (w: Seq.seq zqt) (r: Seq.seq nat) (m: nat) : prop
  = m <= Seq.length w /\ Seq.length r == Seq.length w /\
    (forall (u: nat). u < m ==> S32.v (Seq.index w u) == Seq.index r u)

let pw_zero (w: Seq.seq zqt) (r: Seq.seq nat)
  : Lemma (requires Seq.length r == Seq.length w) (ensures pw_inv w r 0) = ()

let pw_step (w: Seq.seq zqt) (r: Seq.seq nat) (m: nat) (x: zqt)
  : Lemma (requires pw_inv w r m /\ m < Seq.length w /\ S32.v x == Seq.index r m)
          (ensures pw_inv (Seq.upd w m x) r (m + 1))
  = ()

let pw_done (w: Seq.seq zqt) (r: Seq.seq nat)
  : Lemma (requires pw_inv w r (Seq.length w)) (ensures as_ints w == r)
  = as_ints_intro w r

let hint_bit_at (vh: Seq.seq S32.t) (u: nat)
  : Lemma (requires hint_bits vh /\ u < Seq.length vh)
          (ensures S32.v (Seq.index vh u) == 0 \/ S32.v (Seq.index vh u) == 1)
  = ()

(** [w1 <- HighBits(w)]. *)
fn high_bits_impl (w1 w: A.array zqt) (p: erased params) (gd: U32.t { g2_div_ok p gd })
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  (#v1: erased (Seq.seq zqt)) (#pw: perm) (#vw: erased (Seq.seq zqt))
requires A.pts_to w1 v1 ** A.pts_to w #pw vw **
         pure (vlen_ok k /\ Seq.length v1 == SZ.v k * n /\ Seq.length vw == SZ.v k * n)
ensures exists* r. A.pts_to w1 r ** A.pts_to w #pw vw **
  pure (vlen_ok k /\ Seq.length vw == SZ.v k * n /\ Seq.length r == SZ.v k * n /\
        as_ints r == vec_high_bits p #(SZ.v k) (as_zqs vw))
{
  A.pts_to_len w1;
  A.pts_to_len w;
  vlen_fits k;
  let len = SZ.mul k 256sz;
  let rs : erased (Seq.lseq nat (SZ.v k * n)) = vec_high_bits p #(SZ.v k) (as_zqs vw);
  pw_zero v1 rs;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (r: Seq.seq zqt).
    pts_to i vi ** A.pts_to w1 r ** A.pts_to w #pw vw **
    pure (SZ.v vi <= SZ.v len /\ SZ.v len == SZ.v k * n /\ vlen_ok k /\
          Seq.length vw == SZ.v len /\ pw_inv r rs (SZ.v vi))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    with r. assert (A.pts_to w1 r);
    let x = A.(w.(vi));
    gamma2_cases p;
    let h = high_bits_w #p gd x;
    assert (pure (Seq.index rs (SZ.v vi) == high_bits p (S32.v x)));
    pw_step r rs (SZ.v vi) h;
    A.(w1.(vi) <- (h <: zqt));
    i := SZ.add vi 1sz;
  };
  with r. assert (A.pts_to w1 r);
  pw_done r rs;
  ()
}

(** [w1 <- UseHint(h, w)]. *)
fn use_hint_impl (w1: A.array zqt) (h: A.array S32.t) (w: A.array zqt)
                 (p: erased params) (gd: U32.t { g2_div_ok p gd })
                 ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 (#v1: erased (Seq.seq zqt)) (#ph #pw: perm) (#vh: erased (Seq.seq S32.t))
                 (#vw: erased (Seq.seq zqt))
requires A.pts_to w1 v1 ** A.pts_to h #ph vh ** A.pts_to w #pw vw **
         pure (vlen_ok k /\ Seq.length v1 == SZ.v k * n /\ Seq.length vh == SZ.v k * n /\
               Seq.length vw == SZ.v k * n /\ hint_bits vh)
ensures exists* r. A.pts_to w1 r ** A.pts_to h #ph vh ** A.pts_to w #pw vw **
  pure (vlen_ok k /\ Seq.length vw == SZ.v k * n /\ Seq.length vh == SZ.v k * n /\
        Seq.length r == SZ.v k * n /\
        as_ints r == vec_use_hint p #(SZ.v k) (hint_view vh) (as_zqs vw))
{
  A.pts_to_len w1;
  A.pts_to_len h;
  A.pts_to_len w;
  vlen_fits k;
  let len = SZ.mul k 256sz;
  let rs : erased (Seq.lseq nat (SZ.v k * n)) = vec_use_hint p #(SZ.v k) (hint_view vh) (as_zqs vw);
  pw_zero v1 rs;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (r: Seq.seq zqt).
    pts_to i vi ** A.pts_to w1 r ** A.pts_to h #ph vh ** A.pts_to w #pw vw **
    pure (SZ.v vi <= SZ.v len /\ SZ.v len == SZ.v k * n /\ vlen_ok k /\ hint_bits vh /\
          Seq.length vw == SZ.v len /\ Seq.length vh == SZ.v len /\ pw_inv r rs (SZ.v vi))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    with r. assert (A.pts_to w1 r);
    let x = A.(w.(vi));
    let hb = A.(h.(vi));
    hint_bit_at vh (SZ.v vi);
    gamma2_cases p;
    let u = use_hint_w #p gd hb x;
    assert (pure (Seq.index rs (SZ.v vi) == use_hint p (S32.v hb = 1) (S32.v x)));
    pw_step r rs (SZ.v vi) u;
    A.(w1.(vi) <- (u <: zqt));
    i := SZ.add vi 1sz;
  };
  with r. assert (A.pts_to w1 r);
  pw_done r rs;
  ()
}

let mh_inv (hs: Seq.seq bool) (v: Seq.seq S32.t) (m: nat) (acc: nat) : prop
  = m <= Seq.length v /\ Seq.length hs == Seq.length v /\
    (forall (u: nat). u < m ==> bool_w (Seq.index hs u) (Seq.index v u)) /\
    acc == count_true (Seq.slice hs 0 m) /\ acc <= m

let mh_zero (hs: Seq.seq bool) (v: Seq.seq S32.t)
  : Lemma (requires Seq.length hs == Seq.length v) (ensures mh_inv hs v 0 0)
  = count_zero hs

let mh_step (hs: Seq.seq bool) (v: Seq.seq S32.t) (m: nat) (acc: nat) (b: S32.t)
  : Lemma (requires mh_inv hs v m acc /\ m < Seq.length v /\ bool_w (Seq.index hs m) b)
          (ensures mh_inv hs (Seq.upd v m b) (m + 1) (acc + S32.v b))
  = count_step hs m

let mh_done (hs: Seq.seq bool) (v: Seq.seq S32.t) (acc: nat)
  : Lemma (requires mh_inv hs v (Seq.length v) acc)
          (ensures hint_bits v /\ hint_view v == hs /\ acc == count_true (hint_view v))
  = Seq.lemma_eq_intro (hint_view v) hs;
    count_full hs

(** [h <- MakeHint(-ct0, r + ct0)], and the number of ones in it.  Only
    the count is declassified. *)
fn make_hint_impl (h: A.array S32.t) (ct0 r: A.array zqt) (p: erased params)
                  (gd: U32.t { g2_div_ok p gd })
                  ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                  (#vh: erased (Seq.seq S32.t)) (#pc #pr: perm) (#vc #vr: erased (Seq.seq zqt))
requires A.pts_to h vh ** A.pts_to ct0 #pc vc ** A.pts_to r #pr vr **
         pure (vlen_ok k /\ Seq.length vh == SZ.v k * n /\ Seq.length vc == SZ.v k * n /\
               Seq.length vr == SZ.v k * n)
returns cnt: U32.t
ensures exists* v. A.pts_to h v ** A.pts_to ct0 #pc vc ** A.pts_to r #pr vr **
  pure (vlen_ok k /\ Seq.length vc == SZ.v k * n /\ Seq.length vr == SZ.v k * n /\
        Seq.length v == SZ.v k * n /\ hint_bits v /\
        hint_view v == vec_make_hint p #(SZ.v k) (vec_map neg (as_zqs vc))
                                                 (vec_add (as_zqs vr) (as_zqs vc)) /\
        U32.v cnt == count_true (hint_view v))
{
  A.pts_to_len h;
  A.pts_to_len ct0;
  A.pts_to_len r;
  vlen_fits k;
  let len = SZ.mul k 256sz;
  let hs : erased (Seq.lseq bool (SZ.v k * n)) =
    vec_make_hint p #(SZ.v k) (vec_map neg (as_zqs vc)) (vec_add (as_zqs vr) (as_zqs vc));
  mh_zero hs vh;
  let mut i = 0sz;
  let mut acc = S32.zero;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (va: S32.t) (v: Seq.seq S32.t).
    pts_to i vi ** pts_to acc va ** A.pts_to h v ** A.pts_to ct0 #pc vc ** A.pts_to r #pr vr **
    pure (SZ.v vi <= SZ.v len /\ SZ.v len == SZ.v k * n /\ vlen_ok k /\
          Seq.length vc == SZ.v len /\ Seq.length vr == SZ.v len /\
          mh_inv hs v (SZ.v vi) (S32.v va))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to h v);
    let c = A.(ct0.(vi));
    let x = A.(r.(vi));
    let b = make_hint_w #p gd (zq_neg c) (zq_add x c);
    assert (pure (Seq.index hs (SZ.v vi) == make_hint p (S32.v (zq_neg c)) (S32.v (zq_add x c))));
    let va = !acc;
    mh_step hs v (SZ.v vi) (S32.v va) b;
    A.(h.(vi) <- b);
    Math.small_mod (S32.v va + S32.v b) (pow2 32);
    acc := S32.add_mod va b;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to h v);
  with va. assert (pts_to acc va);
  mh_done hs v (S32.v va);
  let va = !acc;
  Declassify.u32 va
}

(** {2 Norm checks} *)

let all_lt_upto (s: Seq.seq zqt) (m: nat) (b: nat) : prop
  = m <= Seq.length s /\ (forall (u: nat). u < m ==> norm (S32.v (Seq.index s u)) < b)

let all_lt_done (s: Seq.seq zqt) (b: nat)
  : Lemma (all_lt (as_zqs s) b <==> all_lt_upto s (Seq.length s) b)
  = all_lt_spec (as_zqs s) b

let acc_step (va mk: S32.t) (pm pm1: prop) (c: bool)
  : Lemma (requires (S32.v va == 0 \/ S32.v va == pow2 32 - 1) /\ (S32.v va == 0 <==> pm) /\
                    (c ==> S32.v mk == pow2 32 - 1) /\ (not c ==> S32.v mk == 0) /\
                    (pm1 <==> pm /\ not c))
          (ensures (S32.v mk == 0 \/ S32.v mk == pow2 32 - 1) /\
                   (S32.v (S32.select mk S32.ones va) == 0 \/
                    S32.v (S32.select mk S32.ones va) == pow2 32 - 1) /\
                   (S32.v (S32.select mk S32.ones va) == 0 <==> pm1))
  = ()

let all_lt_upto_step (s: Seq.seq zqt) (m: nat) (b: nat)
  : Lemma (requires m < Seq.length s)
          (ensures all_lt_upto s (m + 1) b <==>
                   all_lt_upto s m b /\ not (norm (S32.v (Seq.index s m)) >= b))
  = ()

(** [true] iff every coefficient of [v] has norm below [b]. *)
fn all_lt_impl (v: A.array zqt) (len: SZ.t) (b: S32.t { S32.v b <= half_q })
               (#pv: perm) (#vv: erased (Seq.seq zqt))
requires A.pts_to v #pv vv ** pure (Seq.length vv == SZ.v len)
returns ok: bool
ensures A.pts_to v #pv vv ** pure (ok == all_lt (as_zqs vv) (S32.v b))
{
  A.pts_to_len v;
  let mut i = 0sz;
  let mut acc = S32.zero;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (va: S32.t).
    pts_to i vi ** pts_to acc va ** A.pts_to v #pv vv **
    pure (SZ.v vi <= SZ.v len /\ Seq.length vv == SZ.v len /\
          (S32.v va == 0 \/ S32.v va == pow2 32 - 1) /\
          (S32.v va == 0 <==> all_lt_upto vv (SZ.v vi) (S32.v b)))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(v.(vi));
    let m = norm_ge_mask x b;
    let va = !acc;
    all_lt_upto_step vv (SZ.v vi) (S32.v b);
    acc_step va m (all_lt_upto vv (SZ.v vi) (S32.v b)) (all_lt_upto vv (SZ.v vi + 1) (S32.v b))
      (norm (S32.v x) >= S32.v b);
    acc := S32.select m S32.ones va;
    i := SZ.add vi 1sz;
  };
  let va = !acc;
  all_lt_done vv (S32.v b);
  U32.eq (Declassify.u32 va) 0ul
}

let low_lt_upto (p: params) (s: Seq.seq zqt) (m: nat) (b: nat) : prop
  = m <= Seq.length s /\ (forall (u: nat). u < m ==> norm (low_bits p (S32.v (Seq.index s u))) < b)

let low_lt_done (p: params) (k: pos) (s: Seq.seq zqt { Seq.length s == k * n }) (b: nat)
  : Lemma (all_lt (vec_low_bits p #k (as_zqs s)) b <==> low_lt_upto p s (k * n) b)
  = all_lt_spec (vec_low_bits p #k (as_zqs s)) b

let low_lt_upto_step (p: params) (s: Seq.seq zqt) (m: nat) (b: nat)
  : Lemma (requires m < Seq.length s)
          (ensures low_lt_upto p s (m + 1) b <==>
                   low_lt_upto p s m b /\ not (norm (low_bits p (S32.v (Seq.index s m))) >= b))
  = ()

(** [true] iff every coefficient of [LowBits(r)] has norm below [b]. *)
fn low_lt_impl (r: A.array zqt) (p: erased params) (gd: U32.t { g2_div_ok p gd })
               ([@@@FStar.Attributes.monomorphize] k: SZ.t)
               (b: S32.t { S32.v b <= half_q })
               (#pr: perm) (#vr: erased (Seq.seq zqt))
requires A.pts_to r #pr vr ** pure (vlen_ok k /\ Seq.length vr == SZ.v k * n)
returns ok: bool
ensures A.pts_to r #pr vr **
  pure (vlen_ok k /\ Seq.length vr == SZ.v k * n /\
        ok == all_lt (vec_low_bits p #(SZ.v k) (as_zqs vr)) (S32.v b))
{
  A.pts_to_len r;
  vlen_fits k;
  let len = SZ.mul k 256sz;
  let mut i = 0sz;
  let mut acc = S32.zero;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (va: S32.t).
    pts_to i vi ** pts_to acc va ** A.pts_to r #pr vr **
    pure (SZ.v vi <= SZ.v len /\ SZ.v len == SZ.v k * n /\ vlen_ok k /\
          Seq.length vr == SZ.v len /\
          (S32.v va == 0 \/ S32.v va == pow2 32 - 1) /\
          (S32.v va == 0 <==> low_lt_upto p vr (SZ.v vi) (S32.v b)))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(r.(vi));
    let lb = low_bits_w #p gd x;
    let m = norm_ge_mask lb b;
    let va = !acc;
    low_lt_upto_step p vr (SZ.v vi) (S32.v b);
    acc_step va m (low_lt_upto p vr (SZ.v vi) (S32.v b)) (low_lt_upto p vr (SZ.v vi + 1) (S32.v b))
      (norm (S32.v lb) >= S32.v b);
    acc := S32.select m S32.ones va;
    i := SZ.add vi 1sz;
  };
  let va = !acc;
  low_lt_done p (SZ.v k) vr (S32.v b);
  U32.eq (Declassify.u32 va) 0ul
}

(** {2 Verification} *)

(** [t1 <- t1 2^d], for [t1] coefficients below [2^10]. *)
fn t1_shift_impl (t1: A.array zqt) ([@@@FStar.Attributes.monomorphize] k: SZ.t)
                 (#vt: erased (Seq.seq zqt))
requires A.pts_to t1 vt **
         pure (vlen_ok k /\ Seq.length vt == SZ.v k * n /\
               (forall (i: nat). i < SZ.v k * n ==> S32.v (Seq.index vt i) < 1024))
ensures exists* w. A.pts_to t1 w **
  pure (vlen_ok k /\ Seq.length vt == SZ.v k * n /\ Seq.length w == SZ.v k * n /\
        (forall (i: nat). i < SZ.v k * n ==> S32.v (Seq.index w i) == S32.v (Seq.index vt i) * pow2 d))
{
  A.pts_to_len t1;
  vlen_fits k;
  let len = SZ.mul k 256sz;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (w: Seq.seq zqt).
    pts_to i vi ** A.pts_to t1 w **
    pure (SZ.v vi <= SZ.v len /\ SZ.v len == SZ.v k * n /\ vlen_ok k /\
          Seq.length vt == SZ.v len /\ Seq.length w == SZ.v len /\
          (forall (u: nat). u < SZ.v vi ==> S32.v (Seq.index w u) == S32.v (Seq.index vt u) * pow2 d) /\
          (forall (u: nat). SZ.v vi <= u /\ u < SZ.v len ==> Seq.index w u == Seq.index vt u))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(t1.(vi));
    assert_norm (pow2 13 == 8192 /\ 1023 * 8192 < q /\ q < pow2 32);
    Math.lemma_mult_le_right 8192 (S32.v x) 1023;
    Math.small_mod (S32.v x * pow2 13) (pow2 32);
    let y : zqt = S32.shift_left x 13ul;
    A.(t1.(vi) <- y);
    i := SZ.add vi 1sz;
  };
}

#pop-options
