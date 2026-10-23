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

(** Variable-time double-scalar multiplication, for verification.

    [point_mul_double o a k s] sets [o] to [[k]A + [s]G], up to
    [point_equal], with one doubling chain shared between the two scalars
    (Straus's trick).  Both scalars are written in unsigned sliding-window
    form: 256 digits, each zero or odd, with at least [w - 1] zeros after
    every nonzero one.  A rung doubles the accumulator and, for each
    scalar whose digit there is nonzero, adds the matching odd multiple:
    of [A] from a sixteen-entry table built at run time ([w = 5]), of [G]
    from the first table of the fixed-base comb, which holds [0..8]G and
    so serves [w = 3].

    Everything here is public: verification has no secrets.  The digits
    are declassified when they are read off the scalars, and every branch
    and table index below depends on them.  Nothing else may call this. *)
module Hacl.Ed25519.Straus

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Curve25519.Field
open Hacl.Curve25519.Field
open Hacl.Ed25519.Point

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module C = Spec.Curve25519
module E = Spec.Ed25519
module GR = Spec.Ed25519.Group
module SM = Spec.Ed25519.Smul
module G = Spec.Group.Smul
module ST = Spec.Ed25519.Straus
module CB = Spec.Ed25519.Comb
module CT = Spec.Ed25519.CombTable
module CE = Hacl.Ed25519.CombEnt
module CD = Hacl.Ed25519.CombData
module CDO = Hacl.Ed25519.CombDataOk
module CF = Hacl.Curve25519.Field
module B = Hacl.Spec.Bytes
module W = Hacl.Ed25519.PointWin
module MC = Hacl.Ed25519.PointMulComb
module GA = Pulse.Lib.GlobalArray
module Table = Hacl.Impl.Table
module Declassify = Hacl.Secret.Declassify
module Cast = FStar.Int.Cast
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module Mem = Hacl.Mem

(** {2 Digits} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** Every digit is zero or odd and below [2^w]. *)
let dgok (w: nat) (x: nat) : prop = x == 0 \/ (x % 2 == 1 /\ x < pow2 w)

[@@"opaque_to_smt"]
let dok (w: nat) (s: Seq.seq U8.t) : prop =
  Seq.length s == 256 /\ (forall (j: nat). j < 256 ==> dgok w (ST.dg s j))

let dok_intro (w: nat) (s: Seq.seq U8.t)
  : Lemma (requires Seq.length s == 256 /\
                    (forall (j: nat). j < 256 ==> dgok w (ST.dg s j)))
          (ensures dok w s)
  = reveal_opaque (`%dok) (dok w s)

let dok_get (w: nat) (s: Seq.seq U8.t) (j: nat)
  : Lemma (requires dok w s /\ j < 256)
          (ensures Seq.length s == 256 /\ dgok w (ST.dg s j) /\
                   ST.dg s j == U8.v (Seq.index s j))
  = reveal_opaque (`%dok) (dok w s)

let bit_ok (vk: Seq.lseq S8.t 32) (i: nat) (x: U8.t) (r: U8.t)
  : Lemma (requires i < 256 /\ U8.v x == S8.v (Seq.index vk (i / 8)) /\
                    U8.v r == (U8.v x / pow2 (i % 8)) % 2)
          (ensures U8.v r == G.gbit (B.le_nat vk) i)
  = SM.ith_bit_gbit vk i

let bits_done (s: Seq.seq U8.t) (vk: Seq.lseq S8.t 32)
  : Lemma (requires (forall (j: nat). j < 256 ==> ST.dg s j == G.gbit (B.le_nat vk) j))
          (ensures ST.dsum s ST.nd == B.le_nat vk)
  = ST.dsum_bits s (B.le_nat vk) 256;
    B.le_nat_bound vk;
    Math.small_mod (B.le_nat vk) (pow2 256)

let shl_one (t: U32.t)
  : Lemma (requires U32.v t < 7)
          (ensures U8.v (U8.shift_left 1uy t) == pow2 (U32.v t) /\ pow2 (U32.v t) < 128)
  = Math.pow2_lt_compat 7 (U32.v t);
    assert_norm (pow2 7 == 128);
    Math.small_mod (pow2 (U32.v t)) (pow2 8)

let pow2_succ (t: nat) : Lemma (pow2 (t + 1) == 2 * pow2 t) = Math.pow2_plus 1 t; assert_norm (pow2 1 == 2)

[@@"opaque_to_smt"]
let lo (w: nat) (s: Seq.seq U8.t) (i: nat) : prop =
  forall (j: nat). j < i ==> dgok w (ST.dg s j)

[@@"opaque_to_smt"]
let hi (s: Seq.seq U8.t) (i: nat) : prop =
  forall (j: nat). i <= j /\ j < 256 ==> ST.dg s j <= 1

let lo_zero (w: nat) (s: Seq.seq U8.t) : Lemma (lo w s 0)
  = reveal_opaque (`%lo) (lo w s 0)

let hi_init (s: Seq.seq U8.t)
  : Lemma (requires forall (j: nat). j < 256 ==> ST.dg s j <= 1) (ensures hi s 0)
  = reveal_opaque (`%hi) (hi s 0)

let hi_get (s: Seq.seq U8.t) (i: nat)
  : Lemma (requires hi s i /\ i < 256 /\ Seq.length s == 256)
          (ensures ST.dg s i <= 1 /\ ST.dg s i == U8.v (Seq.index s i) /\ hi s (i + 1))
  = reveal_opaque (`%hi) (hi s i); reveal_opaque (`%hi) (hi s (i + 1))

let lo_step (w: nat) (s: Seq.seq U8.t) (i: nat)
  : Lemma (requires lo w s i /\ dgok w (ST.dg s i)) (ensures lo w s (i + 1))
  = reveal_opaque (`%lo) (lo w s i); reveal_opaque (`%lo) (lo w s (i + 1))

let lo_done (w: nat) (s: Seq.seq U8.t)
  : Lemma (requires lo w s 256 /\ Seq.length s == 256) (ensures dok w s)
  = reveal_opaque (`%lo) (lo w s 256); dok_intro w s

let fold_ok (w: nat) (s s': Seq.seq U8.t) (i t: nat) (v: U8.t)
  : Lemma (requires Seq.length s == ST.nd /\ i + t < ST.nd /\ t > 0 /\
                    Seq.index s (i + t) <> 0uy /\ lo w s i /\ hi s (i + 1) /\
                    U8.v v == ST.dg s i + pow2 t /\
                    s' == Seq.upd (Seq.upd s i v) (i + t) 0uy)
          (ensures ST.dsum s' ST.nd == ST.dsum s ST.nd /\ Seq.length s' == ST.nd /\
                   ST.dg s' i == U8.v v /\ lo w s' i /\ hi s' (i + 1))
  = let x = Seq.index s (i + t) in
    if U8.v x = 0 then U8.v_inj x 0uy;
    assert (ST.dg s (i + t) == U8.v x);
    reveal_opaque (`%hi) (hi s (i + 1));
    assert (ST.dg s (i + t) <= 1);
    ST.dsum_fold s i t v;
    reveal_opaque (`%lo) (lo w s i); reveal_opaque (`%lo) (lo w s' i);
    reveal_opaque (`%hi) (hi s' (i + 1))

let odd_add (c t: nat)
  : Lemma (requires c % 2 == 1 /\ t > 0) (ensures (c + pow2 t) % 2 == 1)
  = Math.pow2_plus 1 (t - 1); assert_norm (pow2 1 == 2);
    Math.lemma_mod_plus c (pow2 (t - 1)) 2

let pow2_mono (a b: nat) : Lemma (requires a <= b) (ensures pow2 a <= pow2 b)
  = if a < b then Math.pow2_lt_compat b a

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [dst[j] := bit j of ks], as public bytes. *)
fn bits (dst: A.array U8.t) (ks: A.array S8.t)
        (#vd: erased (Seq.seq U8.t)) (#pk: perm) (#vk: erased (Seq.lseq S8.t 32))
requires A.pts_to dst vd ** A.pts_to ks #pk vk ** pure (Seq.length vd == 256)
ensures exists* (wd: Seq.seq U8.t).
  A.pts_to dst wd ** A.pts_to ks #pk vk **
  pure (Seq.length wd == 256 /\ ST.dsum wd ST.nd == B.le_nat vk /\
        (forall (j: nat). j < 256 ==> ST.dg wd j <= 1))
{
  A.pts_to_len dst; A.pts_to_len ks;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (wd: Seq.seq U8.t).
    pts_to i vi ** A.pts_to dst wd ** A.pts_to ks #pk vk **
    pure (SZ.v vi <= 256 /\ Seq.length wd == 256 /\
          (forall (j: nat). j < SZ.v vi ==> ST.dg wd j == G.gbit (B.le_nat vk) j))
  decreases (256 - SZ.v (!i))
  {
    let vi = !i;
    let bj = SZ.div vi 8sz;
    let sh = SZ.sizet_to_uint32 (SZ.rem vi 8sz);
    assert_norm (pow2 32 > 8);
    Math.small_mod (SZ.v (SZ.rem vi 8sz)) (pow2 32);
    let x = Declassify.u8 (A.(ks.(bj)));
    let r = U8.rem (U8.shift_right x sh) 2uy;
    bit_ok vk (SZ.v vi) x r;
    A.(dst.(vi) <- r);
    i := SZ.add vi 1sz;
  };
  with wd. assert (A.pts_to dst wd);
  bits_done wd vk;
  ()
}

(** Unsigned sliding-window recoding, in place.  Walking up, every one
    bit absorbs the one bits in the next [w - 1] places above it, which
    leaves it odd and below [2^w] and zeroes them.  Each absorption moves
    [2^(i+t)] from place [i + t] to place [i], so the value is unchanged
    throughout. *)
fn slide (d: A.array U8.t) (w: U32.t) (k: erased nat)
         (#vd: erased (Seq.seq U8.t))
requires A.pts_to d vd **
  pure (1 <= U32.v w /\ U32.v w <= 7 /\ Seq.length vd == 256 /\
        ST.dsum vd ST.nd == reveal k /\ (forall (j: nat). j < 256 ==> ST.dg vd j <= 1))
ensures exists* (wd: Seq.seq U8.t).
  A.pts_to d wd ** pure (dok (U32.v w) wd /\ ST.dsum wd ST.nd == reveal k)
{
  A.pts_to_len d;
  lo_zero (U32.v w) vd;
  hi_init vd;
  let mut i = 0sz;
  let mut t = 1ul;
  while (let vi = !i; SZ.lt vi 256sz)
  invariant exists* (vi: SZ.t) (vt0: U32.t) (wd: Seq.seq U8.t).
    pts_to i vi ** pts_to t vt0 ** A.pts_to d wd **
    pure (SZ.v vi <= 256 /\ Seq.length wd == 256 /\ ST.dsum wd ST.nd == reveal k /\
          lo (U32.v w) wd (SZ.v vi) /\ hi wd (SZ.v vi))
  decreases (256 - SZ.v (!i))
  {
    let vi = !i;
    with wd0. assert (A.pts_to d wd0);
    hi_get wd0 (SZ.v vi);
    let di = A.(d.(vi));
    if (di <> 0uy)
    ensures exists* (vt0: U32.t) (wd: Seq.seq U8.t).
      pts_to i vi ** pts_to t vt0 ** A.pts_to d wd **
      pure (Seq.length wd == 256 /\ ST.dsum wd ST.nd == reveal k /\
            lo (U32.v w) wd (SZ.v vi + 1) /\ hi wd (SZ.v vi + 1))
    {
      t := 1ul;
      assert_norm (pow2 1 == 2);
      while (let vt = !t; U32.lt vt w && SZ.lt (SZ.add vi (SZ.uint32_to_sizet vt)) 256sz)
      invariant exists* (vt: U32.t) (wd: Seq.seq U8.t).
        pts_to i vi ** pts_to t vt ** A.pts_to d wd **
        pure (SZ.v vi < 256 /\ 1 <= U32.v vt /\ U32.v vt <= U32.v w /\
              SZ.v vi + U32.v vt <= 256 /\
              Seq.length wd == 256 /\ ST.dsum wd ST.nd == reveal k /\
              lo (U32.v w) wd (SZ.v vi) /\ hi wd (SZ.v vi + 1) /\
              ST.dg wd (SZ.v vi) % 2 == 1 /\ ST.dg wd (SZ.v vi) < pow2 (U32.v vt))
      decreases (U32.v w - U32.v (!t))
      {
        let vt = !t;
        let at = SZ.add vi (SZ.uint32_to_sizet vt);
        let x = A.(d.(at));
        with wd. assert (A.pts_to d wd);
        pow2_succ (U32.v vt);
        if (x <> 0uy)
        ensures exists* (wd': Seq.seq U8.t).
          pts_to i vi ** pts_to t vt ** A.pts_to d wd' **
          pure (Seq.length wd' == 256 /\ ST.dsum wd' ST.nd == reveal k /\
                lo (U32.v w) wd' (SZ.v vi) /\ hi wd' (SZ.v vi + 1) /\
                ST.dg wd' (SZ.v vi) % 2 == 1 /\ ST.dg wd' (SZ.v vi) < pow2 (U32.v vt + 1))
        {
          let cur = A.(d.(vi));
          shl_one vt;
          let nv = U8.add cur (U8.shift_left 1uy vt);
          A.(d.(vi) <- nv);
          A.(d.(at) <- 0uy);
          odd_add (U8.v cur) (U32.v vt);
          with wd2. assert (A.pts_to d wd2);
          fold_ok (U32.v w) wd wd2 (SZ.v vi) (U32.v vt) nv;
          ()
        } else {
          ()
        };
        t := U32.add vt 1ul;
      };
      with vt. assert (pts_to t vt);
      with wd1. assert (A.pts_to d wd1);
      pow2_mono (U32.v vt) (U32.v w);
      lo_step (U32.v w) wd1 (SZ.v vi);
      ()
    } else {
      lo_step (U32.v w) wd0 (SZ.v vi);
      ()
    };
    i := SZ.add vi 1sz;
  };
  with wd. assert (A.pts_to d wd);
  lo_done (U32.v w) wd;
  ()
}

#pop-options

(** {2 The accumulator, over limbs}

    [sr x y z t na a b] is {!ST.st} read off four limb sequences, behind a
    name of its own for the reason {!W.rep} is: the step functions below
    then carry no field arithmetic in their contexts. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

[@@"opaque_to_smt"]
let sr (x y z t: Seq.seq S64.t) (na: E.ext_point) (a b: nat) : prop =
  ST.st (pt x y z t) na a b

let sr_zero (x y z t: Seq.seq S64.t) (na: E.ext_point)
  : Lemma (requires W.oc na /\ pt x y z t == E.point_at_infinity)
          (ensures sr x y z t na 0 0)
  = reveal_opaque (`%sr) (sr x y z t na 0 0);
    reveal_opaque (`%W.oc) (W.oc na);
    ST.st_zero na

let sr_cong (x y z t: Seq.seq S64.t) (na: E.ext_point) (a b a' b': nat)
  : Lemma (requires sr x y z t na a b /\ a == a' /\ b == b')
          (ensures sr x y z t na a' b')
  = ()

let sr_done (x y z t: Seq.seq S64.t) (na: E.ext_point) (a b: nat)
  : Lemma (requires sr x y z t na a b) (ensures ST.st (pt x y z t) na a b)
  = reveal_opaque (`%sr) (sr x y z t na a b)

let sr_dbl (ox oy oz ot wx wy wz wt: Seq.seq S64.t) (na: E.ext_point) (a b: nat)
  : Lemma (requires sr ox oy oz ot na a b /\
                    pt wx wy wz wt == E.point_double (pt ox oy oz ot))
          (ensures sr wx wy wz wt na (2 * a) (2 * b))
  = reveal_opaque (`%sr) (sr ox oy oz ot na a b);
    reveal_opaque (`%sr) (sr wx wy wz wt na (2 * a) (2 * b));
    ST.st_dbl (pt ox oy oz ot) na a b

let sr_adda (ox oy oz ot sx sy sz st wx wy wz wt: Seq.seq S64.t)
            (na: E.ext_point) (a b d: nat)
  : Lemma (requires sr ox oy oz ot na a b /\ W.rep sx sy sz st d na /\
                    pt wx wy wz wt == E.point_add (pt ox oy oz ot) (pt sx sy sz st))
          (ensures sr wx wy wz wt na (a + d) b)
  = reveal_opaque (`%sr) (sr ox oy oz ot na a b);
    reveal_opaque (`%sr) (sr wx wy wz wt na (a + d) b);
    W.rep_elim sx sy sz st d na;
    ST.st_adda (pt ox oy oz ot) na (pt sx sy sz st) a b d

let pow2_zero8 (m: nat) : Lemma (m * pow2 (8 * 0) == m) = assert_norm (pow2 (8 * 0) == 1)

(** Entry [m] of the comb's first table is [m]G, stored affine. *)
let tp0_ok (m: nat { m < 9 })
  : Lemma (CB.affine (CT.tp 0 m) /\ GR.on_curve (CT.tp 0 m) /\
           E.point_equal (CT.tp 0 m) (SM.smul m E.g))
  = CT.tp_ok 0 m;
    pow2_zero8 m;
    CB.isq_elim (CT.tp 0 m) (m * pow2 (8 * 0))

let sr_addb (ox oy oz ot wx wy wz wt va vb vc: Seq.seq S64.t)
            (na: E.ext_point) (a b: nat) (m: nat { m < 9 })
  : Lemma (requires sr ox oy oz ot na a b /\
                    (fev (vals va), fev (vals vb), fev (vals vc)) ==
                      CB.to_niels (CT.tp 0 m) /\
                    pt wx wy wz wt ==
                      CB.madd (pt ox oy oz ot) (fev (vals va), fev (vals vb), fev (vals vc)))
          (ensures sr wx wy wz wt na a (b + m))
  = let e = CT.tp 0 m in
    tp0_ok m;
    CB.madd_ok (pt ox oy oz ot) e;
    reveal_opaque (`%sr) (sr ox oy oz ot na a b);
    reveal_opaque (`%sr) (sr wx wy wz wt na a (b + m));
    ST.st_addb (pt ox oy oz ot) na e a b m

(** {2 The table of odd multiples}

    Entry [m] is [(2m + 1)]A, up to equivalence: the same bookkeeping as
    {!W.ent}, with the odd scale in place of [d n]. *)

[@@"opaque_to_smt"]
let oent (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (m: nat) : prop =
  W.pok (W.entry tx m) (W.entry ty m) (W.entry tz m) (W.entry tt m) /\
  W.rep (W.entry tx m) (W.entry ty m) (W.entry tz m) (W.entry tt m) (2 * m + 1) p

let oent_intro (tx ty tz tt sx sy sz st: Seq.seq S64.t) (p: E.ext_point) (m: nat)
  : Lemma (requires W.entry tx m == sx /\ W.entry ty m == sy /\
                    W.entry tz m == sz /\ W.entry tt m == st /\
                    W.pok sx sy sz st /\ W.rep sx sy sz st (2 * m + 1) p)
          (ensures oent tx ty tz tt p m)
  = reveal_opaque (`%oent) oent

let oent_eq (tx ty tz tt tx' ty' tz' tt': Seq.seq S64.t) (p: E.ext_point) (m: nat)
  : Lemma (requires oent tx ty tz tt p m /\ W.entry tx' m == W.entry tx m /\
                    W.entry ty' m == W.entry ty m /\ W.entry tz' m == W.entry tz m /\
                    W.entry tt' m == W.entry tt m)
          (ensures oent tx' ty' tz' tt' p m)
  = reveal_opaque (`%oent) oent

let otok (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (upto: nat) : prop =
  forall (m: nat). m < upto ==> oent tx ty tz tt p m

let otok_zero (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) : Lemma (otok tx ty tz tt p 0)
  = ()

let otok_get (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (m: nat)
  : Lemma (requires otok tx ty tz tt p 16 /\ m < 16)
          (ensures W.pok (W.entry tx m) (W.entry ty m) (W.entry tz m) (W.entry tt m) /\
                   W.rep (W.entry tx m) (W.entry ty m) (W.entry tz m) (W.entry tt m)
                         (2 * m + 1) p)
  = reveal_opaque (`%oent) oent

let oent_same (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (e m: nat)
  : Lemma (requires oent tx ty tz tt p e /\ m == e) (ensures oent tx ty tz tt p m)
  = ()

#push-options "--ifuel 1 --z3rlimit 100"
let otok_extend (tx ty tz tt tx' ty' tz' tt': Seq.seq S64.t) (p: E.ext_point) (e: nat)
  : Lemma (requires otok tx ty tz tt p e /\ e < 16 /\ oent tx' ty' tz' tt' p e /\
                    (forall (m: nat). m < e ==>
                       (W.entry tx' m == W.entry tx m /\ W.entry ty' m == W.entry ty m /\
                        W.entry tz' m == W.entry tz m /\ W.entry tt' m == W.entry tt m)))
          (ensures otok tx' ty' tz' tt' p (e + 1))
  = introduce forall (m: nat). m < e + 1 ==> oent tx' ty' tz' tt' p m
    with introduce _ ==> _
    with (if m < e then oent_eq tx ty tz tt tx' ty' tz' tt' p m
                   else oent_same tx' ty' tz' tt' p e m)
#pop-options

let odd_next (a: nat) : Lemma (2 * a + 1 + 2 == 2 * (a + 1) + 1) = ()

let sz_sixteen (x: SZ.t) : Lemma (requires SZ.lt x 16sz == false /\ SZ.v x <= 16)
                                 (ensures SZ.v x == 16) = ()

(** An odd digit below [2^w] is [2m + 1] for an [m] below [2^(w-1)]. *)
let half_ok (x: nat) (w: pos)
  : Lemma (requires x % 2 == 1 /\ x < pow2 w)
          (ensures 2 * (x / 2) + 1 == x /\ x / 2 < pow2 (w - 1))
  = Math.pow2_plus 1 (w - 1); assert_norm (pow2 1 == 2)

let dok_digit (w: nat) (s: Seq.seq U8.t) (j: nat)
  : Lemma (requires dok w s /\ j < 256)
          (ensures Seq.length s == 256 /\ ST.dg s j == U8.v (Seq.index s j) /\
                   (Seq.index s j <> 0uy ==> (U8.v (Seq.index s j) % 2 == 1 /\
                                              U8.v (Seq.index s j) < pow2 w)))
  = dok_get w s j;
    let x = Seq.index s j in
    if U8.v x = 0 then U8.v_inj x 0uy

#pop-options

(** {2 Moving limbs} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [dst := src[off .. off + 5]], with an index that is public. *)
inline_for_extraction
fn load5 (dst: A.array S64.t) (src: A.array S64.t) (off: SZ.t)
         (#vd: erased (Seq.seq S64.t)) (#ps: perm) (#vs: erased (Seq.seq S64.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
  pure (Seq.length vd == 5 /\ SZ.v off + 5 <= Seq.length vs /\ SZ.fits (SZ.v off + 5))
ensures exists* (w: Seq.seq S64.t).
  A.pts_to dst w ** A.pts_to src #ps vs **
  pure (SZ.v off + 5 <= Seq.length vs /\ w == Seq.slice vs (SZ.v off) (SZ.v off + 5))
{
  A.pts_to_len dst; A.pts_to_len src;
  let x0 = A.(src.(off));
  let x1 = A.(src.(SZ.add off 1sz));
  let x2 = A.(src.(SZ.add off 2sz));
  let x3 = A.(src.(SZ.add off 3sz));
  let x4 = A.(src.(SZ.add off 4sz));
  A.(dst.(0sz) <- x0);
  A.(dst.(1sz) <- x1);
  A.(dst.(2sz) <- x2);
  A.(dst.(3sz) <- x3);
  A.(dst.(4sz) <- x4);
  with w. assert (A.pts_to dst w);
  Seq.lemma_eq_intro w (Seq.slice vs (SZ.v off) (SZ.v off + 5));
  ()
}

#pop-options

(** {2 Building the table} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** [odd_table t q p] fills the sixteen entries with [Q, 3Q, .., 31Q],
    where [Q] is [P] itself. *)
fn odd_table (tx ty tz tt: A.array S64.t) (qx qy qz qt: A.array S64.t)
             (p: erased E.ext_point)
             (#vtx #vty #vtz #vtt: erased (Seq.seq S64.t))
             (#pq: perm) (#vqx #vqy #vqz #vqt: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz ** A.pts_to tt vtt **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
  A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
  pure (Seq.length vtx == 80 /\ Seq.length vty == 80 /\
        Seq.length vtz == 80 /\ Seq.length vtt == 80 /\
        W.pok vqx vqy vqz vqt /\ W.oc (reveal p) /\
        W.rep vqx vqy vqz vqt 1 (reveal p))
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz ** A.pts_to tt wt **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
  A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
  pure (Seq.length wx == 80 /\ Seq.length wy == 80 /\
        Seq.length wz == 80 /\ Seq.length wt == 80 /\
        otok wx wy wz wt (reveal p) 16)
{
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz; A.pts_to_len tt;
  W.pok_elim vqx vqy vqz vqt;
  let z = S64.zero;
  let mut cx = [| z; 5sz |];
  Mem.track cx; A.pts_to_len cx;
  let mut cy = [| z; 5sz |];
  Mem.track cy; A.pts_to_len cy;
  let mut cz = [| z; 5sz |];
  Mem.track cz; A.pts_to_len cz;
  let mut ct = [| z; 5sz |];
  Mem.track ct; A.pts_to_len ct;
  let mut dx = [| z; 5sz |];
  Mem.track dx; A.pts_to_len dx;
  let mut dy = [| z; 5sz |];
  Mem.track dy; A.pts_to_len dy;
  let mut dz = [| z; 5sz |];
  Mem.track dz; A.pts_to_len dz;
  let mut dt = [| z; 5sz |];
  Mem.track dt; A.pts_to_len dt;
  let mut nx = [| z; 5sz |];
  Mem.track nx; A.pts_to_len nx;
  let mut ny = [| z; 5sz |];
  Mem.track ny; A.pts_to_len ny;
  let mut nz = [| z; 5sz |];
  Mem.track nz; A.pts_to_len nz;
  let mut nt = [| z; 5sz |];
  Mem.track nt; A.pts_to_len nt;
  A.pts_to_len cx; A.pts_to_len cy; A.pts_to_len cz; A.pts_to_len ct;
  A.pts_to_len dx; A.pts_to_len dy; A.pts_to_len dz; A.pts_to_len dt;
  A.pts_to_len nx; A.pts_to_len ny; A.pts_to_len nz; A.pts_to_len nt;

  CF.copy cx qx; CF.copy cy qy; CF.copy cz qz; CF.copy ct qt;
  point_double dx dy dz dt qx qy qz qt;
  with d0x d0y d0z d0t.
    assert (A.pts_to dx d0x ** A.pts_to dy d0y ** A.pts_to dz d0z ** A.pts_to dt d0t);
  W.dbl_ok vqx vqy vqz vqt d0x d0y d0z d0t (reveal p) 1;
  W.pok_intro d0x d0y d0z d0t;
  W.pok_elim d0x d0y d0z d0t;
  otok_zero vtx vty vtz vtt (reveal p);

  let mut m = 0sz;
  while (let vm = !m; SZ.lt vm 16sz)
  invariant exists* (vm: SZ.t)
                    (wx wy wz wt wcx wcy wcz wct wnx wny wnz wnt: Seq.seq S64.t).
    pts_to m vm **
    A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz ** A.pts_to tt wt **
    A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz ** A.pts_to ct wct **
    A.pts_to dx d0x ** A.pts_to dy d0y ** A.pts_to dz d0z ** A.pts_to dt d0t **
    A.pts_to nx wnx ** A.pts_to ny wny ** A.pts_to nz wnz ** A.pts_to nt wnt **
    A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
    A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
    pure (SZ.v vm <= 16 /\
          Seq.length wx == 80 /\ Seq.length wy == 80 /\
          Seq.length wz == 80 /\ Seq.length wt == 80 /\
          Seq.length wnx == nl /\ Seq.length wny == nl /\
          Seq.length wnz == nl /\ Seq.length wnt == nl /\
          W.pok wcx wcy wcz wct /\
          W.rep wcx wcy wcz wct (2 * SZ.v vm + 1) (reveal p) /\
          otok wx wy wz wt (reveal p) (SZ.v vm))
  decreases (16 - SZ.v (!m))
  {
    let vm = !m;
    with wx wy wz wt.
      assert (A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz ** A.pts_to tt wt);
    with wcx wcy wcz wct.
      assert (A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz ** A.pts_to ct wct);
    W.pok_elim wcx wcy wcz wct;
    W.store_off (SZ.v vm);
    W.store4 tx ty tz tt cx cy cz ct (SZ.mul vm 5sz);
    with wx' wy' wz' wt'.
      assert (A.pts_to tx wx' ** A.pts_to ty wy' ** A.pts_to tz wz' ** A.pts_to tt wt');
    W.tbl_shape wx wx' wcx (SZ.v vm);
    W.tbl_shape wy wy' wcy (SZ.v vm);
    W.tbl_shape wz wz' wcz (SZ.v vm);
    W.tbl_shape wt wt' wct (SZ.v vm);
    oent_intro wx' wy' wz' wt' wcx wcy wcz wct (reveal p) (SZ.v vm);
    otok_extend wx wy wz wt wx' wy' wz' wt' (reveal p) (SZ.v vm);
    point_add nx ny nz nt cx cy cz ct dx dy dz dt;
    with wnx wny wnz wnt.
      assert (A.pts_to nx wnx ** A.pts_to ny wny ** A.pts_to nz wnz ** A.pts_to nt wnt);
    W.add_ok wcx wcy wcz wct d0x d0y d0z d0t wnx wny wnz wnt
             (reveal p) (2 * SZ.v vm + 1) 2;
    odd_next (SZ.v vm);
    W.rep_cong wnx wny wnz wnt (2 * SZ.v vm + 1 + 2) (2 * (SZ.v vm + 1) + 1) (reveal p);
    W.pok_intro wnx wny wnz wnt;
    CF.copy cx nx; CF.copy cy ny; CF.copy cz nz; CF.copy ct nt;
    m := SZ.add vm 1sz;
  };
  let vm = !m;
  sz_sixteen vm;
  Mem.wipe nt 5sz;
  Mem.wipe nz 5sz;
  Mem.wipe ny 5sz;
  Mem.wipe nx 5sz;
  Mem.wipe dt 5sz;
  Mem.wipe dz 5sz;
  Mem.wipe dy 5sz;
  Mem.wipe dx 5sz;
  Mem.wipe ct 5sz;
  Mem.wipe cz 5sz;
  Mem.wipe cy 5sz;
  Mem.wipe cx 5sz;
  ()
}

#pop-options

(** {2 The three steps}

    Each is behind a contract of its own that mentions only the opaque
    {!sr}, so that a rung's context carries none of the curve. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** [o := 2 o], through the scratch [u]. *)
fn s_dbl (ox oy oz ot ux uy uz ut: A.array S64.t)
         (na: erased E.ext_point) (a b: erased nat)
         (#vox #voy #voz #vot: erased (Seq.seq S64.t))
         (#vux #vuy #vuz #vut: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz ** A.pts_to ut vut **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\
        Seq.length vuz == nl /\ Seq.length vut == nl /\
        W.pok vox voy voz vot /\ sr vox voy voz vot na a b)
ensures exists* (wx wy wz wt wux wuy wuz wut: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\
        Seq.length wuz == nl /\ Seq.length wut == nl /\
        W.pok wx wy wz wt /\ sr wx wy wz wt na (2 * reveal a) (2 * reveal b))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz; A.pts_to_len ut;
  W.pok_elim vox voy voz vot;
  point_double ux uy uz ut ox oy oz ot;
  with u1x u1y u1z u1t.
    assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z ** A.pts_to ut u1t);
  sr_dbl vox voy voz vot u1x u1y u1z u1t na a b;
  W.pok_intro u1x u1y u1z u1t;
  CF.copy ox ux; CF.copy oy uy; CF.copy oz uz; CF.copy ot ut;
  ()
}

(** [o := o + (2m + 1) A], from the odd table. *)
fn s_adda (ox oy oz ot ux uy uz ut sx sy sz st: A.array S64.t)
          (tx ty tz tt: A.array S64.t) (m: SZ.t)
          (na: erased E.ext_point) (a b: erased nat)
          (#vox #voy #voz #vot: erased (Seq.seq S64.t))
          (#vux #vuy #vuz #vut: erased (Seq.seq S64.t))
          (#vsx #vsy #vsz #vst: erased (Seq.seq S64.t))
          (#ptb: perm) (#vtx #vty #vtz #vtt: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz ** A.pts_to ut vut **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz ** A.pts_to st vst **
  A.pts_to tx #ptb vtx ** A.pts_to ty #ptb vty **
  A.pts_to tz #ptb vtz ** A.pts_to tt #ptb vtt **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\
        Seq.length vuz == nl /\ Seq.length vut == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\
        Seq.length vsz == nl /\ Seq.length vst == nl /\
        Seq.length vtx == 80 /\ Seq.length vty == 80 /\
        Seq.length vtz == 80 /\ Seq.length vtt == 80 /\
        SZ.v m < 16 /\ otok vtx vty vtz vtt na 16 /\
        W.pok vox voy voz vot /\ sr vox voy voz vot na a b)
ensures exists* (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
  A.pts_to tx #ptb vtx ** A.pts_to ty #ptb vty **
  A.pts_to tz #ptb vtz ** A.pts_to tt #ptb vtt **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\
        Seq.length wuz == nl /\ Seq.length wut == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\
        Seq.length wsz == nl /\ Seq.length wst == nl /\
        W.pok wx wy wz wt /\
        sr wx wy wz wt na (reveal a + (2 * SZ.v m + 1)) b)
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz; A.pts_to_len ut;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz; A.pts_to_len st;
  W.store_off (SZ.v m);
  W.entry_def vtx (SZ.v m); W.entry_def vty (SZ.v m);
  W.entry_def vtz (SZ.v m); W.entry_def vtt (SZ.v m);
  let off = SZ.mul m 5sz;
  load5 sx tx off;
  load5 sy ty off;
  load5 sz tz off;
  load5 st tt off;
  otok_get vtx vty vtz vtt na (SZ.v m);
  with wsx wsy wsz wst.
    assert (A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst);
  W.pok_elim wsx wsy wsz wst;
  W.pok_elim vox voy voz vot;
  point_add ux uy uz ut ox oy oz ot sx sy sz st;
  with u1x u1y u1z u1t.
    assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z ** A.pts_to ut u1t);
  sr_adda vox voy voz vot wsx wsy wsz wst u1x u1y u1z u1t na a b (2 * SZ.v m + 1);
  W.pok_intro u1x u1y u1z u1t;
  CF.copy ox ux; CF.copy oy uy; CF.copy oz uz; CF.copy ot ut;
  ()
}

let eoff0 (m: nat) : Lemma (CE.eoff 0 m == 15 * m) = ()

(** [o := o + m G], from the comb's first table, by mixed addition. *)
fn s_addb (ox oy oz ot pa pb pc: A.array S64.t) (tbl: A.array S64.t) (m: SZ.t)
          (na: erased E.ext_point) (a b: erased nat)
          (#vox #voy #voz #vot: erased (Seq.seq S64.t))
          (#va #vb #vc: erased (Seq.seq S64.t))
          (#ptb: perm) (#vtb: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to pa va ** A.pts_to pb vb ** A.pts_to pc vc **
  A.pts_to tbl #ptb vtb **
  pure (Seq.length va == nl /\ Seq.length vb == nl /\ Seq.length vc == nl /\
        SZ.v m < 9 /\ MC.tok vtb /\
        W.pok vox voy voz vot /\ sr vox voy voz vot na a b)
ensures exists* (wx wy wz wt wa wb wc: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to pa wa ** A.pts_to pb wb ** A.pts_to pc wc **
  A.pts_to tbl #ptb vtb **
  pure (Seq.length wa == nl /\ Seq.length wb == nl /\ Seq.length wc == nl /\
        W.pok wx wy wz wt /\ sr wx wy wz wt na a (reveal b + SZ.v m))
{
  A.pts_to_len pa; A.pts_to_len pb; A.pts_to_len pc;
  MC.tok_len vtb;
  eoff0 (SZ.v m);
  let off = SZ.mul m 15sz;
  load5 pa tbl off;
  load5 pb tbl (SZ.add off 5sz);
  load5 pc tbl (SZ.add off 10sz);
  with wa wb wc. assert (A.pts_to pa wa ** A.pts_to pb wb ** A.pts_to pc wc);
  MC.ent_ok vtb 0 (SZ.v m) wa wb wc;
  W.pok_elim vox voy voz vot;
  MC.madd ox oy oz ot pa pb pc;
  with wx wy wz wt.
    assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt);
  sr_addb vox voy voz vot wx wy wz wt wa wb wc na a b (SZ.v m);
  W.pok_intro wx wy wz wt;
  ()
}

#pop-options

(** {2 The chain} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let rung_a (da: Seq.seq U8.t) (j: nat) (a2 m: nat)
  : Lemma (requires j < ST.nd /\ a2 == 2 * ST.hsum da (j + 1) /\ ST.dg da j == 2 * m + 1)
          (ensures a2 + (2 * m + 1) == ST.hsum da j)
  = ST.hsum_step da j

let rung_b (db: Seq.seq U8.t) (j: nat) (b2 m: nat)
  : Lemma (requires j < ST.nd /\ b2 == 2 * ST.hsum db (j + 1) /\ ST.dg db j == m)
          (ensures b2 + m == ST.hsum db j)
  = ST.hsum_step db j

let digit_a (x: U8.t)
  : Lemma (requires U8.v x % 2 == 1 /\ U8.v x < pow2 5)
          (ensures 2 * (U8.v x / 2) + 1 == U8.v x /\ U8.v x / 2 < 16)
  = half_ok (U8.v x) 5; assert_norm (pow2 4 == 16)

let digit_b (x: U8.t)
  : Lemma (requires U8.v x < pow2 3) (ensures U8.v x < 9)
  = assert_norm (pow2 3 == 8)

(** One rung: double, then add the two digits at [j]. *)
fn rung (ox oy oz ot ux uy uz ut sx sy sz st: A.array S64.t)
        (tx ty tz tt: A.array S64.t) (tbl: A.array S64.t)
        (da db: A.array U8.t) (j: SZ.t) (na: erased E.ext_point)
        (#vox #voy #voz #vot: erased (Seq.seq S64.t))
        (#vux #vuy #vuz #vut: erased (Seq.seq S64.t))
        (#vsx #vsy #vsz #vst: erased (Seq.seq S64.t))
        (#ptt: perm) (#vtx #vty #vtz #vtt: erased (Seq.seq S64.t))
        (#ptb: perm) (#vtb: erased (Seq.seq S64.t))
        (#vda #vdb: erased (Seq.seq U8.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz ** A.pts_to ut vut **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz ** A.pts_to st vst **
  A.pts_to tx #ptt vtx ** A.pts_to ty #ptt vty **
  A.pts_to tz #ptt vtz ** A.pts_to tt #ptt vtt **
  A.pts_to tbl #ptb vtb ** A.pts_to da vda ** A.pts_to db vdb **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\
        Seq.length vuz == nl /\ Seq.length vut == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\
        Seq.length vsz == nl /\ Seq.length vst == nl /\
        Seq.length vtx == 80 /\ Seq.length vty == 80 /\
        Seq.length vtz == 80 /\ Seq.length vtt == 80 /\
        otok vtx vty vtz vtt na 16 /\ MC.tok vtb /\
        SZ.v j < 256 /\ dok 5 vda /\ dok 3 vdb /\
        W.pok vox voy voz vot /\
        sr vox voy voz vot na (ST.hsum vda (SZ.v j + 1)) (ST.hsum vdb (SZ.v j + 1)))
ensures exists* (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
  A.pts_to tx #ptt vtx ** A.pts_to ty #ptt vty **
  A.pts_to tz #ptt vtz ** A.pts_to tt #ptt vtt **
  A.pts_to tbl #ptb vtb ** A.pts_to da vda ** A.pts_to db vdb **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\
        Seq.length wuz == nl /\ Seq.length wut == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\
        Seq.length wsz == nl /\ Seq.length wst == nl /\
        W.pok wx wy wz wt /\
        sr wx wy wz wt na (ST.hsum vda (SZ.v j)) (ST.hsum vdb (SZ.v j)))
{
  let a1 : erased nat = hide (ST.hsum vda (SZ.v j + 1));
  let b1 : erased nat = hide (ST.hsum vdb (SZ.v j + 1));
  s_dbl ox oy oz ot ux uy uz ut na a1 b1;
  dok_digit 5 vda (SZ.v j);
  dok_digit 3 vdb (SZ.v j);
  let x = A.(da.(j));
  if (x <> 0uy)
  ensures exists* (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
    A.pts_to tx #ptt vtx ** A.pts_to ty #ptt vty **
    A.pts_to tz #ptt vtz ** A.pts_to tt #ptt vtt **
    A.pts_to tbl #ptb vtb ** A.pts_to da vda ** A.pts_to db vdb **
    pure (Seq.length wux == nl /\ Seq.length wuy == nl /\
          Seq.length wuz == nl /\ Seq.length wut == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\
          Seq.length wsz == nl /\ Seq.length wst == nl /\
          W.pok wx wy wz wt /\
          sr wx wy wz wt na (ST.hsum vda (SZ.v j)) (2 * reveal b1))
  {
    digit_a x;
    let m = SZ.uint32_to_sizet (Cast.uint8_to_uint32 (U8.div x 2uy));
    s_adda ox oy oz ot ux uy uz ut sx sy sz st tx ty tz tt m na
           (hide (2 * reveal a1)) (hide (2 * reveal b1));
    with wx wy wz wt.
      assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt);
    rung_a vda (SZ.v j) (2 * reveal a1) (SZ.v m);
    sr_cong wx wy wz wt na (2 * reveal a1 + (2 * SZ.v m + 1)) (2 * reveal b1)
            (ST.hsum vda (SZ.v j)) (2 * reveal b1);
    ()
  } else {
    with wx wy wz wt.
      assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt);
    ST.hsum_step vda (SZ.v j);
    sr_cong wx wy wz wt na (2 * reveal a1) (2 * reveal b1)
            (ST.hsum vda (SZ.v j)) (2 * reveal b1);
    ()
  };
  let y = A.(db.(j));
  if (y <> 0uy)
  ensures exists* (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
    A.pts_to tx #ptt vtx ** A.pts_to ty #ptt vty **
    A.pts_to tz #ptt vtz ** A.pts_to tt #ptt vtt **
    A.pts_to tbl #ptb vtb ** A.pts_to da vda ** A.pts_to db vdb **
    pure (Seq.length wux == nl /\ Seq.length wuy == nl /\
          Seq.length wuz == nl /\ Seq.length wut == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\
          Seq.length wsz == nl /\ Seq.length wst == nl /\
          W.pok wx wy wz wt /\
          sr wx wy wz wt na (ST.hsum vda (SZ.v j)) (ST.hsum vdb (SZ.v j)))
  {
    digit_b y;
    let m = SZ.uint32_to_sizet (Cast.uint8_to_uint32 y);
    s_addb ox oy oz ot sx sy sz tbl m na
           (hide (ST.hsum vda (SZ.v j))) (hide (2 * reveal b1));
    with wx wy wz wt.
      assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt);
    rung_b vdb (SZ.v j) (2 * reveal b1) (SZ.v m);
    sr_cong wx wy wz wt na (ST.hsum vda (SZ.v j)) (2 * reveal b1 + SZ.v m)
            (ST.hsum vda (SZ.v j)) (ST.hsum vdb (SZ.v j));
    ()
  } else {
    with wx wy wz wt.
      assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt);
    ST.hsum_step vdb (SZ.v j);
    sr_cong wx wy wz wt na (ST.hsum vda (SZ.v j)) (2 * reveal b1)
            (ST.hsum vda (SZ.v j)) (ST.hsum vdb (SZ.v j));
    ()
  };
  ()
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

let sz_zero (x: SZ.t) : Lemma (requires SZ.gt x 0sz == false) (ensures SZ.v x == 0) = ()

(** [point_mul_double o a kk ks] is [o := [kk]A + [ks]G], up to
    [point_equal]. *)
fn point_mul_double (ox oy oz ot: A.array S64.t) (ax ay az at: A.array S64.t)
                    (kk ks: A.array S8.t)
                    (#vox #voy #voz #vot: erased (Seq.seq S64.t))
                    (#pa: perm) (#vax #vay #vaz #vat: erased (Seq.seq S64.t))
                    (#pk1: perm) (#vk1: erased (Seq.lseq S8.t 32))
                    (#pk2: perm) (#vk2: erased (Seq.lseq S8.t 32))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ax #pa vax ** A.pts_to ay #pa vay **
  A.pts_to az #pa vaz ** A.pts_to at #pa vat **
  A.pts_to kk #pk1 vk1 ** A.pts_to ks #pk2 vk2 **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl /\
        pt_ok vax vay vaz vat /\ GR.on_curve (pt vax vay vaz vat))
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ax #pa vax ** A.pts_to ay #pa vay **
  A.pts_to az #pa vaz ** A.pts_to at #pa vat **
  A.pts_to kk #pk1 vk1 ** A.pts_to ks #pk2 vk2 **
  pure (pt_ok wx wy wz wt /\
        ST.st (pt wx wy wz wt) (pt vax vay vaz vat) (B.le_nat vk1) (B.le_nat vk2))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  let na : erased E.ext_point = hide (pt vax vay vaz vat);
  W.oc_intro (pt vax vay vaz vat);
  W.pok_intro vax vay vaz vat;
  W.rep_one vax vay vaz vat;

  (* The digits. *)
  let mut da = [| 0uy; 256sz |];
  Mem.track da; A.pts_to_len da;
  let mut db = [| 0uy; 256sz |];
  Mem.track db; A.pts_to_len db;
  bits da kk;
  slide da 5ul (hide (B.le_nat vk1));
  bits db ks;
  slide db 3ul (hide (B.le_nat vk2));
  with vda. assert (A.pts_to da vda);
  with vdb. assert (A.pts_to db vdb);

  (* The odd multiples of A. *)
  let z = S64.zero;
  let mut tx = [| z; 80sz |];
  Mem.track tx; A.pts_to_len tx;
  let mut ty = [| z; 80sz |];
  Mem.track ty; A.pts_to_len ty;
  let mut tz = [| z; 80sz |];
  Mem.track tz; A.pts_to_len tz;
  let mut tt = [| z; 80sz |];
  Mem.track tt; A.pts_to_len tt;
  odd_table tx ty tz tt ax ay az at na;

  let mut ux = [| z; 5sz |];
  Mem.track ux; A.pts_to_len ux;
  let mut uy = [| z; 5sz |];
  Mem.track uy; A.pts_to_len uy;
  let mut uz = [| z; 5sz |];
  Mem.track uz; A.pts_to_len uz;
  let mut ut = [| z; 5sz |];
  Mem.track ut; A.pts_to_len ut;
  let mut sx = [| z; 5sz |];
  Mem.track sx; A.pts_to_len sx;
  let mut sy = [| z; 5sz |];
  Mem.track sy; A.pts_to_len sy;
  let mut sz = [| z; 5sz |];
  Mem.track sz; A.pts_to_len sz;
  let mut st = [| z; 5sz |];
  Mem.track st; A.pts_to_len st;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz; A.pts_to_len ut;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz; A.pts_to_len st;

  CDO.tbl_ok ();
  MC.tok_intro (GA.static_array_elems CD.tbl_arr);
  let tbl = Table.table CD.tbl_arr 4320sz;

  set_infinity ox oy oz ot;
  with o0x o0y o0z o0t.
    assert (A.pts_to ox o0x ** A.pts_to oy o0y ** A.pts_to oz o0z ** A.pts_to ot o0t);
  W.pok_intro o0x o0y o0z o0t;
  sr_zero o0x o0y o0z o0t na;
  ST.hsum_top vda; ST.hsum_top vdb;
  sr_cong o0x o0y o0z o0t na 0 0 (ST.hsum vda 256) (ST.hsum vdb 256);

  let mut i = 256sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t)
                    (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst: Seq.seq S64.t).
    pts_to i vi **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
    pure (SZ.v vi <= 256 /\
          Seq.length wux == nl /\ Seq.length wuy == nl /\
          Seq.length wuz == nl /\ Seq.length wut == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\
          Seq.length wsz == nl /\ Seq.length wst == nl /\
          W.pok wx wy wz wt /\
          sr wx wy wz wt na (ST.hsum vda (SZ.v vi)) (ST.hsum vdb (SZ.v vi)))
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let j = SZ.sub vi 1sz;
    rung ox oy oz ot ux uy uz ut sx sy sz st tx ty tz tt tbl da db j na;
    i := j;
  };
  let vi = !i;
  sz_zero vi;
  with wx wy wz wt.
    assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt);
  ST.hsum_dsum vda; ST.hsum_dsum vdb;
  sr_cong wx wy wz wt na (ST.hsum vda 0) (ST.hsum vdb 0) (B.le_nat vk1) (B.le_nat vk2);
  sr_done wx wy wz wt na (B.le_nat vk1) (B.le_nat vk2);
  W.pok_elim wx wy wz wt;

  Table.drop_table tbl;
  Mem.wipe st 5sz;
  Mem.wipe sz 5sz;
  Mem.wipe sy 5sz;
  Mem.wipe sx 5sz;
  Mem.wipe ut 5sz;
  Mem.wipe uz 5sz;
  Mem.wipe uy 5sz;
  Mem.wipe ux 5sz;
  Mem.wipe tt 80sz;
  Mem.wipe tz 80sz;
  Mem.wipe ty 80sz;
  Mem.wipe tx 80sz;
  Mem.wipe db 256sz;
  Mem.wipe da 256sz;
  ()
}

#pop-options
