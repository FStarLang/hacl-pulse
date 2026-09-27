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

(** Four bits of the scalar at a time.

    The bit-at-a-time ladder spends one doubling and one addition per bit,
    and the addition is wasted whenever the bit is zero -- but it cannot be
    skipped, because the scalar is secret.  A four-bit window spends four
    doublings and one addition per four bits: five point operations where
    the ladder spends eight.  The price is sixteen precomputed multiples of
    the base point and a lookup that must not let the digit reach the
    address bus, which is {!Hacl.Bignum.Base.table_select}.

    What makes this legal is {!Spec.K256.Smul}: the window computes the
    multiple in a different order from the specification's ladder, so it
    does not produce the specification's projective triple, only one
    equivalent to it.  Everything here is therefore stated up to [peq], and
    the callers discharge that at the point where they leave projective
    coordinates.

    The table is built at run time from the point that is passed in, so
    this serves the variable-base case; the generator gets the same
    treatment for free, since one of its multiples is [g] itself. *)
module Hacl.K256.PointWin

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum52
open Spec.K256.Field52
open Hacl.Impl.Limb4
open Hacl.Impl.Mont4
open Hacl.Bignum.Base
open Hacl.K256.Field52
open Hacl.K256.Point
open Hacl.K256.PointStep

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module K = Spec.K256
module GR = Spec.K256.Group
module SM = Spec.K256.Smul
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module B4 = Spec.Bignum4
module L4 = Hacl.Impl.Limb4

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The table, as a flat array}

    One array per coordinate, sixteen five-limb entries each.  [entry] is
    total -- out of range it is the empty sequence -- so that the
    invariants below typecheck without carrying the bound on [d] into every
    one of them. *)

let entry (v: Seq.seq S64.t) (d: nat) : Seq.seq S64.t =
  if d * 5 + 5 <= Seq.length v
  then Seq.slice v (d * 5) (d * 5 + 5)
  else Seq.empty #S64.t

let entry_fits (d: nat) : Lemma (requires d < 16) (ensures d * 5 + 5 <= 80)
  = Math.lemma_mult_le_right 5 (d + 1) 16

#push-options "--ifuel 1"
let entry_def (v: Seq.seq S64.t) (d: nat)
  : Lemma (requires d * 5 + 5 <= Seq.length v)
          (ensures entry v d == Seq.slice v (d * 5) (d * 5 + 5))
  = ()
#pop-options

#push-options "--ifuel 1 --z3rlimit 200"

(** Writing one entry leaves the others where they were. *)
let entry_untouched (v v': Seq.seq S64.t) (e d: nat)
  : Lemma (requires Seq.length v == 80 /\ Seq.length v' == 80 /\
                    e < 16 /\ d < 16 /\ ~(d == e) /\
                    (forall (j: nat). j < 80 ==>
                       (j < e * 5 \/ e * 5 + 5 <= j) ==>
                       Seq.index v' j == Seq.index v j))
          (ensures entry v' d == entry v d)
  = entry_fits d;
    entry_fits e;
    entry_def v d;
    entry_def v' d;
    if d < e then Math.lemma_mult_le_right 5 (d + 1) e
             else Math.lemma_mult_le_right 5 (e + 1) d;
    Seq.lemma_eq_intro (Seq.slice v' (d * 5) (d * 5 + 5))
                       (Seq.slice v (d * 5) (d * 5 + 5))

(** And it puts what was asked for into the one it does write. *)
let entry_written (v': Seq.seq S64.t) (src: Seq.seq S64.t) (e: nat)
  : Lemma (requires Seq.length v' == 80 /\ Seq.length src == 5 /\ e < 16 /\
                    (forall (j: nat). j < 5 ==>
                       Seq.index v' (e * 5 + j) == Seq.index src j))
          (ensures entry v' e == src)
  = entry_fits e;
    entry_def v' e;
    Seq.lemma_eq_intro (Seq.slice v' (e * 5) (e * 5 + 5)) src

(** What one store does to a table, entry by entry rather than limb by
    limb. *)
let tbl_shape (v v' src: Seq.seq S64.t) (e: nat)
  : Lemma (requires Seq.length v == 80 /\ Seq.length v' == 80 /\
                    Seq.length src == 5 /\ e < 16 /\
                    (forall (j: nat). j < 5 ==>
                       Seq.index v' (e * 5 + j) == Seq.index src j) /\
                    (forall (j: nat). j < 80 ==>
                       (j < e * 5 \/ e * 5 + 5 <= j) ==>
                       Seq.index v' j == Seq.index v j))
          (ensures (forall (dd: nat). dd < e ==> entry v' dd == entry v dd) /\
                   entry v' e == src)
  = entry_written v' src e;
    let aux (dd: nat) : Lemma (dd < e ==> entry v' dd == entry v dd)
      = if dd < e then entry_untouched v v' e dd else () in
    Classical.forall_intro aux

#pop-options

(** {2 The representation invariant, made opaque}

    Everything below says of some triple that it is on the curve and is
    equivalent to a multiple of the base point.  Said directly, that is
    [GR.on_curve] and [GR.peq], both of which are transparent definitions
    that unfold into field equations over a 78-digit prime.  Any verification
    condition that carries a few of them is minutes of Z3 time -- and a
    Pulse function's precondition is carried through its whole body, so the
    cost is paid on every goal, down to [2 * (4 * e) == 8 * e].

    So the pair is bundled into one opaque predicate.  The Pulse contracts
    below mention only [rep] and [oc]; the field appears in exactly the six
    small lemmas that introduce and eliminate them, each proved in a context
    containing nothing else. *)

[@@"opaque_to_smt"]
let oc (p: K.proj_point) : prop = GR.on_curve p

[@@"opaque_to_smt"]
let rep (a: K.proj_point) (n: nat) (p: K.proj_point) : prop =
  GR.on_curve a /\ GR.peq a (SM.smul n p)

let oc_intro (p: K.proj_point) : Lemma (requires GR.on_curve p) (ensures oc p)
  = reveal_opaque (`%oc) oc

let rep_elim (a: K.proj_point) (n: nat) (p: K.proj_point)
  : Lemma (requires rep a n p)
          (ensures GR.on_curve a /\ GR.peq a (SM.smul n p))
  = reveal_opaque (`%rep) rep

(** {2 What the table holds}

    [ent tx ty tz p d] is "entry [d] is the [d]-th multiple of [p]", up to
    equivalence -- the entries are built by repeated addition, so they are
    not the specification's triples.

    Everything here is bookkeeping about which table slots a store did and
    did not touch, and none of it needs to see the curve; the value of an
    entry is carried by the opaque {!rep}, so none of it does. *)

let ent (tx ty tz: Seq.seq S64.t) (p: K.proj_point) (n d: nat) : prop =
  pt_ok (entry tx d) (entry ty d) (entry tz d) /\
  rep (pt (entry tx d) (entry ty d) (entry tz d)) (d * n) p

let ent_intro (tx ty tz sx sy sz: Seq.seq S64.t) (p: K.proj_point) (n d: nat)
  : Lemma (requires entry tx d == sx /\ entry ty d == sy /\
                    entry tz d == sz /\ pt_ok sx sy sz /\
                    rep (pt sx sy sz) (d * n) p)
          (ensures ent tx ty tz p n d)
  = ()

(** An entry that was not written is still what it was. *)
let ent_eq (tx ty tz tx' ty' tz': Seq.seq S64.t) (p: K.proj_point) (n d: nat)
  : Lemma (requires ent tx ty tz p n d /\ entry tx' d == entry tx d /\
                    entry ty' d == entry ty d /\ entry tz' d == entry tz d)
          (ensures ent tx' ty' tz' p n d)
  = ()

let tok (tx ty tz: Seq.seq S64.t) (p: K.proj_point) (n: nat) (upto: nat) : prop =
  forall (d: nat). d < upto ==> ent tx ty tz p n d

(** Reading one entry back out, as a lemma so that the caller's query never
    has to instantiate the quantifier itself. *)
let tok_get (tx ty tz: Seq.seq S64.t) (p: K.proj_point) (n d: nat)
  : Lemma (requires tok tx ty tz p n 16 /\ d < 16)
          (ensures pt_ok (entry tx d) (entry ty d) (entry tz d) /\
                   rep (pt (entry tx d) (entry ty d) (entry tz d)) (d * n) p)
  = ()

#push-options "--ifuel 1 --z3rlimit 100"
let tok_extend (tx ty tz tx' ty' tz': Seq.seq S64.t) (p: K.proj_point)
               (n e: nat)
  : Lemma (requires tok tx ty tz p n e /\ e < 16 /\ ent tx' ty' tz' p n e /\
                    (forall (dd: nat). dd < e ==>
                       (entry tx' dd == entry tx dd /\
                        entry ty' dd == entry ty dd /\
                        entry tz' dd == entry tz dd)))
          (ensures tok tx' ty' tz' p n (e + 1))
  = introduce forall (dd: nat). dd < e + 1 ==> ent tx' ty' tz' p n dd
    with introduce _ ==> _
    with (if dd < e then ent_eq tx ty tz tx' ty' tz' p n dd else ())
#pop-options

(** Where entry [d] starts, and that it is addressable. *)
let store_off (d: nat)
  : Lemma (requires d < 16)
          (ensures d * 5 + 5 <= 80 /\ SZ.fits (d * 5) /\ SZ.fits (d * 5 + 5))
  = entry_fits d;
    SZ.fits_lte (d * 5) 80;
    SZ.fits_lte (d * 5 + 5) 80

#pop-options

(** {2 The spec-side steps}

    Each is one lemma of {!Spec.K256.Smul} with its hypotheses arranged as
    the Pulse function that uses it leaves them, so that at the point of
    use nothing remains to be discharged.  Doing it this way matters here
    more than usual: [peq] is transparent, so any goal the solver has to
    work at will drag in the field. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let smul_cong (x y: nat) (p: K.proj_point)
  : Lemma (requires x == y) (ensures SM.smul x p == SM.smul y p) = ()

let rep_cong (a: K.proj_point) (x y: nat) (p: K.proj_point)
  : Lemma (requires rep a x p /\ x == y) (ensures rep a y p) = ()

let dbl_ok (a b p: K.proj_point) (e: nat)
  : Lemma (requires oc p /\ rep a e p /\ b == K.point_double a)
          (ensures rep b (2 * e) p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.smul_dbl_congr e p a

let add_ok (a s r p: K.proj_point) (e d: nat)
  : Lemma (requires oc p /\ rep a e p /\ rep s d p /\ r == K.point_add a s)
          (ensures rep r (e + d) p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.smul_add_congr e d p a s

(** The scale arithmetic, proved where nothing else is in scope.  Both are
    one step of distributivity, but a product of two variables asked for
    in the middle of a loop whose context carries the addition law is the
    difference between a second and twenty minutes. *)
let mul_zero (b: nat) : Lemma (0 * b == 0) = ()

let mul_succ (a b: nat) : Lemma (a * b + b == (a + 1) * b)
  = Math.distributivity_add_left a 1 b

let mul_one (a: nat) : Lemma (a * 1 == a) = ()

let mul_nat (a b: nat) : Lemma (a * b >= 0) = Math.nat_times_nat_is_nat a b

let zero_ok (p: K.proj_point)
  : Lemma (requires oc p) (ensures rep K.point_at_infinity 0 p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    GR.point_at_infinity_on_curve ();
    SM.smul_zero p;
    GR.peq_refl K.point_at_infinity

(** A point is its own first multiple.  The scale below is one for a
    variable-base window; a fixed-base one passes a power of two. *)
let rep_one (p: K.proj_point)
  : Lemma (requires oc p) (ensures rep p 1 p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.smul_one p;
    SM.smul_ok 1 p;
    GR.peq_sym (SM.smul 1 p) p

(** Leaving the abstraction: what the caller of the window is told.  The
    specification's own ladder produces a different triple from the window,
    so the two are related by [peq] and not by equality; {!Spec.K256.Smul}
    is where that is proved. *)
let win_done (a p: K.proj_point) (k: nat)
  : Lemma (requires oc p /\ rep a k p /\ k < pow2 256)
          (ensures GR.on_curve a /\ GR.on_curve (K.point_mul k p) /\
                   GR.peq a (K.point_mul k p))
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.point_mul_is_smul k p;
    SM.smul_ok k p;
    GR.peq_sym (K.point_mul k p) (SM.smul k p);
    GR.peq_trans a (SM.smul k p) (K.point_mul k p)

(** One step down the scalar, four bits at a time. *)
let digit_split (n i: nat)
  : Lemma (n / pow2 i == 16 * (n / pow2 (i + 4)) + n / pow2 i % 16)
  = assert_norm (pow2 4 == 16);
    Math.pow2_plus i 4;
    Math.division_multiplication_lemma n (pow2 i) (pow2 4);
    Math.euclidean_division_definition (n / pow2 i) 16

let pow2_pos (i: nat) : Lemma (pow2 i > 0)
  = Math.pow2_le_compat i 0; assert_norm (pow2 0 == 1)

let div_nonneg (x: nat) (i: nat) : Lemma (requires pow2 i > 0)
                                         (ensures x / pow2 i >= 0) = ()

let pow2_cong (x y: nat) : Lemma (requires x == y) (ensures pow2 x == pow2 y) = ()

let step4 (x: nat) : Lemma (requires x > 0 /\ x % 4 == 0)
                           (ensures 4 <= x /\ (x - 4) % 4 == 0) = ()

let sz_zero (x: SZ.t) : Lemma (requires SZ.gt x 0sz == false)
                              (ensures SZ.v x == 0) = ()

let top_div (k: nat) : Lemma (requires k < pow2 256) (ensures k / pow2 256 == 0)
  = Math.small_div k (pow2 256)

let bot_div (k: nat) : Lemma (k / pow2 0 == k) = assert_norm (pow2 0 == 1)

#pop-options

(** {2 Building the table}

    Entry [d] is [d] copies of the point added together, computed by
    walking up from the point at infinity: sixteen additions, one of which
    is wasted on the entry that is never used.  Spending it buys a loop
    with one case rather than three. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The three coordinates of one entry, stored together. *)
inline_for_extraction
fn store3 (tx ty tz: A.array S64.t) (sx sy sz: A.array S64.t) (off: SZ.t)
          (#vtx #vty #vtz: erased (Seq.seq S64.t)) (#ps: perm)
          (#vsx #vsy #vsz: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
  A.pts_to sx #ps vsx ** A.pts_to sy #ps vsy ** A.pts_to sz #ps vsz **
  pure (Seq.length vtx == 80 /\ Seq.length vty == 80 /\ Seq.length vtz == 80 /\
        Seq.length vsx == 5 /\ Seq.length vsy == 5 /\ Seq.length vsz == 5 /\
        SZ.v off + 5 <= 80 /\ SZ.fits (SZ.v off + 5))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
  A.pts_to sx #ps vsx ** A.pts_to sy #ps vsy ** A.pts_to sz #ps vsz **
  pure (Seq.length wx == 80 /\ Seq.length wy == 80 /\ Seq.length wz == 80 /\
        Seq.length vtx == 80 /\ Seq.length vty == 80 /\ Seq.length vtz == 80 /\
        Seq.length vsx == 5 /\ Seq.length vsy == 5 /\ Seq.length vsz == 5 /\
        SZ.v off + 5 <= 80 /\
        (forall (j: nat). j < 5 ==>
           (Seq.index wx (SZ.v off + j) == Seq.index vsx j /\
            Seq.index wy (SZ.v off + j) == Seq.index vsy j /\
            Seq.index wz (SZ.v off + j) == Seq.index vsz j)) /\
        (forall (j: nat). j < 80 ==>
           (j < SZ.v off \/ SZ.v off + 5 <= j) ==>
           (Seq.index wx j == Seq.index vtx j /\
            Seq.index wy j == Seq.index vty j /\
            Seq.index wz j == Seq.index vtz j)))
{
  table_store tx sx 5sz off;
  table_store ty sy 5sz off;
  table_store tz sz 5sz off;
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

let sz_sixteen (x: SZ.t) : Lemma (requires SZ.lt x 16sz == false /\ SZ.v x <= 16)
                                 (ensures SZ.v x == 16) = ()

(** [build_table tx ty tz q p n] fills the sixteen entries with
    [0]Q .. [15]Q, where [Q] is the [n]-th multiple of [P]: entry [d] is
    recorded as the [d n]-th multiple of [P], not the [d]-th of [Q].

    Carrying the scale is what lets the fixed-base window share this code.
    There, four tables are built from [G], [2^64 G], [2^128 G] and
    [2^192 G], and all four have to be described in terms of the one
    generator, because it is [G] that the answer is a multiple of.  A
    variable-base window passes [n = 1] and the two readings coincide. *)
fn build_table (tx ty tz: A.array S64.t) (qx qy qz: A.array S64.t)
               (p: erased K.proj_point) (n: erased nat)
               (#vtx #vty #vtz: erased (Seq.seq S64.t))
               (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  pure (Seq.length vtx == 80 /\ Seq.length vty == 80 /\ Seq.length vtz == 80 /\
        pt_ok vqx vqy vqz /\ oc (reveal p) /\
        rep (pt vqx vqy vqz) n (reveal p))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  pure (Seq.length wx == 80 /\ Seq.length wy == 80 /\ Seq.length wz == 80 /\
        tok wx wy wz (reveal p) (reveal n) 16)
{
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  let z = S64.zero;
  let mut cx = [| z; 5sz |]; A.pts_to_len cx;
  let mut cy = [| z; 5sz |]; A.pts_to_len cy;
  let mut cz = [| z; 5sz |]; A.pts_to_len cz;
  let mut nx = [| z; 5sz |]; A.pts_to_len nx;
  let mut ny = [| z; 5sz |]; A.pts_to_len ny;
  let mut nz = [| z; 5sz |]; A.pts_to_len nz;
  A.pts_to_len cx; A.pts_to_len cy; A.pts_to_len cz;
  A.pts_to_len nx; A.pts_to_len ny; A.pts_to_len nz;

  set_infinity cx cy cz;
  zero_ok (reveal p);
  mul_zero (reveal n);
  rep_cong K.point_at_infinity 0 (0 * reveal n) (reveal p);

  let mut d = 0sz;
  while (let vd = !d; SZ.lt vd 16sz)
  invariant exists* (vd: SZ.t)
                    (wx wy wz wcx wcy wcz wnx wny wnz: Seq.seq S64.t).
    pts_to d vd **
    A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
    A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz **
    A.pts_to nx wnx ** A.pts_to ny wny ** A.pts_to nz wnz **
    A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
    pure (SZ.v vd <= 16 /\
          Seq.length wx == 80 /\ Seq.length wy == 80 /\ Seq.length wz == 80 /\
          Seq.length wnx == nl /\ Seq.length wny == nl /\ Seq.length wnz == nl /\
          pt_ok wcx wcy wcz /\
          rep (pt wcx wcy wcz) (SZ.v vd * reveal n) (reveal p) /\
          tok wx wy wz (reveal p) (reveal n) (SZ.v vd))
  decreases (16 - SZ.v (!d))
  {
    let vd = !d;
    with wx wy wz. assert (A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz);
    with wcx wcy wcz. assert (A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz);
    store_off (SZ.v vd);
    store3 tx ty tz cx cy cz (SZ.mul vd 5sz);
    with wx' wy' wz'. assert (A.pts_to tx wx' ** A.pts_to ty wy' ** A.pts_to tz wz');
    tbl_shape wx wx' wcx (SZ.v vd);
    tbl_shape wy wy' wcy (SZ.v vd);
    tbl_shape wz wz' wcz (SZ.v vd);
    ent_intro wx' wy' wz' wcx wcy wcz (reveal p) (reveal n) (SZ.v vd);
    tok_extend wx wy wz wx' wy' wz' (reveal p) (reveal n) (SZ.v vd);
    point_add nx ny nz cx cy cz qx qy qz;
    with wnx wny wnz. assert (A.pts_to nx wnx ** A.pts_to ny wny ** A.pts_to nz wnz);
    mul_nat (SZ.v vd) (reveal n);
    add_ok (pt wcx wcy wcz) (pt vqx vqy vqz) (pt wnx wny wnz) (reveal p)
           (SZ.v vd * reveal n) (reveal n);
    mul_succ (SZ.v vd) (reveal n);
    rep_cong (pt wnx wny wnz) (SZ.v vd * reveal n + reveal n)
             ((SZ.v vd + 1) * reveal n) (reveal p);
    fcopy cx nx; fcopy cy ny; fcopy cz nz;
    d := SZ.add vd 1sz;
  };
  let vd = !d;
  sz_sixteen vd;
  ()
}

#pop-options


(** {2 One rung}

    Four doublings and one addition, which advance the accumulator from
    [e] to [16e + d].  The digit is secret, so the table entry is fetched
    by reading all sixteen of them.

    The doublings are a function apiece.  The solver's work grows with what
    it can see, and [peq], [on_curve] and [pt_ok] all unfold into field
    equations over the prime; with four doublings in one body the context
    is large enough that [2 * (4 * e) == 8 * e] takes minutes.  Behind a
    contract each doubling contributes three facts and nothing else. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** One doubling, in place: through the scratch triple and back. *)
inline_for_extraction
fn win_dbl (ox oy oz ux uy uz: A.array S64.t)
           (p: erased K.proj_point) (e: erased nat)
           (#vox #voy #voz: erased (Seq.seq S64.t))
           (#vux #vuy #vuz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        pt_ok vox voy voz /\ oc (reveal p) /\
        rep (pt vox voy voz) e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        pt_ok wx wy wz /\ rep (pt wx wy wz) (2 * reveal e) (reveal p))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  point_double ux uy uz ox oy oz;
  with u1x u1y u1z. assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z);
  dbl_ok (pt vox voy voz) (pt u1x u1y u1z) p (reveal e);
  fcopy ox ux; fcopy oy uy; fcopy oz uz;
  ()
}

(** Four of them, which is the doubling half of a rung. *)
fn win_dbl4 (ox oy oz ux uy uz: A.array S64.t)
            (p: erased K.proj_point) (e: erased nat)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        pt_ok vox voy voz /\ oc (reveal p) /\
        rep (pt vox voy voz) e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        pt_ok wx wy wz /\ rep (pt wx wy wz) (16 * reveal e) (reveal p))
{
  win_dbl ox oy oz ux uy uz p e;
  with a1x a1y a1z. assert (A.pts_to ox a1x ** A.pts_to oy a1y ** A.pts_to oz a1z);
  rep_cong (pt a1x a1y a1z) (2 * reveal e) (2 * reveal e) p;
  win_dbl ox oy oz ux uy uz p (hide (2 * reveal e));
  with a2x a2y a2z. assert (A.pts_to ox a2x ** A.pts_to oy a2y ** A.pts_to oz a2z);
  rep_cong (pt a2x a2y a2z) (2 * (2 * reveal e)) (4 * reveal e) p;
  win_dbl ox oy oz ux uy uz p (hide (4 * reveal e));
  with a3x a3y a3z. assert (A.pts_to ox a3x ** A.pts_to oy a3y ** A.pts_to oz a3z);
  rep_cong (pt a3x a3y a3z) (2 * (4 * reveal e)) (8 * reveal e) p;
  win_dbl ox oy oz ux uy uz p (hide (8 * reveal e));
  with a4x a4y a4z. assert (A.pts_to ox a4x ** A.pts_to oy a4y ** A.pts_to oz a4z);
  rep_cong (pt a4x a4y a4z) (2 * (8 * reveal e)) (16 * reveal e) p;
  ()
}

#pop-options

(** The other half of a rung: fetch [tbl[d]] without letting [d] reach the
    address bus, and add it in.  The contract mentions no divisions and no
    powers of two -- the partial scalar [e] and the digit [d] are opaque
    naturals -- which keeps the index arithmetic of the ladder out of a
    context that carries the addition law. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn win_add (ox oy oz ux uy uz sx sy sz: A.array S64.t)
           (tx ty tz: A.array S64.t) (dig: S64.t)
           (p: erased K.proj_point) (n: erased nat)
           (e: erased nat) (d: erased nat)
           (#vox #voy #voz: erased (Seq.seq S64.t))
           (#vux #vuy #vuz: erased (Seq.seq S64.t))
           (#vsx #vsy #vsz: erased (Seq.seq S64.t))
           (#ptb: perm) (#vtx #vty #vtz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to tx #ptb vtx ** A.pts_to ty #ptb vty ** A.pts_to tz #ptb vtz **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\ Seq.length vsz == nl /\
        Seq.length vtx == 80 /\ Seq.length vty == 80 /\ Seq.length vtz == 80 /\
        pt_ok vox voy voz /\ oc (reveal p) /\
        rep (pt vox voy voz) e (reveal p) /\
        tok vtx vty vtz (reveal p) (reveal n) 16 /\
        reveal d < 16 /\ S64.v dig == reveal d)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to tx #ptb vtx ** A.pts_to ty #ptb vty ** A.pts_to tz #ptb vtz **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\ Seq.length wsz == nl /\
        pt_ok wx wy wz /\
        rep (pt wx wy wz) (reveal e + reveal d * reveal n) (reveal p))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz;
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  entry_fits (reveal d);
  table_select sx tx 5sz dig d;
  table_select sy ty 5sz dig d;
  table_select sz tz 5sz dig d;
  entry_def vtx (reveal d); entry_def vty (reveal d); entry_def vtz (reveal d);
  tok_get vtx vty vtz (reveal p) (reveal n) (reveal d);
  with wsx wsy wsz. assert (A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz);
  point_add ux uy uz ox oy oz sx sy sz;
  with u1x u1y u1z. assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z);
  add_ok (pt vox voy voz) (pt wsx wsy wsz) (pt u1x u1y u1z) (reveal p)
         (reveal e) (reveal d * reveal n);
  fcopy ox ux; fcopy oy uy; fcopy oz uz;
  ()
}

#pop-options

(** {2 The ladder}

    Sixty-four rungs of four bits each.  The accumulator starts at the
    point at infinity, which is the multiple by the empty prefix of the
    scalar, and after the rung at [j] it is the multiple by [k / 2^j]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** The scalar, as a number.  Named so that the invariant below does not
    have to spell it out four times. *)
let kv (vk: Seq.seq S64.t) : GTot nat = B4.eval (L4.vals vk)

let kv_bnd (vk: Seq.seq S64.t)
  : Lemma (requires Seq.length vk == B4.nl /\ B4.bnd (L4.vals vk) B4.base)
          (ensures kv vk < pow2 256)
  = B4.eval_bnd (L4.vals vk);
    assert_norm (B4.rad * B4.nl == 256)

(** [point_mul_win o q ks] is [o := [ks] Q], up to [peq]. *)
fn point_mul_win (ox oy oz: A.array S64.t) (qx qy qz: A.array S64.t)
                 (ks: A.array S64.t)
                 (#vox #voy #voz: erased (Seq.seq S64.t))
                 (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
                 (#pk: perm) (#vk: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\ Seq.length voz == nl /\
        Seq.length vk == B4.nl /\ B4.bnd (L4.vals vk) B4.base /\
        pt_ok vqx vqy vqz /\ GR.on_curve (pt vqx vqy vqz))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  A.pts_to ks #pk vk **
  pure (pt_ok wx wy wz /\ GR.on_curve (pt wx wy wz) /\
        GR.on_curve (K.point_mul (kv vk) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz) (K.point_mul (kv vk) (pt vqx vqy vqz)))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ks;
  kv_bnd vk;
  oc_intro (pt vqx vqy vqz);
  let z = S64.zero;
  let mut tx = [| z; 80sz |]; A.pts_to_len tx;
  let mut ty = [| z; 80sz |]; A.pts_to_len ty;
  let mut tz = [| z; 80sz |]; A.pts_to_len tz;
  let mut ux = [| z; 5sz |]; A.pts_to_len ux;
  let mut uy = [| z; 5sz |]; A.pts_to_len uy;
  let mut uz = [| z; 5sz |]; A.pts_to_len uz;
  let mut sx = [| z; 5sz |]; A.pts_to_len sx;
  let mut sy = [| z; 5sz |]; A.pts_to_len sy;
  let mut sz = [| z; 5sz |]; A.pts_to_len sz;
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz;

  rep_one (pt vqx vqy vqz);
  build_table tx ty tz qx qy qz (hide (pt vqx vqy vqz)) (hide 1);
  set_infinity ox oy oz;
  zero_ok (pt vqx vqy vqz);
  top_div (kv vk);
  pow2_pos 256;
  div_nonneg (kv vk) 256;

  let mut j = 256sz;
  while (let vj = !j; SZ.gt vj 0sz)
  invariant exists* (vj: SZ.t)
                    (wx wy wz wux wuy wuz wsx wsy wsz
                     wtx wty wtz: Seq.seq S64.t).
    pts_to j vj **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
    A.pts_to tx wtx ** A.pts_to ty wty ** A.pts_to tz wtz **
    A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
    A.pts_to ks #pk vk **
    pure (SZ.v vj <= 256 /\ SZ.v vj % 4 == 0 /\
          pow2 (SZ.v vj) > 0 /\ kv vk / pow2 (SZ.v vj) >= 0 /\
          Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\ Seq.length wsz == nl /\
          Seq.length wtx == 80 /\ Seq.length wty == 80 /\ Seq.length wtz == 80 /\
          tok wtx wty wtz (pt vqx vqy vqz) 1 16 /\
          pt_ok wx wy wz /\
          rep (pt wx wy wz) (kv vk / pow2 (SZ.v vj)) (pt vqx vqy vqz))
  decreases (SZ.v (!j))
  {
    let vj = !j;
    step4 (SZ.v vj);
    let j2 = SZ.sub vj 4sz;
    pow2_pos (SZ.v j2);
    div_nonneg (kv vk) (SZ.v j2);
    let dig = adigit ks j2;
    mul_nat (kv vk / pow2 (SZ.v j2) % 16) 1;
    win_dbl4 ox oy oz ux uy uz (hide (pt vqx vqy vqz))
             (hide (kv vk / pow2 (SZ.v vj)));
    win_add ox oy oz ux uy uz sx sy sz tx ty tz dig
            (hide (pt vqx vqy vqz)) (hide 1)
            (hide (16 * (kv vk / pow2 (SZ.v vj))))
            (hide (kv vk / pow2 (SZ.v j2) % 16));
    pow2_cong (SZ.v j2 + 4) (SZ.v vj);
    digit_split (kv vk) (SZ.v j2);
    mul_one (kv vk / pow2 (SZ.v j2) % 16);
    with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
    rep_cong (pt wx wy wz)
             (16 * (kv vk / pow2 (SZ.v vj)) + kv vk / pow2 (SZ.v j2) % 16)
             (kv vk / pow2 (SZ.v j2)) (pt vqx vqy vqz);
    j := j2;
  };
  let vj = !j;
  sz_zero vj;
  bot_div (kv vk);
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  win_done (pt wx wy wz) (pt vqx vqy vqz) (kv vk);
  ()
}

#pop-options
