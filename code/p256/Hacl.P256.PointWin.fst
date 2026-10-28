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

    What makes this legal is {!Spec.P256.Smul}: the window computes the
    multiple in a different order from the specification's ladder, so it
    does not produce the specification's projective triple, only one
    equivalent to it.  Everything here is therefore stated up to [peq], and
    the callers discharge that at the point where they leave projective
    coordinates.

    The table is built at run time from the point that is passed in, so
    this serves the variable-base case; the generator gets the same
    treatment for free, since one of its multiples is [g] itself. *)
module Hacl.P256.PointWin

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum4
open Spec.P256.Field
open Hacl.Impl.Limb4
open Hacl.Impl.Mont4
open Hacl.Bignum.Base
open Hacl.P256.Field
open Hacl.P256.Point
open Hacl.P256.PointStep

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P256
module GR = Spec.P256.Group
module SM = Spec.P256.Smul
module J = Spec.P256.Jac
module JS = Spec.P256.JacSv
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module B4 = Spec.Bignum4
module L4 = Hacl.Impl.Limb4
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The table, as a flat array}

    One array per coordinate, sixteen four-limb entries each.  [entry] is
    total -- out of range it is the empty sequence -- so that the
    invariants below typecheck without carrying the bound on [d] into every
    one of them. *)

let entry (v: Seq.seq S64.t) (d: nat) : Seq.seq S64.t =
  if d * 4 + 4 <= Seq.length v
  then Seq.slice v (d * 4) (d * 4 + 4)
  else Seq.empty #S64.t

let entry_fits (d: nat) : Lemma (requires d < 16) (ensures d * 4 + 4 <= 64)
  = Math.lemma_mult_le_right 4 (d + 1) 16

#push-options "--ifuel 1"
let entry_def (v: Seq.seq S64.t) (d: nat)
  : Lemma (requires d * 4 + 4 <= Seq.length v)
          (ensures entry v d == Seq.slice v (d * 4) (d * 4 + 4))
  = ()
#pop-options

#push-options "--ifuel 1 --z3rlimit 200"

(** Writing one entry leaves the others where they were. *)
let entry_untouched (v v': Seq.seq S64.t) (e d: nat)
  : Lemma (requires Seq.length v == 64 /\ Seq.length v' == 64 /\
                    e < 16 /\ d < 16 /\ ~(d == e) /\
                    (forall (j: nat). j < 64 ==>
                       (j < e * 4 \/ e * 4 + 4 <= j) ==>
                       Seq.index v' j == Seq.index v j))
          (ensures entry v' d == entry v d)
  = entry_fits d;
    entry_fits e;
    entry_def v d;
    entry_def v' d;
    if d < e then Math.lemma_mult_le_right 4 (d + 1) e
             else Math.lemma_mult_le_right 4 (e + 1) d;
    Seq.lemma_eq_intro (Seq.slice v' (d * 4) (d * 4 + 4))
                       (Seq.slice v (d * 4) (d * 4 + 4))

(** And it puts what was asked for into the one it does write. *)
let entry_written (v': Seq.seq S64.t) (src: Seq.seq S64.t) (e: nat)
  : Lemma (requires Seq.length v' == 64 /\ Seq.length src == 4 /\ e < 16 /\
                    (forall (j: nat). j < 4 ==>
                       Seq.index v' (e * 4 + j) == Seq.index src j))
          (ensures entry v' e == src)
  = entry_fits e;
    entry_def v' e;
    Seq.lemma_eq_intro (Seq.slice v' (e * 4) (e * 4 + 4)) src

(** What one store does to a table, entry by entry rather than limb by
    limb. *)
let tbl_shape (v v' src: Seq.seq S64.t) (e: nat)
  : Lemma (requires Seq.length v == 64 /\ Seq.length v' == 64 /\
                    Seq.length src == 4 /\ e < 16 /\
                    (forall (j: nat). j < 4 ==>
                       Seq.index v' (e * 4 + j) == Seq.index src j) /\
                    (forall (j: nat). j < 64 ==>
                       (j < e * 4 \/ e * 4 + 4 <= j) ==>
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
    below mention only [rep], [oc] and [pok].

    [pok] is where this curve differs from secp256k1.  There [pt_ok] is a
    bound on four limbs and costs nothing, so it is stated directly; here
    the field is in Montgomery form and [felem] unfolds to
    [eval (vals v) < fmod.m], an evaluation of the whole 256-bit number
    against the prime.  Three of those per point, carried through the body
    of a function with four points in flight, is enough on its own to put
    the four-doubling rung over the timeout -- which is what it did.  So it
    is opaque here too, and the array lengths it implies are restated
    alongside it, since those are what the array operations need and they
    cost nothing. *)

[@@"opaque_to_smt"]
let oc (p: P.proj_point) : prop = GR.on_curve p

(** [rep x y z n p] is "the triple of limb sequences [x], [y], [z] reads as
    a point on the curve equivalent to [n] copies of [p]".

    It takes the three sequences rather than the point they read as, and
    that is not cosmetic.  [pt x y z] unfolds to three applications of
    [fev], and on this curve [fev v] is [eval (vals v) * fmod.ri % fmod.m]
    -- it carries the Montgomery constants, two 78-digit literals, in every
    coordinate.  The four-doubling rung has five triples in flight, so
    stating its invariant over points puts thirty of those literals in a
    context that never needs one, and the rung does not terminate.  Over
    sequences the rung's contract mentions no field at all. *)
[@@"opaque_to_smt"]
let rep (x y z: Seq.seq S64.t) (n: nat) (p: P.proj_point) : prop =
  GR.on_curve (pt x y z) /\ GR.peq (pt x y z) (SM.smul n p)

[@@"opaque_to_smt"]
let pok (x y z: Seq.seq S64.t) : prop = pt_ok x y z

let oc_intro (p: P.proj_point) : Lemma (requires GR.on_curve p) (ensures oc p)
  = reveal_opaque (`%oc) oc

let pok_intro (x y z: Seq.seq S64.t)
  : Lemma (requires pt_ok x y z) (ensures pok x y z)
  = reveal_opaque (`%pok) pok

let pok_elim (x y z: Seq.seq S64.t)
  : Lemma (requires pok x y z)
          (ensures pt_ok x y z /\ Seq.length x == nl /\
                   Seq.length y == nl /\ Seq.length z == nl)
  = reveal_opaque (`%pok) pok

let rep_elim (x y z: Seq.seq S64.t) (n: nat) (p: P.proj_point)
  : Lemma (requires rep x y z n p)
          (ensures GR.on_curve (pt x y z) /\ GR.peq (pt x y z) (SM.smul n p))
  = reveal_opaque (`%rep) rep

(** {2 What the table holds}

    [ent tx ty tz p d] is "entry [d] is the [d]-th multiple of [p]", up to
    equivalence -- the entries are built by repeated addition, so they are
    not the specification's triples.

    Everything here is bookkeeping about which table slots a store did and
    did not touch, and none of it needs to see the curve; the value of an
    entry is carried by the opaque {!rep}, so none of it does. *)

[@@"opaque_to_smt"]
let ent (tx ty tz: Seq.seq S64.t) (p: P.proj_point) (n d: nat) : prop =
  pok (entry tx d) (entry ty d) (entry tz d) /\
  rep (entry tx d) (entry ty d) (entry tz d) (d * n) p

let ent_intro (tx ty tz sx sy sz: Seq.seq S64.t) (p: P.proj_point) (n d: nat)
  : Lemma (requires entry tx d == sx /\ entry ty d == sy /\
                    entry tz d == sz /\ pok sx sy sz /\ rep sx sy sz (d * n) p)
          (ensures ent tx ty tz p n d)
  = reveal_opaque (`%ent) ent

(** An entry that was not written is still what it was. *)
let ent_eq (tx ty tz tx' ty' tz': Seq.seq S64.t) (p: P.proj_point) (n d: nat)
  : Lemma (requires ent tx ty tz p n d /\ entry tx' d == entry tx d /\
                    entry ty' d == entry ty d /\ entry tz' d == entry tz d)
          (ensures ent tx' ty' tz' p n d)
  = reveal_opaque (`%ent) ent

let tok (tx ty tz: Seq.seq S64.t) (p: P.proj_point) (n: nat) (upto: nat) : prop =
  forall (d: nat). d < upto ==> ent tx ty tz p n d

(** Reading one entry back out, as a lemma so that the caller's query never
    has to instantiate the quantifier itself. *)
let tok_get (tx ty tz: Seq.seq S64.t) (p: P.proj_point) (n d: nat)
  : Lemma (requires tok tx ty tz p n 16 /\ d < 16)
          (ensures pok (entry tx d) (entry ty d) (entry tz d) /\
                   rep (entry tx d) (entry ty d) (entry tz d) (d * n) p)
  = reveal_opaque (`%ent) ent

(** The entry that was just written is the one the index names.  Stated as
    a lemma of its own because the [dd == e] case of {!tok_extend} is not
    the triviality it looks: left to itself the solver reproves the entry
    from scratch rather than matching it, and with the curve in scope that
    is twenty minutes and a timeout. *)
let ent_same (tx ty tz: Seq.seq S64.t) (p: P.proj_point) (n e dd: nat)
  : Lemma (requires ent tx ty tz p n e /\ dd == e)
          (ensures ent tx ty tz p n dd)
  = ()

#push-options "--ifuel 1 --z3rlimit 100"
let tok_extend (tx ty tz tx' ty' tz': Seq.seq S64.t) (p: P.proj_point)
               (n e: nat)
  : Lemma (requires tok tx ty tz p n e /\ e < 16 /\ ent tx' ty' tz' p n e /\
                    (forall (dd: nat). dd < e ==>
                       (entry tx' dd == entry tx dd /\
                        entry ty' dd == entry ty dd /\
                        entry tz' dd == entry tz dd)))
          (ensures tok tx' ty' tz' p n (e + 1))
  = introduce forall (dd: nat). dd < e + 1 ==> ent tx' ty' tz' p n dd
    with introduce _ ==> _
    with (if dd < e then ent_eq tx ty tz tx' ty' tz' p n dd
                    else ent_same tx' ty' tz' p n e dd)
#pop-options

(** Where entry [d] starts, and that it is addressable. *)
let store_off (d: nat)
  : Lemma (requires d < 16)
          (ensures d * 4 + 4 <= 64 /\ SZ.fits (d * 4) /\ SZ.fits (d * 4 + 4))
  = entry_fits d;
    SZ.fits_lte (d * 4) 64;
    SZ.fits_lte (d * 4 + 4) 64

#pop-options

(** {2 The spec-side steps}

    Each is one lemma of {!Spec.P256.Smul} with its hypotheses arranged as
    the Pulse function that uses it leaves them, so that at the point of
    use nothing remains to be discharged.  Doing it this way matters here
    more than usual: [peq] is transparent, so any goal the solver has to
    work at will drag in the field. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let smul_cong (x y: nat) (p: P.proj_point)
  : Lemma (requires x == y) (ensures SM.smul x p == SM.smul y p) = ()

let rep_cong (x y z: Seq.seq S64.t) (a b: nat) (p: P.proj_point)
  : Lemma (requires rep x y z a p /\ a == b) (ensures rep x y z b p) = ()

(** A copy that preserves every coordinate preserves the whole invariant.
    This is the one place [fev] has to be named, and it is named exactly as
    {!Hacl.P256.Field.fcopy} leaves it. *)
let rep_fcopy (x y z x' y' z': Seq.seq S64.t) (n: nat) (p: P.proj_point)
  : Lemma (requires rep x y z n p /\
                    fev x' == fev x /\ fev y' == fev y /\ fev z' == fev z)
          (ensures rep x' y' z' n p)
  = reveal_opaque (`%rep) rep

(** The Jacobian run's invariant, over sequences for the same reason as
    {!rep}: "[x], [y], [z] read as a Jacobian triple equivalent to [n]
    copies of [p]" ({!Spec.P256.Jac.jr}). *)
[@@"opaque_to_smt"]
let jrs (x y z: Seq.seq S64.t) (n: nat) (p: P.proj_point) : prop =
  J.jr (pt x y z) n p

let jrs_cong (x y z: Seq.seq S64.t) (a b: nat) (p: P.proj_point)
  : Lemma (requires jrs x y z a p /\ a == b) (ensures jrs x y z b p) = ()

let jin_ok (hx hy hz jx jy: Seq.seq S64.t) (p: P.proj_point) (e: nat)
  : Lemma (requires oc p /\ rep hx hy hz e p /\
                    pt jx jy hz == J.to_j (pt hx hy hz))
          (ensures jrs jx jy hz e p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    reveal_opaque (`%jrs) jrs;
    J.jr_in (pt hx hy hz) e p

let jdbl_ok (ox oy oz wx wy wz: Seq.seq S64.t) (p: P.proj_point) (e: nat)
  : Lemma (requires oc p /\ jrs ox oy oz e p /\
                    pt wx wy wz == JS.jdouble (pt ox oy oz))
          (ensures jrs wx wy wz (2 * e) p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%jrs) jrs;
    J.jr_dbl (pt ox oy oz) e p

let jout_ok (ox oy oz wx wz: Seq.seq S64.t) (p: P.proj_point) (e: nat)
  : Lemma (requires jrs ox oy oz e p /\
                    pt wx oy wz == JS.to_h (pt ox oy oz))
          (ensures rep wx oy wz e p)
  = reveal_opaque (`%jrs) jrs;
    reveal_opaque (`%rep) rep;
    J.jr_out (pt ox oy oz) e p

let add_ok (ox oy oz sx sy sz wx wy wz: Seq.seq S64.t) (p: P.proj_point)
           (e d: nat)
  : Lemma (requires oc p /\ rep ox oy oz e p /\ rep sx sy sz d p /\
                    pt wx wy wz == P.point_add (pt ox oy oz) (pt sx sy sz))
          (ensures rep wx wy wz (e + d) p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.smul_add_congr e d p (pt ox oy oz) (pt sx sy sz)

(** The scale arithmetic, proved where nothing else is in scope.  Each is
    one step of distributivity, but a product of two variables asked for in
    the middle of a loop whose context carries the addition law is the
    difference between a second and twenty minutes.  On this curve that is
    truer than on the others: the projection out of a limb sequence carries
    the Montgomery constants. *)
let mul_zero (b: nat) : Lemma (0 * b == 0) = ()

let mul_succ (a b: nat) : Lemma (a * b + b == (a + 1) * b)
  = Math.distributivity_add_left a 1 b

let mul_one (a: nat) : Lemma (a * 1 == a) = ()

let mul_nat (a b: nat) : Lemma (a * b >= 0) = Math.nat_times_nat_is_nat a b

let zero_ok (wx wy wz: Seq.seq S64.t) (p: P.proj_point)
  : Lemma (requires oc p /\ pt wx wy wz == P.point_at_infinity)
          (ensures rep wx wy wz 0 p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    GR.point_at_infinity_on_curve ();
    SM.smul_zero p;
    GR.peq_refl P.point_at_infinity

(** A point is its own first multiple.  The scale below is one for a
    variable-base window; a fixed-base one passes a power of two. *)
let rep_one (x y z: Seq.seq S64.t) (p: P.proj_point)
  : Lemma (requires oc p /\ pt x y z == p) (ensures rep x y z 1 p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.smul_one p;
    SM.smul_ok 1 p;
    GR.peq_sym (SM.smul 1 p) p

(** Leaving the abstraction: what the caller of the window is told.  The
    specification's own ladder produces a different triple from the window,
    so the two are related by [peq] and not by equality; {!Spec.P256.Smul}
    is where that is proved. *)
let win_done (wx wy wz: Seq.seq S64.t) (p: P.proj_point) (k: nat)
  : Lemma (requires oc p /\ rep wx wy wz k p /\ k < pow2 256)
          (ensures GR.on_curve (pt wx wy wz) /\
                   GR.on_curve (P.point_mul k p) /\
                   GR.peq (pt wx wy wz) (P.point_mul k p))
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.point_mul_is_smul k p;
    SM.smul_ok k p;
    GR.peq_sym (P.point_mul k p) (SM.smul k p);
    GR.peq_trans (pt wx wy wz) (SM.smul k p) (P.point_mul k p)

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
  pure (Seq.length vtx == 64 /\ Seq.length vty == 64 /\ Seq.length vtz == 64 /\
        Seq.length vsx == 4 /\ Seq.length vsy == 4 /\ Seq.length vsz == 4 /\
        SZ.v off + 4 <= 64 /\ SZ.fits (SZ.v off + 4))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
  A.pts_to sx #ps vsx ** A.pts_to sy #ps vsy ** A.pts_to sz #ps vsz **
  pure (Seq.length wx == 64 /\ Seq.length wy == 64 /\ Seq.length wz == 64 /\
        Seq.length vtx == 64 /\ Seq.length vty == 64 /\ Seq.length vtz == 64 /\
        Seq.length vsx == 4 /\ Seq.length vsy == 4 /\ Seq.length vsz == 4 /\
        SZ.v off + 4 <= 64 /\
        (forall (j: nat). j < 4 ==>
           (Seq.index wx (SZ.v off + j) == Seq.index vsx j /\
            Seq.index wy (SZ.v off + j) == Seq.index vsy j /\
            Seq.index wz (SZ.v off + j) == Seq.index vsz j)) /\
        (forall (j: nat). j < 64 ==>
           (j < SZ.v off \/ SZ.v off + 4 <= j) ==>
           (Seq.index wx j == Seq.index vtx j /\
            Seq.index wy j == Seq.index vty j /\
            Seq.index wz j == Seq.index vtz j)))
{
  table_store tx sx 4sz off;
  table_store ty sy 4sz off;
  table_store tz sz 4sz off;
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
               (p: erased P.proj_point) (n: erased nat)
               (#vtx #vty #vtz: erased (Seq.seq S64.t))
               (#pq: perm) (#vqx #vqy #vqz: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  pure (Seq.length vtx == 64 /\ Seq.length vty == 64 /\ Seq.length vtz == 64 /\
        pok vqx vqy vqz /\ oc (reveal p) /\
        rep vqx vqy vqz n (reveal p))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy ** A.pts_to qz #pq vqz **
  pure (Seq.length wx == 64 /\ Seq.length wy == 64 /\ Seq.length wz == 64 /\
        tok wx wy wz (reveal p) (reveal n) 16)
{
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  let z = S64.zero;
  let mut cx = [| z; 4sz |];
  Mem.track cx; A.pts_to_len cx;
  let mut cy = [| z; 4sz |];
  Mem.track cy; A.pts_to_len cy;
  let mut cz = [| z; 4sz |];
  Mem.track cz; A.pts_to_len cz;
  let mut nx = [| z; 4sz |];
  Mem.track nx; A.pts_to_len nx;
  let mut ny = [| z; 4sz |];
  Mem.track ny; A.pts_to_len ny;
  let mut nz = [| z; 4sz |];
  Mem.track nz; A.pts_to_len nz;
  A.pts_to_len cx; A.pts_to_len cy; A.pts_to_len cz;
  A.pts_to_len nx; A.pts_to_len ny; A.pts_to_len nz;

  set_infinity cx cy cz;
  with c0x c0y c0z. assert (A.pts_to cx c0x ** A.pts_to cy c0y ** A.pts_to cz c0z);
  pok_intro c0x c0y c0z;
  zero_ok c0x c0y c0z (reveal p);
  mul_zero (reveal n);
  rep_cong c0x c0y c0z 0 (0 * reveal n) (reveal p);

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
          Seq.length wx == 64 /\ Seq.length wy == 64 /\ Seq.length wz == 64 /\
          Seq.length wnx == nl /\ Seq.length wny == nl /\ Seq.length wnz == nl /\
          pok wcx wcy wcz /\
          rep wcx wcy wcz (SZ.v vd * reveal n) (reveal p) /\
          tok wx wy wz (reveal p) (reveal n) (SZ.v vd))
  decreases (16 - SZ.v (!d))
  {
    let vd = !d;
    with wx wy wz. assert (A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz);
    with wcx wcy wcz. assert (A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz);
    pok_elim wcx wcy wcz;
    pok_elim vqx vqy vqz;
    store_off (SZ.v vd);
    store3 tx ty tz cx cy cz (SZ.mul vd 4sz);
    with wx' wy' wz'. assert (A.pts_to tx wx' ** A.pts_to ty wy' ** A.pts_to tz wz');
    tbl_shape wx wx' wcx (SZ.v vd);
    tbl_shape wy wy' wcy (SZ.v vd);
    tbl_shape wz wz' wcz (SZ.v vd);
    ent_intro wx' wy' wz' wcx wcy wcz (reveal p) (reveal n) (SZ.v vd);
    tok_extend wx wy wz wx' wy' wz' (reveal p) (reveal n) (SZ.v vd);
    point_add nx ny nz cx cy cz qx qy qz;
    with wnx wny wnz. assert (A.pts_to nx wnx ** A.pts_to ny wny ** A.pts_to nz wnz);
    mul_nat (SZ.v vd) (reveal n);
    add_ok wcx wcy wcz vqx vqy vqz wnx wny wnz (reveal p)
           (SZ.v vd * reveal n) (reveal n);
    mul_succ (SZ.v vd) (reveal n);
    fcopy cx nx; fcopy cy ny; fcopy cz nz;
    with c1x c1y c1z. assert (A.pts_to cx c1x ** A.pts_to cy c1y ** A.pts_to cz c1z);
    pok_intro c1x c1y c1z;
    rep_fcopy wnx wny wnz c1x c1y c1z (SZ.v vd * reveal n + reveal n) (reveal p);
    rep_cong c1x c1y c1z (SZ.v vd * reveal n + reveal n)
             ((SZ.v vd + 1) * reveal n) (reveal p);
    d := SZ.add vd 1sz;
  };
  let vd = !d;
  sz_sixteen vd;
  Mem.wipe nz 4sz;
  Mem.wipe ny 4sz;
  Mem.wipe nx 4sz;
  Mem.wipe cz 4sz;
  Mem.wipe cy 4sz;
  Mem.wipe cx 4sz;
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

(** One Jacobian doubling, in place, with the scratch triple as its
    temporaries. *)
inline_for_extraction
fn win_jdbl (ox oy oz ux uy uz: A.array S64.t)
            (p: erased P.proj_point) (e: erased nat)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        pok vox voy voz /\ oc (reveal p) /\
        jrs vox voy voz e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        pok wx wy wz /\ jrs wx wy wz (2 * reveal e) (reveal p))
{
  pok_elim vox voy voz;
  jdouble ox oy oz ux uy uz;
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  jdbl_ok vox voy voz wx wy wz p (reveal e);
  pok_intro wx wy wz;
  ()
}

(** Into Jacobian coordinates, and back out. *)
inline_for_extraction
fn win_jin (ox oy oz ux uy uz: A.array S64.t)
            (p: erased P.proj_point) (e: erased nat)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        pok vox voy voz /\ oc (reveal p) /\
        rep vox voy voz e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        pok wx wy wz /\ jrs wx wy wz (reveal e) (reveal p))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  pok_elim vox voy voz;
  to_j ox oy oz ux uy;
  with jx jy. assert (A.pts_to ox jx ** A.pts_to oy jy);
  jin_ok vox voy voz jx jy p (reveal e);
  pok_intro jx jy voz;
  ()
}

inline_for_extraction
fn win_jout (ox oy oz ux uy uz: A.array S64.t)
            (p: erased P.proj_point) (e: erased nat)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        pok vox voy voz /\ oc (reveal p) /\
        jrs vox voy voz e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        pok wx wy wz /\ rep wx wy wz (reveal e) (reveal p))
{
  pok_elim vox voy voz;
  to_h ox oy oz ux;
  with wx wz. assert (A.pts_to ox wx ** A.pts_to oz wz);
  jout_ok vox voy voz wx wz p (reveal e);
  pok_intro wx voy wz;
  ()
}

(** Four of them, which is the doubling half of a rung: into Jacobian
    coordinates, four doublings there, and back. *)
fn win_dbl4 (ox oy oz ux uy uz: A.array S64.t)
            (p: erased P.proj_point) (e: erased nat)
            (#vox #voy #voz: erased (Seq.seq S64.t))
            (#vux #vuy #vuz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        pok vox voy voz /\ oc (reveal p) /\
        rep vox voy voz e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        pok wx wy wz /\ rep wx wy wz (16 * reveal e) (reveal p))
{
  win_jin ox oy oz ux uy uz p e;
  with a0x a0y a0z. assert (A.pts_to ox a0x ** A.pts_to oy a0y ** A.pts_to oz a0z);
  win_jdbl ox oy oz ux uy uz p e;
  with a1x a1y a1z. assert (A.pts_to ox a1x ** A.pts_to oy a1y ** A.pts_to oz a1z);
  jrs_cong a1x a1y a1z (2 * reveal e) (2 * reveal e) p;
  win_jdbl ox oy oz ux uy uz p (hide (2 * reveal e));
  with a2x a2y a2z. assert (A.pts_to ox a2x ** A.pts_to oy a2y ** A.pts_to oz a2z);
  jrs_cong a2x a2y a2z (2 * (2 * reveal e)) (4 * reveal e) p;
  win_jdbl ox oy oz ux uy uz p (hide (4 * reveal e));
  with a3x a3y a3z. assert (A.pts_to ox a3x ** A.pts_to oy a3y ** A.pts_to oz a3z);
  jrs_cong a3x a3y a3z (2 * (4 * reveal e)) (8 * reveal e) p;
  win_jdbl ox oy oz ux uy uz p (hide (8 * reveal e));
  with a4x a4y a4z. assert (A.pts_to ox a4x ** A.pts_to oy a4y ** A.pts_to oz a4z);
  jrs_cong a4x a4y a4z (2 * (8 * reveal e)) (16 * reveal e) p;
  win_jout ox oy oz ux uy uz p (hide (16 * reveal e));
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
           (p: erased P.proj_point) (n: erased nat)
           (e: erased nat) (d: erased nat)
           (#vox #voy #voz: erased (Seq.seq S64.t))
           (#vux #vuy #vuz: erased (Seq.seq S64.t))
           (#vsx #vsy #vsz: erased (Seq.seq S64.t))
           (#ptx #pty #ptz: perm) (#vtx #vty #vtz: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz **
  A.pts_to sx vsx ** A.pts_to sy vsy ** A.pts_to sz vsz **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty ** A.pts_to tz #ptz vtz **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\ Seq.length vuz == nl /\
        Seq.length vsx == nl /\ Seq.length vsy == nl /\ Seq.length vsz == nl /\
        Seq.length vtx == 64 /\ Seq.length vty == 64 /\ Seq.length vtz == 64 /\
        pok vox voy voz /\ oc (reveal p) /\
        rep vox voy voz e (reveal p) /\
        tok vtx vty vtz (reveal p) (reveal n) 16 /\
        reveal d < 16 /\ S64.v dig == reveal d)
ensures exists* (wx wy wz wux wuy wuz wsx wsy wsz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz **
  A.pts_to tx #ptx vtx ** A.pts_to ty #pty vty ** A.pts_to tz #ptz vtz **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\ Seq.length wuz == nl /\
        Seq.length wsx == nl /\ Seq.length wsy == nl /\ Seq.length wsz == nl /\
        pok wx wy wz /\
        rep wx wy wz (reveal e + reveal d * reveal n) (reveal p))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz;
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  pok_elim vox voy voz;
  entry_fits (reveal d);
  table_select sx tx 4sz dig d;
  table_select sy ty 4sz dig d;
  table_select sz tz 4sz dig d;
  entry_def vtx (reveal d); entry_def vty (reveal d); entry_def vtz (reveal d);
  tok_get vtx vty vtz (reveal p) (reveal n) (reveal d);
  with wsx wsy wsz. assert (A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz);
  pok_elim wsx wsy wsz;
  point_add ux uy uz ox oy oz sx sy sz;
  with u1x u1y u1z. assert (A.pts_to ux u1x ** A.pts_to uy u1y ** A.pts_to uz u1z);
  add_ok vox voy voz wsx wsy wsz u1x u1y u1z (reveal p) (reveal e)
         (reveal d * reveal n);
  fcopy ox ux; fcopy oy uy; fcopy oz uz;
  with w1x w1y w1z. assert (A.pts_to ox w1x ** A.pts_to oy w1y ** A.pts_to oz w1z);
  pok_intro w1x w1y w1z;
  rep_fcopy u1x u1y u1z w1x w1y w1z (reveal e + reveal d * reveal n) (reveal p);
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
        GR.on_curve (P.point_mul (kv vk) (pt vqx vqy vqz)) /\
        GR.peq (pt wx wy wz) (P.point_mul (kv vk) (pt vqx vqy vqz)))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz;
  A.pts_to_len ks;
  kv_bnd vk;
  oc_intro (pt vqx vqy vqz);
  let z = S64.zero;
  let mut tx = [| z; 64sz |];
  Mem.track tx; A.pts_to_len tx;
  let mut ty = [| z; 64sz |];
  Mem.track ty; A.pts_to_len ty;
  let mut tz = [| z; 64sz |];
  Mem.track tz; A.pts_to_len tz;
  let mut ux = [| z; 4sz |];
  Mem.track ux; A.pts_to_len ux;
  let mut uy = [| z; 4sz |];
  Mem.track uy; A.pts_to_len uy;
  let mut uz = [| z; 4sz |];
  Mem.track uz; A.pts_to_len uz;
  let mut sx = [| z; 4sz |];
  Mem.track sx; A.pts_to_len sx;
  let mut sy = [| z; 4sz |];
  Mem.track sy; A.pts_to_len sy;
  let mut sz = [| z; 4sz |];
  Mem.track sz; A.pts_to_len sz;
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz;

  pok_intro vqx vqy vqz;
  rep_one vqx vqy vqz (pt vqx vqy vqz);
  build_table tx ty tz qx qy qz (hide (pt vqx vqy vqz)) (hide 1);
  set_infinity ox oy oz;
  with o0x o0y o0z. assert (A.pts_to ox o0x ** A.pts_to oy o0y ** A.pts_to oz o0z);
  pok_intro o0x o0y o0z;
  zero_ok o0x o0y o0z (pt vqx vqy vqz);
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
          Seq.length wtx == 64 /\ Seq.length wty == 64 /\ Seq.length wtz == 64 /\
          tok wtx wty wtz (pt vqx vqy vqz) 1 16 /\
          pok wx wy wz /\
          rep wx wy wz (kv vk / pow2 (SZ.v vj)) (pt vqx vqy vqz))
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
    rep_cong wx wy wz
             (16 * (kv vk / pow2 (SZ.v vj)) + kv vk / pow2 (SZ.v j2) % 16)
             (kv vk / pow2 (SZ.v j2)) (pt vqx vqy vqz);
    j := j2;
  };
  let vj = !j;
  sz_zero vj;
  bot_div (kv vk);
  with wx wy wz. assert (A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz);
  pok_elim wx wy wz;
  win_done wx wy wz (pt vqx vqy vqz) (kv vk);
  Mem.wipe sz 4sz;
  Mem.wipe sy 4sz;
  Mem.wipe sx 4sz;
  Mem.wipe uz 4sz;
  Mem.wipe uy 4sz;
  Mem.wipe ux 4sz;
  Mem.wipe tz 64sz;
  Mem.wipe ty 64sz;
  Mem.wipe tx 64sz;
  ()
}

#pop-options
