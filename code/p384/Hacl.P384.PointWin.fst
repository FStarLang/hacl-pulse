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

(** What the P-384 windows share.

    A window spends several doublings and one addition per digit of the
    scalar, against a table of precomputed multiples read with a lookup
    that must not let the digit reach the address bus, which is
    {!Hacl.Bignum.Base.table_select}.  The windows themselves are
    {!Hacl.P384.PointMulV} (variable base) and {!Hacl.P384.PointMulG}
    (the generator); this module has the table layout, the opaque
    representation invariant, and the doublings.

    What makes a window legal is {!Spec.P384.Smul}: it computes the
    multiple in a different order from the specification's ladder, so it
    does not produce the specification's projective triple, only one
    equivalent to it.  Everything here is therefore stated up to [peq], and
    the callers discharge that at the point where they leave projective
    coordinates.

    This began as {!Hacl.P256.PointWin} on six limbs; the comments below
    that explain why the proof is shaped as it is were written there, and
    hold here with the 78-digit prime replaced by a 116-digit one. *)
module Hacl.P384.PointWin

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Impl.Limb64
open Hacl.Impl.Table
open Hacl.Bignum.Base
open Hacl.P384.Field
open Hacl.P384.Point

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module S64 = Hacl.Secret.UInt64
module P = Spec.P384
module GR = Spec.P384.Group
module SM = Spec.P384.Smul
module J = Spec.P384.Jac
module JS = Spec.P384.JacSv
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module Mem = Hacl.Mem

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 The table, as a flat array}

    One array per coordinate, sixteen four-limb entries each.  [entry] is
    total -- out of range it is the empty sequence -- so that the
    invariants below typecheck without carrying the bound on [d] into every
    one of them. *)

let entry (v: Seq.seq S64.t) (d: nat) : Seq.seq S64.t =
  if d * 6 + 6 <= Seq.length v
  then Seq.slice v (d * 6) (d * 6 + 6)
  else Seq.empty #S64.t

let entry_fits (d: nat) : Lemma (requires d < 16) (ensures d * 6 + 6 <= 96)
  = Math.lemma_mult_le_right 6 (d + 1) 16

#push-options "--ifuel 1"
let entry_def (v: Seq.seq S64.t) (d: nat)
  : Lemma (requires d * 6 + 6 <= Seq.length v)
          (ensures entry v d == Seq.slice v (d * 6) (d * 6 + 6))
  = ()
#pop-options

#push-options "--ifuel 1 --z3rlimit 200"

(** Writing one entry leaves the others where they were. *)
let entry_untouched (v v': Seq.seq S64.t) (e d: nat)
  : Lemma (requires Seq.length v == 96 /\ Seq.length v' == 96 /\
                    e < 16 /\ d < 16 /\ ~(d == e) /\
                    (forall (j: nat). j < 96 ==>
                       (j < e * 6 \/ e * 6 + 6 <= j) ==>
                       Seq.index v' j == Seq.index v j))
          (ensures entry v' d == entry v d)
  = entry_fits d;
    entry_fits e;
    entry_def v d;
    entry_def v' d;
    if d < e then Math.lemma_mult_le_right 6 (d + 1) e
             else Math.lemma_mult_le_right 6 (e + 1) d;
    Seq.lemma_eq_intro (Seq.slice v' (d * 6) (d * 6 + 6))
                       (Seq.slice v (d * 6) (d * 6 + 6))

(** And it puts what was asked for into the one it does write. *)
let entry_written (v': Seq.seq S64.t) (src: Seq.seq S64.t) (e: nat)
  : Lemma (requires Seq.length v' == 96 /\ Seq.length src == 6 /\ e < 16 /\
                    (forall (j: nat). j < 6 ==>
                       Seq.index v' (e * 6 + j) == Seq.index src j))
          (ensures entry v' e == src)
  = entry_fits e;
    entry_def v' e;
    Seq.lemma_eq_intro (Seq.slice v' (e * 6) (e * 6 + 6)) src

(** What one store does to a table, entry by entry rather than limb by
    limb. *)
let tbl_shape (v v' src: Seq.seq S64.t) (e: nat)
  : Lemma (requires Seq.length v == 96 /\ Seq.length v' == 96 /\
                    Seq.length src == 6 /\ e < 16 /\
                    (forall (j: nat). j < 6 ==>
                       Seq.index v' (e * 6 + j) == Seq.index src j) /\
                    (forall (j: nat). j < 96 ==>
                       (j < e * 6 \/ e * 6 + 6 <= j) ==>
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
    that unfold into field equations over a 116-digit prime.  Any verification
    condition that carries a few of them is minutes of Z3 time -- and a
    Pulse function's precondition is carried through its whole body, so the
    cost is paid on every goal, down to [2 * (4 * e) == 8 * e].

    So the pair is bundled into one opaque predicate.  The Pulse contracts
    below mention only [rep], [oc] and [pok].

    [pok] is opaque too: the field is in Montgomery form and [felem]
    unfolds to [num v < P.prime], an evaluation of the whole 384-bit number
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
    [fev], and on this curve [fev v] is [num v * rinv % P.prime] -- it
    carries the Montgomery constants, two 116-digit literals, in every
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
          (ensures pt_ok x y z /\ Seq.length x == 6 /\
                   Seq.length y == 6 /\ Seq.length z == 6)
  = reveal_opaque (`%pok) pok

let rep_elim (x y z: Seq.seq S64.t) (n: nat) (p: P.proj_point)
  : Lemma (requires rep x y z n p)
          (ensures GR.on_curve (pt x y z) /\ GR.peq (pt x y z) (SM.smul n p))
  = reveal_opaque (`%rep) rep

(** Where entry [d] starts, and that it is addressable. *)
let store_off (d: nat)
  : Lemma (requires d < 16)
          (ensures d * 6 + 6 <= 96 /\ SZ.fits (d * 6) /\ SZ.fits (d * 6 + 6))
  = entry_fits d;
    SZ.fits_lte (d * 6) 96;
    SZ.fits_lte (d * 6 + 6) 96

#pop-options

(** {2 The spec-side steps}

    Each is one lemma of {!Spec.P384.Smul} with its hypotheses arranged as
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
    {!Hacl.P384.Field.fcopy} leaves it. *)
let rep_fcopy (x y z x' y' z': Seq.seq S64.t) (n: nat) (p: P.proj_point)
  : Lemma (requires rep x y z n p /\
                    fev x' == fev x /\ fev y' == fev y /\ fev z' == fev z)
          (ensures rep x' y' z' n p)
  = reveal_opaque (`%rep) rep

(** The Jacobian run's invariant, over sequences for the same reason as
    {!rep}: "[x], [y], [z] read as a Jacobian triple equivalent to [n]
    copies of [p]" ({!Spec.P384.Jac.jr}). *)
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
    so the two are related by [peq] and not by equality; {!Spec.P384.Smul}
    is where that is proved. *)
let win_done (wx wy wz: Seq.seq S64.t) (p: P.proj_point) (k: nat)
  : Lemma (requires oc p /\ rep wx wy wz k p /\ k < pow2 384)
          (ensures GR.on_curve (pt wx wy wz) /\
                   GR.on_curve (P.point_mul k p) /\
                   GR.peq (pt wx wy wz) (P.point_mul k p))
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.point_mul_is_smul k p;
    SM.smul_ok k p;
    GR.peq_sym (P.point_mul k p) (SM.smul k p);
    GR.peq_trans (pt wx wy wz) (SM.smul k p) (P.point_mul k p)

let sz_zero (x: SZ.t) : Lemma (requires SZ.gt x 0sz == false)
                              (ensures SZ.v x == 0) = ()

#pop-options

(** {2 Building tables} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn set_infinity (ox oy oz: A.array S64.t)
                (#vox #voy #voz: erased (Seq.seq S64.t))
requires A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz **
  pure (Seq.length vox == 6 /\ Seq.length voy == 6 /\ Seq.length voz == 6)
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  pure (pt_ok wx wy wz /\ pt wx wy wz == P.point_at_infinity)
{
  fzero ox;
  fone oy;
  fzero oz;
}

(** The three coordinates of one entry, stored together. *)
inline_for_extraction
fn store3 (tx ty tz: A.array S64.t) (sx sy sz: A.array S64.t) (off: SZ.t)
          (#vtx #vty #vtz: erased (Seq.seq S64.t)) (#ps: perm)
          (#vsx #vsy #vsz: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz **
  A.pts_to sx #ps vsx ** A.pts_to sy #ps vsy ** A.pts_to sz #ps vsz **
  pure (Seq.length vtx == 96 /\ Seq.length vty == 96 /\ Seq.length vtz == 96 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\ Seq.length vsz == 6 /\
        SZ.v off + 6 <= 96 /\ SZ.fits (SZ.v off + 6))
ensures exists* (wx wy wz: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz **
  A.pts_to sx #ps vsx ** A.pts_to sy #ps vsy ** A.pts_to sz #ps vsz **
  pure (Seq.length wx == 96 /\ Seq.length wy == 96 /\ Seq.length wz == 96 /\
        Seq.length vtx == 96 /\ Seq.length vty == 96 /\ Seq.length vtz == 96 /\
        Seq.length vsx == 6 /\ Seq.length vsy == 6 /\ Seq.length vsz == 6 /\
        SZ.v off + 6 <= 96 /\
        (forall (j: nat). j < 6 ==>
           (Seq.index wx (SZ.v off + j) == Seq.index vsx j /\
            Seq.index wy (SZ.v off + j) == Seq.index vsy j /\
            Seq.index wz (SZ.v off + j) == Seq.index vsz j)) /\
        (forall (j: nat). j < 96 ==>
           (j < SZ.v off \/ SZ.v off + 6 <= j) ==>
           (Seq.index wx j == Seq.index vtx j /\
            Seq.index wy j == Seq.index vty j /\
            Seq.index wz j == Seq.index vtz j)))
{
  table_store tx sx 6sz off;
  table_store ty sy 6sz off;
  table_store tz sz 6sz off;
}

#pop-options


(** {2 Doublings}

    The doublings are a function apiece.  The solver's work grows with what
    it can see, and [peq], [on_curve] and [pt_ok] all unfold into field
    equations over the prime; with several doublings in one body the
    context is large enough that [2 * (4 * e) == 8 * e] takes minutes.
    Behind a contract each doubling contributes three facts and nothing
    else. *)

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
  pure (Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        pok vox voy voz /\ oc (reveal p) /\
        jrs vox voy voz e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
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
  pure (Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        pok vox voy voz /\ oc (reveal p) /\
        rep vox voy voz e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
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
  pure (Seq.length vux == 6 /\ Seq.length vuy == 6 /\ Seq.length vuz == 6 /\
        pok vox voy voz /\ oc (reveal p) /\
        jrs vox voy voz e (reveal p))
ensures exists* (wx wy wz wux wuy wuz: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz **
  pure (Seq.length wux == 6 /\ Seq.length wuy == 6 /\ Seq.length wuz == 6 /\
        pok wx wy wz /\ rep wx wy wz (reveal e) (reveal p))
{
  pok_elim vox voy voz;
  to_h ox oy oz ux;
  with wx wz. assert (A.pts_to ox wx ** A.pts_to oz wz);
  jout_ok vox voy voz wx wz p (reveal e);
  pok_intro wx voy wz;
  ()
}

#pop-options

(** {2 The scalar} *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** The scalar, as a number.  Named so that the invariant below does not
    have to spell it out four times. *)
let kv (vk: Seq.seq S64.t) : GTot nat = num vk

let kv_bnd (vk: Seq.seq S64.t)
  : Lemma (requires Seq.length vk == 6)
          (ensures kv vk < pow2 384)
  = eval_bnd (vals vk);
    facts ()

#pop-options
