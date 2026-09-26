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

    What makes this legal is {!Spec.Ed25519.Smul}: the window computes the
    multiple in a different order from the specification's ladder, so it
    does not produce the specification's extended quadruple, only one
    equivalent to it.  Everything here is therefore stated up to
    [point_equal], and the callers discharge that where they leave
    extended coordinates -- compression and the verification equation both
    respect it.

    Two things differ from the prime-curve windows.  A point here has four
    coordinates rather than three, so there are four tables; and the
    scalar arrives as thirty-two bytes rather than as four limbs, so the
    digit is a nibble of a byte rather than of a limb.  Neither straddles:
    four divides eight, so a nibble is one shift and one mask.  The bridge
    from bytes to the number they denote is
    {!Spec.Ed25519.Smul.nibble_of_bytes}. *)
module Hacl.Ed25519.PointWin

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum51
open Spec.Curve25519.Field
open Hacl.Curve25519.Field
open Hacl.Bignum.Base
open Hacl.Ed25519.Point

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast
module CF = Hacl.Curve25519.Field
module C = Spec.Curve25519
module E = Spec.Ed25519
module GR = Spec.Ed25519.Group
module SM = Spec.Ed25519.Smul
module B = Hacl.Spec.Bytes
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical

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

    Everything below says of some quadruple that it is on the curve and is
    equivalent to a multiple of the base point.  Said directly, that is
    [GR.on_curve] and [E.point_equal], both of which are transparent
    definitions that unfold into field equations over [2^255 - 19].  Any
    verification condition that carries a few of them is minutes of Z3
    time -- and a Pulse function's precondition is carried through its
    whole body, so the cost is paid on every goal, down to
    [2 * (4 * e) == 8 * e].

    So the pair is bundled into one opaque predicate, and the Pulse
    contracts below mention only [rep], [oc] and [pok].

    [rep] takes the four limb sequences rather than the point they read
    as.  That is the lesson P-256 taught: [pt w x y z] is four
    applications of [fev], and [fev v] is [eval v % prime], which carries
    a 78-digit literal.  A rung has several quadruples in flight, and
    stating its invariant over points puts a dozen of those literals into
    a context that never needs one. *)

[@@"opaque_to_smt"]
let oc (p: E.ext_point) : prop = GR.on_curve p

[@@"opaque_to_smt"]
let rep (x y z t: Seq.seq S64.t) (n: nat) (p: E.ext_point) : prop =
  GR.on_curve (pt x y z t) /\ E.point_equal (pt x y z t) (SM.smul n p)

[@@"opaque_to_smt"]
let pok (x y z t: Seq.seq S64.t) : prop = pt_ok x y z t

let oc_intro (p: E.ext_point) : Lemma (requires GR.on_curve p) (ensures oc p)
  = reveal_opaque (`%oc) oc

let pok_intro (x y z t: Seq.seq S64.t)
  : Lemma (requires pt_ok x y z t) (ensures pok x y z t)
  = reveal_opaque (`%pok) pok

let pok_elim (x y z t: Seq.seq S64.t)
  : Lemma (requires pok x y z t)
          (ensures pt_ok x y z t /\ Seq.length x == nl /\
                   Seq.length y == nl /\ Seq.length z == nl /\
                   Seq.length t == nl)
  = reveal_opaque (`%pok) pok

let rep_elim (x y z t: Seq.seq S64.t) (n: nat) (p: E.ext_point)
  : Lemma (requires rep x y z t n p)
          (ensures GR.on_curve (pt x y z t) /\
                   E.point_equal (pt x y z t) (SM.smul n p))
  = reveal_opaque (`%rep) rep

(** {2 What the table holds}

    [ent tx ty tz tt p d] is "entry [d] is the [d]-th multiple of [p]", up
    to equivalence -- the entries are built by repeated addition, so they
    are not the specification's quadruples.

    Everything here is bookkeeping about which table slots a store did and
    did not touch, and none of it needs to see the curve; the value of an
    entry is carried by the opaque {!rep}, so none of it does. *)

[@@"opaque_to_smt"]
let ent (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (n d: nat) : prop =
  pok (entry tx d) (entry ty d) (entry tz d) (entry tt d) /\
  rep (entry tx d) (entry ty d) (entry tz d) (entry tt d) (d * n) p

let ent_intro (tx ty tz tt sx sy sz st: Seq.seq S64.t) (p: E.ext_point)
              (n d: nat)
  : Lemma (requires entry tx d == sx /\ entry ty d == sy /\
                    entry tz d == sz /\ entry tt d == st /\
                    pok sx sy sz st /\ rep sx sy sz st (d * n) p)
          (ensures ent tx ty tz tt p n d)
  = reveal_opaque (`%ent) ent

(** An entry that was not written is still what it was. *)
let ent_eq (tx ty tz tt tx' ty' tz' tt': Seq.seq S64.t) (p: E.ext_point)
           (n d: nat)
  : Lemma (requires ent tx ty tz tt p n d /\ entry tx' d == entry tx d /\
                    entry ty' d == entry ty d /\ entry tz' d == entry tz d /\
                    entry tt' d == entry tt d)
          (ensures ent tx' ty' tz' tt' p n d)
  = reveal_opaque (`%ent) ent

let tok (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (n: nat) (upto: nat) : prop =
  forall (d: nat). d < upto ==> ent tx ty tz tt p n d

(** Reading one entry back out, as a lemma so that the caller's query never
    has to instantiate the quantifier itself. *)
let tok_get (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (n d: nat)
  : Lemma (requires tok tx ty tz tt p n 16 /\ d < 16)
          (ensures pok (entry tx d) (entry ty d) (entry tz d) (entry tt d) /\
                   rep (entry tx d) (entry ty d) (entry tz d) (entry tt d)
                       (d * n) p)
  = reveal_opaque (`%ent) ent

(** The entry that was just written is the one the index names.  Stated as
    a lemma of its own because the [dd == e] case of {!tok_extend} is not
    the triviality it looks: left to itself the solver reproves the entry
    from scratch rather than matching it, and with the curve in scope that
    is twenty minutes and a timeout. *)
let ent_same (tx ty tz tt: Seq.seq S64.t) (p: E.ext_point) (n e dd: nat)
  : Lemma (requires ent tx ty tz tt p n e /\ dd == e)
          (ensures ent tx ty tz tt p n dd)
  = ()

#push-options "--ifuel 1 --z3rlimit 100"
let tok_extend (tx ty tz tt tx' ty' tz' tt': Seq.seq S64.t) (p: E.ext_point)
               (n e: nat)
  : Lemma (requires tok tx ty tz tt p n e /\ e < 16 /\
                    ent tx' ty' tz' tt' p n e /\
                    (forall (dd: nat). dd < e ==>
                       (entry tx' dd == entry tx dd /\
                        entry ty' dd == entry ty dd /\
                        entry tz' dd == entry tz dd /\
                        entry tt' dd == entry tt dd)))
          (ensures tok tx' ty' tz' tt' p n (e + 1))
  = introduce forall (dd: nat). dd < e + 1 ==> ent tx' ty' tz' tt' p n dd
    with introduce _ ==> _
    with (if dd < e then ent_eq tx ty tz tt tx' ty' tz' tt' p n dd
                    else ent_same tx' ty' tz' tt' p n e dd)
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

    Each is one lemma of {!Spec.Ed25519.Smul} with its hypotheses arranged
    as the Pulse function that uses it leaves them, so that at the point of
    use nothing remains to be discharged. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

let rep_cong (x y z t: Seq.seq S64.t) (a b: nat) (p: E.ext_point)
  : Lemma (requires rep x y z t a p /\ a == b) (ensures rep x y z t b p) = ()

(** The scale arithmetic, proved where nothing else is in scope.  Both are
    one step of distributivity, but a product of two variables asked for
    in the middle of a loop whose context carries the addition law is the
    difference between a second and twenty minutes. *)
let mul_zero (b: nat) : Lemma (0 * b == 0) = ()

let mul_succ (a b: nat) : Lemma (a * b + b == (a + 1) * b)
  = Math.distributivity_add_left a 1 b

let mul_one (a: nat) : Lemma (a * 1 == a) = ()

let dbl_ok (ox oy oz ot wx wy wz wt: Seq.seq S64.t) (p: E.ext_point) (e: nat)
  : Lemma (requires oc p /\ rep ox oy oz ot e p /\
                    pt wx wy wz wt == E.point_double (pt ox oy oz ot))
          (ensures rep wx wy wz wt (2 * e) p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.smul_dbl_congr e p (pt ox oy oz ot)

let add_ok (ox oy oz ot sx sy sz st wx wy wz wt: Seq.seq S64.t)
           (p: E.ext_point) (e d: nat)
  : Lemma (requires oc p /\ rep ox oy oz ot e p /\ rep sx sy sz st d p /\
                    pt wx wy wz wt ==
                      E.point_add (pt ox oy oz ot) (pt sx sy sz st))
          (ensures rep wx wy wz wt (e + d) p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.smul_add_congr e d p (pt ox oy oz ot) (pt sx sy sz st)

let zero_ok (wx wy wz wt: Seq.seq S64.t) (p: E.ext_point)
  : Lemma (requires oc p /\ pt wx wy wz wt == E.point_at_infinity)
          (ensures rep wx wy wz wt 0 p)
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    GR.point_at_infinity_on_curve ();
    SM.smul_zero p;
    GR.point_equal_refl E.point_at_infinity

(** A point is its own first multiple.  The scale below is one for a
    variable-base window; a fixed-base one passes a power of two. *)
let rep_one (x y z t: Seq.seq S64.t)
  : Lemma (requires oc (pt x y z t)) (ensures rep x y z t 1 (pt x y z t))
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.smul_one (pt x y z t);
    SM.smul_ok 1 (pt x y z t);
    GR.point_equal_sym (SM.smul 1 (pt x y z t)) (pt x y z t)

(** Leaving the abstraction: what the caller of the window is told.  The
    specification's own ladder produces a different quadruple from the
    window, so the two are related by [point_equal] and not by equality;
    {!Spec.Ed25519.Smul} is where that is proved. *)
let win_done (wx wy wz wt: Seq.seq S64.t) (p: E.ext_point)
             (k: Seq.lseq S8.t 32)
  : Lemma (requires oc p /\ rep wx wy wz wt (B.le_nat k) p)
          (ensures GR.on_curve (pt wx wy wz wt) /\
                   GR.on_curve (E.point_mul k p) /\
                   E.point_equal (pt wx wy wz wt) (E.point_mul k p))
  = reveal_opaque (`%oc) oc;
    reveal_opaque (`%rep) rep;
    SM.point_mul_is_smul k p;
    SM.smul_ok (B.le_nat k) p;
    GR.point_equal_sym (E.point_mul k p) (SM.smul (B.le_nat k) p);
    GR.point_equal_trans (pt wx wy wz wt) (SM.smul (B.le_nat k) p)
                         (E.point_mul k p)

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

let top_div (k: Seq.lseq S8.t 32)
  : Lemma (B.le_nat k / pow2 256 == 0)
  = B.le_nat_bound k; Math.small_div (B.le_nat k) (pow2 256)

let bot_div (k: nat) : Lemma (k / pow2 0 == k) = assert_norm (pow2 0 == 1)

let sz_sixteen (x: SZ.t) : Lemma (requires SZ.lt x 16sz == false /\ SZ.v x <= 16)
                                 (ensures SZ.v x == 16) = ()

#pop-options

(** {2 Reading a nibble of the scalar}

    Bit offset [i], a multiple of four, names byte [i / 8] and shift
    [i % 8], which is zero or four.  Nothing straddles, so this is one
    load, one shift and one mask; {!Spec.Ed25519.Smul.nibble_of_bytes}
    says the result is the digit of the number the bytes denote. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

inline_for_extraction
fn nibble (ks: A.array S8.t) (i: SZ.t)
          (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires A.pts_to ks #pk vk **
  pure (Seq.length vk == 32 /\ SZ.v i < 256 /\ SZ.v i % 4 == 0)
returns d: S64.t
ensures A.pts_to ks #pk vk **
  pure (Seq.length vk == 32 /\
        S64.v d == B.le_nat vk / pow2 (SZ.v i) % 16 /\ S64.v d < 16)
{
  A.pts_to_len ks;
  let bj = SZ.div i 8sz;
  let sh = SZ.sizet_to_uint32 (SZ.rem i 8sz);
  assert_norm (pow2 32 > 8);
  Math.small_mod (SZ.v (SZ.rem i 8sz)) (pow2 32);
  assert (pure (SZ.v bj == SZ.v i / 8 /\ U32.v sh == SZ.v i % 8));
  let byte = A.(ks.(bj));
  let w = Cast.u8_to_u64 byte;
  let sr = S64.shift_right w sh;
  assert (pure (S64.v sr == S64.v w / pow2 (SZ.v i % 8)));
  assert_norm (pow2 4 - 1 == 15);
  UInt.logand_mask #64 (S64.v sr) 4;
  let d = S64.logand sr (S64.classify 15uL);
  SM.nibble_of_bytes vk (SZ.v i);
  d
}

#pop-options

(** {2 Building the table}

    Entry [d] is [d] copies of the point added together, computed by
    walking up from the point at infinity: sixteen additions, one of which
    is wasted on the entry that is never used.  Spending it buys a loop
    with one case rather than three. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** The four coordinates of one entry, stored together. *)
inline_for_extraction
fn store4 (tx ty tz tt: A.array S64.t) (sx sy sz st: A.array S64.t)
          (off: SZ.t)
          (#vtx #vty #vtz #vtt: erased (Seq.seq S64.t)) (#ps: perm)
          (#vsx #vsy #vsz #vst: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz ** A.pts_to tt vtt **
  A.pts_to sx #ps vsx ** A.pts_to sy #ps vsy **
  A.pts_to sz #ps vsz ** A.pts_to st #ps vst **
  pure (Seq.length vtx == 80 /\ Seq.length vty == 80 /\
        Seq.length vtz == 80 /\ Seq.length vtt == 80 /\
        Seq.length vsx == 5 /\ Seq.length vsy == 5 /\
        Seq.length vsz == 5 /\ Seq.length vst == 5 /\
        SZ.v off + 5 <= 80 /\ SZ.fits (SZ.v off + 5))
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz ** A.pts_to tt wt **
  A.pts_to sx #ps vsx ** A.pts_to sy #ps vsy **
  A.pts_to sz #ps vsz ** A.pts_to st #ps vst **
  pure (Seq.length wx == 80 /\ Seq.length wy == 80 /\
        Seq.length wz == 80 /\ Seq.length wt == 80 /\
        Seq.length vtx == 80 /\ Seq.length vty == 80 /\
        Seq.length vtz == 80 /\ Seq.length vtt == 80 /\
        Seq.length vsx == 5 /\ Seq.length vsy == 5 /\
        Seq.length vsz == 5 /\ Seq.length vst == 5 /\
        SZ.v off + 5 <= 80 /\
        (forall (j: nat). j < 5 ==>
           (Seq.index wx (SZ.v off + j) == Seq.index vsx j /\
            Seq.index wy (SZ.v off + j) == Seq.index vsy j /\
            Seq.index wz (SZ.v off + j) == Seq.index vsz j /\
            Seq.index wt (SZ.v off + j) == Seq.index vst j)) /\
        (forall (j: nat). j < 80 ==>
           (j < SZ.v off \/ SZ.v off + 5 <= j) ==>
           (Seq.index wx j == Seq.index vtx j /\
            Seq.index wy j == Seq.index vty j /\
            Seq.index wz j == Seq.index vtz j /\
            Seq.index wt j == Seq.index vtt j)))
{
  table_store tx sx 5sz off;
  table_store ty sy 5sz off;
  table_store tz sz 5sz off;
  table_store tt st 5sz off;
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** [build_table tx ty tz tt q p n] fills the sixteen entries with
    [0]Q .. [15]Q, where [Q] is the [n]-th multiple of [P]: entry [d] is
    recorded as the [d n]-th multiple of [P], not the [d]-th of [Q].

    Carrying the scale is what lets the fixed-base window below share this
    code.  There, four tables are built from [G], [2^64 G], [2^128 G] and
    [2^192 G], and all four have to be described in terms of the one
    generator, because it is [G] that the answer is a multiple of.  A
    variable-base window passes [n = 1] and the two readings coincide. *)
fn build_table (tx ty tz tt: A.array S64.t) (qx qy qz qt: A.array S64.t)
               (p: erased E.ext_point) (n: erased nat)
               (#vtx #vty #vtz #vtt: erased (Seq.seq S64.t))
               (#pq: perm) (#vqx #vqy #vqz #vqt: erased (Seq.seq S64.t))
requires
  A.pts_to tx vtx ** A.pts_to ty vty ** A.pts_to tz vtz ** A.pts_to tt vtt **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
  A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
  pure (Seq.length vtx == 80 /\ Seq.length vty == 80 /\
        Seq.length vtz == 80 /\ Seq.length vtt == 80 /\
        pok vqx vqy vqz vqt /\ oc (reveal p) /\
        rep vqx vqy vqz vqt n (reveal p))
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz ** A.pts_to tt wt **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
  A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
  pure (Seq.length wx == 80 /\ Seq.length wy == 80 /\
        Seq.length wz == 80 /\ Seq.length wt == 80 /\
        tok wx wy wz wt (reveal p) (reveal n) 16)
{
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz; A.pts_to_len tt;
  let z = S64.zero;
  let mut cx = [| z; 5sz |]; A.pts_to_len cx;
  let mut cy = [| z; 5sz |]; A.pts_to_len cy;
  let mut cz = [| z; 5sz |]; A.pts_to_len cz;
  let mut ct = [| z; 5sz |]; A.pts_to_len ct;
  let mut nx = [| z; 5sz |]; A.pts_to_len nx;
  let mut ny = [| z; 5sz |]; A.pts_to_len ny;
  let mut nz = [| z; 5sz |]; A.pts_to_len nz;
  let mut nt = [| z; 5sz |]; A.pts_to_len nt;
  A.pts_to_len cx; A.pts_to_len cy; A.pts_to_len cz; A.pts_to_len ct;
  A.pts_to_len nx; A.pts_to_len ny; A.pts_to_len nz; A.pts_to_len nt;

  set_infinity cx cy cz ct;
  with c0x c0y c0z c0t.
    assert (A.pts_to cx c0x ** A.pts_to cy c0y **
            A.pts_to cz c0z ** A.pts_to ct c0t);
  pok_intro c0x c0y c0z c0t;
  zero_ok c0x c0y c0z c0t (reveal p);
  mul_zero (reveal n);
  rep_cong c0x c0y c0z c0t 0 (0 * reveal n) (reveal p);

  let mut d = 0sz;
  while (let vd = !d; SZ.lt vd 16sz)
  invariant exists* (vd: SZ.t)
                    (wx wy wz wt wcx wcy wcz wct
                     wnx wny wnz wnt: Seq.seq S64.t).
    pts_to d vd **
    A.pts_to tx wx ** A.pts_to ty wy ** A.pts_to tz wz ** A.pts_to tt wt **
    A.pts_to cx wcx ** A.pts_to cy wcy ** A.pts_to cz wcz ** A.pts_to ct wct **
    A.pts_to nx wnx ** A.pts_to ny wny ** A.pts_to nz wnz ** A.pts_to nt wnt **
    A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
    A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
    pure (SZ.v vd <= 16 /\
          Seq.length wx == 80 /\ Seq.length wy == 80 /\
          Seq.length wz == 80 /\ Seq.length wt == 80 /\
          Seq.length wnx == nl /\ Seq.length wny == nl /\
          Seq.length wnz == nl /\ Seq.length wnt == nl /\
          pok wcx wcy wcz wct /\
          rep wcx wcy wcz wct (SZ.v vd * reveal n) (reveal p) /\
          tok wx wy wz wt (reveal p) (reveal n) (SZ.v vd))
  decreases (16 - SZ.v (!d))
  {
    let vd = !d;
    with wx wy wz wt.
      assert (A.pts_to tx wx ** A.pts_to ty wy **
              A.pts_to tz wz ** A.pts_to tt wt);
    with wcx wcy wcz wct.
      assert (A.pts_to cx wcx ** A.pts_to cy wcy **
              A.pts_to cz wcz ** A.pts_to ct wct);
    pok_elim wcx wcy wcz wct;
    pok_elim vqx vqy vqz vqt;
    store_off (SZ.v vd);
    store4 tx ty tz tt cx cy cz ct (SZ.mul vd 5sz);
    with wx' wy' wz' wt'.
      assert (A.pts_to tx wx' ** A.pts_to ty wy' **
              A.pts_to tz wz' ** A.pts_to tt wt');
    tbl_shape wx wx' wcx (SZ.v vd);
    tbl_shape wy wy' wcy (SZ.v vd);
    tbl_shape wz wz' wcz (SZ.v vd);
    tbl_shape wt wt' wct (SZ.v vd);
    ent_intro wx' wy' wz' wt' wcx wcy wcz wct
              (reveal p) (reveal n) (SZ.v vd);
    tok_extend wx wy wz wt wx' wy' wz' wt' (reveal p) (reveal n) (SZ.v vd);
    point_add nx ny nz nt cx cy cz ct qx qy qz qt;
    with wnx wny wnz wnt.
      assert (A.pts_to nx wnx ** A.pts_to ny wny **
              A.pts_to nz wnz ** A.pts_to nt wnt);
    add_ok wcx wcy wcz wct vqx vqy vqz vqt wnx wny wnz wnt
           (reveal p) (SZ.v vd * reveal n) (reveal n);
    mul_succ (SZ.v vd) (reveal n);
    rep_cong wnx wny wnz wnt (SZ.v vd * reveal n + reveal n)
             ((SZ.v vd + 1) * reveal n) (reveal p);
    pok_intro wnx wny wnz wnt;
    CF.copy cx nx; CF.copy cy ny; CF.copy cz nz; CF.copy ct nt;
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
    it can see, and [point_equal], [on_curve] and [pt_ok] all unfold into
    field equations over the prime; with four doublings in one body the
    context is large enough that [2 * (4 * e) == 8 * e] takes minutes.
    Behind a contract each doubling contributes three facts and nothing
    else. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** One doubling, in place: through the scratch quadruple and back. *)
inline_for_extraction
fn win_dbl (ox oy oz ot ux uy uz ut: A.array S64.t)
           (p: erased E.ext_point) (e: erased nat)
           (#vox #voy #voz #vot: erased (Seq.seq S64.t))
           (#vux #vuy #vuz #vut: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz ** A.pts_to ut vut **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\
        Seq.length vuz == nl /\ Seq.length vut == nl /\
        pok vox voy voz vot /\ oc (reveal p) /\
        rep vox voy voz vot e (reveal p))
ensures exists* (wx wy wz wt wux wuy wuz wut: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\
        Seq.length wuz == nl /\ Seq.length wut == nl /\
        pok wx wy wz wt /\ rep wx wy wz wt (2 * reveal e) (reveal p))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz; A.pts_to_len ut;
  pok_elim vox voy voz vot;
  point_double ux uy uz ut ox oy oz ot;
  with u1x u1y u1z u1t.
    assert (A.pts_to ux u1x ** A.pts_to uy u1y **
            A.pts_to uz u1z ** A.pts_to ut u1t);
  dbl_ok vox voy voz vot u1x u1y u1z u1t p (reveal e);
  pok_intro u1x u1y u1z u1t;
  (* [copy] gives sequence equality, not merely equality of the field
     elements, so the invariant transfers without a lemma. *)
  CF.copy ox ux; CF.copy oy uy; CF.copy oz uz; CF.copy ot ut;
  ()
}

(** Four of them, which is the doubling half of a rung. *)
fn win_dbl4 (ox oy oz ot ux uy uz ut: A.array S64.t)
            (p: erased E.ext_point) (e: erased nat)
            (#vox #voy #voz #vot: erased (Seq.seq S64.t))
            (#vux #vuy #vuz #vut: erased (Seq.seq S64.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to ux vux ** A.pts_to uy vuy ** A.pts_to uz vuz ** A.pts_to ut vut **
  pure (Seq.length vux == nl /\ Seq.length vuy == nl /\
        Seq.length vuz == nl /\ Seq.length vut == nl /\
        pok vox voy voz vot /\ oc (reveal p) /\
        rep vox voy voz vot e (reveal p))
ensures exists* (wx wy wz wt wux wuy wuz wut: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
  pure (Seq.length wux == nl /\ Seq.length wuy == nl /\
        Seq.length wuz == nl /\ Seq.length wut == nl /\
        pok wx wy wz wt /\ rep wx wy wz wt (16 * reveal e) (reveal p))
{
  win_dbl ox oy oz ot ux uy uz ut p e;
  with a1x a1y a1z a1t.
    assert (A.pts_to ox a1x ** A.pts_to oy a1y **
            A.pts_to oz a1z ** A.pts_to ot a1t);
  rep_cong a1x a1y a1z a1t (2 * reveal e) (2 * reveal e) p;
  win_dbl ox oy oz ot ux uy uz ut p (hide (2 * reveal e));
  with a2x a2y a2z a2t.
    assert (A.pts_to ox a2x ** A.pts_to oy a2y **
            A.pts_to oz a2z ** A.pts_to ot a2t);
  rep_cong a2x a2y a2z a2t (2 * (2 * reveal e)) (4 * reveal e) p;
  win_dbl ox oy oz ot ux uy uz ut p (hide (4 * reveal e));
  with a3x a3y a3z a3t.
    assert (A.pts_to ox a3x ** A.pts_to oy a3y **
            A.pts_to oz a3z ** A.pts_to ot a3t);
  rep_cong a3x a3y a3z a3t (2 * (4 * reveal e)) (8 * reveal e) p;
  win_dbl ox oy oz ot ux uy uz ut p (hide (8 * reveal e));
  with a4x a4y a4z a4t.
    assert (A.pts_to ox a4x ** A.pts_to oy a4y **
            A.pts_to oz a4z ** A.pts_to ot a4t);
  rep_cong a4x a4y a4z a4t (2 * (8 * reveal e)) (16 * reveal e) p;
  ()
}

#pop-options

(** The other half of a rung: fetch [tbl[d]] without letting [d] reach the
    address bus, and add it in.  The contract mentions no divisions and no
    powers of two -- the partial scalar [e] and the digit [d] are opaque
    naturals -- which keeps the index arithmetic of the ladder out of a
    context that carries the addition law. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

fn win_add (ox oy oz ot ux uy uz ut sx sy sz st: A.array S64.t)
           (tx ty tz tt: A.array S64.t) (dig: S64.t)
           (p: erased E.ext_point) (n: erased nat)
           (e: erased nat) (d: erased nat)
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
        pok vox voy voz vot /\ oc (reveal p) /\
        rep vox voy voz vot e (reveal p) /\
        tok vtx vty vtz vtt (reveal p) (reveal n) 16 /\
        reveal d < 16 /\ S64.v dig == reveal d)
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
        pok wx wy wz wt /\
        rep wx wy wz wt (reveal e + reveal d * reveal n) (reveal p))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz; A.pts_to_len ut;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz; A.pts_to_len st;
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz; A.pts_to_len tt;
  pok_elim vox voy voz vot;
  entry_fits (reveal d);
  table_select sx tx 5sz dig d;
  table_select sy ty 5sz dig d;
  table_select sz tz 5sz dig d;
  table_select st tt 5sz dig d;
  entry_def vtx (reveal d); entry_def vty (reveal d);
  entry_def vtz (reveal d); entry_def vtt (reveal d);
  tok_get vtx vty vtz vtt (reveal p) (reveal n) (reveal d);
  with wsx wsy wsz wst.
    assert (A.pts_to sx wsx ** A.pts_to sy wsy **
            A.pts_to sz wsz ** A.pts_to st wst);
  pok_elim wsx wsy wsz wst;
  point_add ux uy uz ut ox oy oz ot sx sy sz st;
  with u1x u1y u1z u1t.
    assert (A.pts_to ux u1x ** A.pts_to uy u1y **
            A.pts_to uz u1z ** A.pts_to ut u1t);
  add_ok vox voy voz vot wsx wsy wsz wst u1x u1y u1z u1t
         (reveal p) (reveal e) (reveal d * reveal n);
  pok_intro u1x u1y u1z u1t;
  CF.copy ox ux; CF.copy oy uy; CF.copy oz uz; CF.copy ot ut;
  ()
}

#pop-options

(** {2 The ladder}

    Sixty-four rungs of four bits each.  The accumulator starts at the
    point at infinity, which is the multiple by the empty prefix of the
    scalar, and after the rung at [j] it is the multiple by [k / 2^j]. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 300"

(** [point_mul_win o q ks] is [o := [ks] Q], up to [point_equal]. *)
fn point_mul_win (ox oy oz ot: A.array S64.t) (qx qy qz qt: A.array S64.t)
                 (ks: A.array S8.t)
                 (#vox #voy #voz #vot: erased (Seq.seq S64.t))
                 (#pq: perm) (#vqx #vqy #vqz #vqt: erased (Seq.seq S64.t))
                 (#pk: perm) (#vk: erased (Seq.seq S8.t))
requires
  A.pts_to ox vox ** A.pts_to oy voy ** A.pts_to oz voz ** A.pts_to ot vot **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
  A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
  A.pts_to ks #pk vk **
  pure (Seq.length vox == nl /\ Seq.length voy == nl /\
        Seq.length voz == nl /\ Seq.length vot == nl /\
        Seq.length vk == 32 /\
        pt_ok vqx vqy vqz vqt /\ GR.on_curve (pt vqx vqy vqz vqt))
ensures exists* (wx wy wz wt: Seq.seq S64.t).
  A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
  A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
  A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
  A.pts_to ks #pk vk **
  pure (Seq.length vk == 32 /\ pt_ok wx wy wz wt /\
        GR.on_curve (pt wx wy wz wt) /\
        GR.on_curve (E.point_mul vk (pt vqx vqy vqz vqt)) /\
        E.point_equal (pt wx wy wz wt)
                      (E.point_mul vk (pt vqx vqy vqz vqt)))
{
  A.pts_to_len ox; A.pts_to_len oy; A.pts_to_len oz; A.pts_to_len ot;
  A.pts_to_len ks;
  oc_intro (pt vqx vqy vqz vqt);
  let z = S64.zero;
  let mut tx = [| z; 80sz |]; A.pts_to_len tx;
  let mut ty = [| z; 80sz |]; A.pts_to_len ty;
  let mut tz = [| z; 80sz |]; A.pts_to_len tz;
  let mut tt = [| z; 80sz |]; A.pts_to_len tt;
  let mut ux = [| z; 5sz |]; A.pts_to_len ux;
  let mut uy = [| z; 5sz |]; A.pts_to_len uy;
  let mut uz = [| z; 5sz |]; A.pts_to_len uz;
  let mut ut = [| z; 5sz |]; A.pts_to_len ut;
  let mut sx = [| z; 5sz |]; A.pts_to_len sx;
  let mut sy = [| z; 5sz |]; A.pts_to_len sy;
  let mut sz = [| z; 5sz |]; A.pts_to_len sz;
  let mut st = [| z; 5sz |]; A.pts_to_len st;
  A.pts_to_len tx; A.pts_to_len ty; A.pts_to_len tz; A.pts_to_len tt;
  A.pts_to_len ux; A.pts_to_len uy; A.pts_to_len uz; A.pts_to_len ut;
  A.pts_to_len sx; A.pts_to_len sy; A.pts_to_len sz; A.pts_to_len st;

  pok_intro vqx vqy vqz vqt;
  rep_one vqx vqy vqz vqt;
  build_table tx ty tz tt qx qy qz qt (hide (pt vqx vqy vqz vqt)) (hide 1);
  set_infinity ox oy oz ot;
  with o0x o0y o0z o0t.
    assert (A.pts_to ox o0x ** A.pts_to oy o0y **
            A.pts_to oz o0z ** A.pts_to ot o0t);
  pok_intro o0x o0y o0z o0t;
  zero_ok o0x o0y o0z o0t (pt vqx vqy vqz vqt);
  top_div vk;
  pow2_pos 256;
  div_nonneg (B.le_nat vk) 256;

  let mut j = 256sz;
  while (let vj = !j; SZ.gt vj 0sz)
  invariant exists* (vj: SZ.t)
                    (wx wy wz wt wux wuy wuz wut wsx wsy wsz wst
                     wtx wty wtz wtt: Seq.seq S64.t).
    pts_to j vj **
    A.pts_to ox wx ** A.pts_to oy wy ** A.pts_to oz wz ** A.pts_to ot wt **
    A.pts_to ux wux ** A.pts_to uy wuy ** A.pts_to uz wuz ** A.pts_to ut wut **
    A.pts_to sx wsx ** A.pts_to sy wsy ** A.pts_to sz wsz ** A.pts_to st wst **
    A.pts_to tx wtx ** A.pts_to ty wty ** A.pts_to tz wtz ** A.pts_to tt wtt **
    A.pts_to qx #pq vqx ** A.pts_to qy #pq vqy **
    A.pts_to qz #pq vqz ** A.pts_to qt #pq vqt **
    A.pts_to ks #pk vk **
    pure (SZ.v vj <= 256 /\ SZ.v vj % 4 == 0 /\
          pow2 (SZ.v vj) > 0 /\ B.le_nat vk / pow2 (SZ.v vj) >= 0 /\
          Seq.length vk == 32 /\
          Seq.length wux == nl /\ Seq.length wuy == nl /\
          Seq.length wuz == nl /\ Seq.length wut == nl /\
          Seq.length wsx == nl /\ Seq.length wsy == nl /\
          Seq.length wsz == nl /\ Seq.length wst == nl /\
          Seq.length wtx == 80 /\ Seq.length wty == 80 /\
          Seq.length wtz == 80 /\ Seq.length wtt == 80 /\
          tok wtx wty wtz wtt (pt vqx vqy vqz vqt) 1 16 /\
          pok wx wy wz wt /\
          rep wx wy wz wt (B.le_nat vk / pow2 (SZ.v vj))
              (pt vqx vqy vqz vqt))
  decreases (SZ.v (!j))
  {
    let vj = !j;
    step4 (SZ.v vj);
    let j2 = SZ.sub vj 4sz;
    pow2_pos (SZ.v j2);
    div_nonneg (B.le_nat vk) (SZ.v j2);
    let dig = nibble ks j2;
    win_dbl4 ox oy oz ot ux uy uz ut (hide (pt vqx vqy vqz vqt))
             (hide (B.le_nat vk / pow2 (SZ.v vj)));
    win_add ox oy oz ot ux uy uz ut sx sy sz st tx ty tz tt dig
            (hide (pt vqx vqy vqz vqt)) (hide 1)
            (hide (16 * (B.le_nat vk / pow2 (SZ.v vj))))
            (hide (B.le_nat vk / pow2 (SZ.v j2) % 16));
    pow2_cong (SZ.v j2 + 4) (SZ.v vj);
    digit_split (B.le_nat vk) (SZ.v j2);
    mul_one (B.le_nat vk / pow2 (SZ.v j2) % 16);
    with wx wy wz wt.
      assert (A.pts_to ox wx ** A.pts_to oy wy **
              A.pts_to oz wz ** A.pts_to ot wt);
    rep_cong wx wy wz wt
             (16 * (B.le_nat vk / pow2 (SZ.v vj)) +
              B.le_nat vk / pow2 (SZ.v j2) % 16)
             (B.le_nat vk / pow2 (SZ.v j2)) (pt vqx vqy vqz vqt);
    j := j2;
  };
  let vj = !j;
  sz_zero vj;
  bot_div (B.le_nat vk);
  with wx wy wz wt.
    assert (A.pts_to ox wx ** A.pts_to oy wy **
            A.pts_to oz wz ** A.pts_to ot wt);
  pok_elim wx wy wz wt;
  win_done wx wy wz wt (pt vqx vqy vqz vqt) vk;
  ()
}

#pop-options
