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

    The windowed ladder itself is gone: verification now uses the
    double-scalar multiplication in {!Hacl.Ed25519.Straus}, and signing
    the comb in {!Hacl.Ed25519.PointMulComb}.  What remains are the
    representation predicates, tables and lemmas both of those share.

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
module Mem = Hacl.Mem

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

let mul_nat (a b: nat) : Lemma (a * b >= 0) = Math.nat_times_nat_is_nat a b

(** The same for every multiple of a fixed [n], for the loop invariant of
    {!build_table}, whose [d n] is a [nat] for a [d] not yet in scope. *)
let mul_nat_all (n: nat)
  : Lemma (forall (a: nat). {:pattern (a * n)} a * n >= 0)
  = introduce forall (a: nat). a * n >= 0 with mul_nat a n

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
