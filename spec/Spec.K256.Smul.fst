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

(** secp256k1 as a commutative group, and the bridge to the ladder.

    Two things.  First, {!kg}: the group axioms proved in
    {!Spec.K256.Group} assembled into the record {!Spec.Group.Smul.grp},
    which is what makes [smul] and its additivity available on this curve.
    The record is the whole of the interface -- the curve is mentioned
    nowhere in the proofs of the facts a window needs, so those proofs cost
    nothing here.

    Second, {!point_mul_is_smul}: [Spec.K256.point_mul], which is
    double-and-add over 256 bits and is what the caller-visible
    specifications are written in terms of, computes the multiple.  This is
    the statement a windowed implementation needs in order to be allowed to
    do the operations in a different order.  It is up to [peq], and
    {!Spec.K256.Group.peq_to_aff_point} carries that to the affine point
    the encoder and the verification equation see. *)
module Spec.K256.Smul

module G = Spec.Group.Smul
module Loops = Hacl.Spec.Loops
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical

open Spec.K256
open Spec.K256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The instance.  Every field is a lemma from {!Spec.K256.Group}; this
    record is the only place in the library where they are all named at
    once. *)
let kg : G.grp proj_point = {
  ok = on_curve;
  eqv = peq;
  zero = point_at_infinity;
  add = point_add;
  dbl = point_double;

  ok_zero = point_at_infinity_on_curve;
  ok_add = point_add_on_curve;
  ok_dbl = point_double_on_curve;

  eqv_refl = peq_refl;
  eqv_sym = peq_sym;
  eqv_trans = peq_trans;

  add_congr = point_add_congr;
  add_assoc = point_add_assoc_law;
  add_comm = point_add_comm_law;
  add_id = point_add_identity;
  dbl_is_add = point_double_is_add;
}

(** The multiple, specialized.  Stated as a definition of its own so that
    the implementation's loop invariant does not have to mention the
    record. *)
let smul (n: nat) (p: proj_point) : proj_point = G.smul kg n p

let smul_ok (n: nat) (p: proj_point)
  : Lemma (requires on_curve p) (ensures on_curve (smul n p))
  = G.smul_ok kg n p

let smul_zero (p: proj_point) : Lemma (smul 0 p == point_at_infinity)
  = assert_norm (G.smul kg 0 p == point_at_infinity)

let smul_one (p: proj_point)
  : Lemma (requires on_curve p) (ensures peq (smul 1 p) p)
  = G.smul_one kg p

let smul_congr (n: nat) (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ peq p q)
          (ensures peq (smul n p) (smul n q))
  = G.smul_congr kg n p q

(** The two shapes a rung of a window produces. *)
let smul_dbl_congr (n: nat) (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ peq q (smul n p))
          (ensures on_curve (point_double q) /\
                   peq (point_double q) (smul (2 * n) p))
  = G.smul_dbl_congr kg n p q

let smul_add_congr (m n: nat) (p q r: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ on_curve r /\
                    peq q (smul m p) /\ peq r (smul n p))
          (ensures on_curve (point_add q r) /\
                   peq (point_add q r) (smul (m + n) p))
  = G.smul_add_congr kg m n p q r

let smul_succ_congr (n: nat) (p q: proj_point)
  : Lemma (requires on_curve p /\ on_curve q /\ peq q (smul n p))
          (ensures on_curve (point_add q p) /\
                   peq (point_add q p) (smul (n + 1) p))
  = G.smul_succ_congr kg n p q

#pop-options

(** {2 The ladder computes it}

    [point_mul] is [repeati_g] over 256 steps of [point_mul_step], which is
    {!Spec.Group.Smul.ladder_step} at this instance -- the two unfold to
    the same term, and saying so mentions no equivalence, so it is cheap
    here.  Everything that is not cheap was done abstractly. *)

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"

let step_is_ladder (k: nat) (p: proj_point) (i: nat) (acc: proj_point)
  : Lemma (point_mul_at k p i acc == G.ladder_at kg 256 k p i acc)
  = ()

let point_mul_is_ladder (k: nat) (p: proj_point)
  : Lemma (point_mul k p ==
           Loops.repeati_g 256 (G.ladder_at kg 256 k p) point_at_infinity)
  = Classical.forall_intro_2 (step_is_ladder k p);
    Loops.repeati_g_ext 256 (point_mul_at k p) (G.ladder_at kg 256 k p)
                        point_at_infinity

let point_mul_is_smul (k: nat) (p: proj_point)
  : Lemma (requires on_curve p /\ k < pow2 256)
          (ensures on_curve (point_mul k p) /\ peq (point_mul k p) (smul k p))
  = point_mul_is_ladder k p;
    G.ladder_is_smul kg 256 k p

#pop-options
