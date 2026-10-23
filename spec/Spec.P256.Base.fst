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

(** The three extra base points a fixed-base window needs, for P-256.

    A windowed multiplication by the generator splits the scalar into four
    sixty-four-bit pieces and multiplies each by its own base point, so
    that one doubling chain serves all four.  The base points are
    [G], [2^64 G], [2^128 G] and [2^192 G], and the last three have to be
    constants in the binary: computing them would cost exactly what the
    window is trying to save.

    Saying what a constant *is* is the whole problem.  [smul (2^64) g] is
    two-to-the-sixty-four additions and cannot be unfolded, so the
    statement is made in terms of a doubling *chain*
    ({!Spec.Group.Smul.dblk}), which the normaliser evaluates on concrete
    field elements at typechecking time, and
    {!Spec.Group.Smul.dblk_ok} turns into a statement about [smul].

    The constants stored are the *affine* representatives [(x, y, 1)].
    Nothing requires them to be the triple the chain produces: [peq] is
    projective equality, the normaliser decides it on concrete numbers
    just as readily, and an affine representative makes [z] a literal one,
    which keeps each table's chain of additions decidable by the
    normaliser.

    The six coordinates are [opaque_to_smt], and the numbers here are the
    coordinates themselves, not their Montgomery forms: this module is
    about the curve, and the implementation's representation belongs in
    {!Hacl.P256.Win0} .. {!Hacl.P256.Win3}, which is where the
    multiplication by [R] happens.  {!Spec.P256.Win1} .. {!Spec.P256.Win3}
    start their chains from these three points.

    This is {!Spec.K256.Base} with a different curve; the scalar
    arithmetic the two share lives in {!Spec.Group.Split4}. *)
module Spec.P256.Base

module G = Spec.Group.Smul
module Math = FStar.Math.Lemmas
module SM = Spec.P256.Smul

open Spec.P256
open Spec.P256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {3 [2^64] G} *)
[@@"opaque_to_smt"]
let q1x : felem =
  assert_norm (7081762767697287976009771493310263771290289599581147299482766892475312560995 < prime);
  7081762767697287976009771493310263771290289599581147299482766892475312560995
[@@"opaque_to_smt"]
let q1y : felem =
  assert_norm (86823381773038968119624426030239743822549553315161612703449942820586000887527 < prime);
  86823381773038968119624426030239743822549553315161612703449942820586000887527

let q1 : proj_point = (q1x, q1y, fone)

(** {3 [2^128] G} *)
[@@"opaque_to_smt"]
let q2x : felem =
  assert_norm (30978927491535595270285342502287618780579786685182435011955893029189825707397 < prime);
  30978927491535595270285342502287618780579786685182435011955893029189825707397
[@@"opaque_to_smt"]
let q2y : felem =
  assert_norm (20481551163499472379222416201371726725754635744576161296521936142531318405938 < prime);
  20481551163499472379222416201371726725754635744576161296521936142531318405938

let q2 : proj_point = (q2x, q2y, fone)

(** {3 [2^192] G} *)
[@@"opaque_to_smt"]
let q3x : felem =
  assert_norm (75457776083317821252662798697757590755920885718289763058263534551782236039358 < prime);
  75457776083317821252662798697757590755920885718289763058263534551782236039358
[@@"opaque_to_smt"]
let q3y : felem =
  assert_norm (46728718496393669138731607516029863508010621830530871863089645384465424840180 < prime);
  46728718496393669138731607516029863508010621830530871863089645384465424840180

let q3 : proj_point = (q3x, q3y, fone)

(** {2 What they are}

    Each is one [assert_norm] for the chain, one for the curve equation,
    and one application of {!Spec.Group.Smul.dblk_ok} to move from the
    chain to [smul].  The chains are linked: [q2] is sixty-four doublings
    of [q1], not a hundred and twenty-eight of [g], so the normaliser does
    sixty-four doublings three times rather than one, two and three times. *)

let g_ok (_: unit) : Lemma (on_curve g /\ peq g (G.smul SM.pg 1 g))
  = g_on_curve ();
    G.smul_one SM.pg g;
    G.smul_ok SM.pg 1 g;
    peq_sym (G.smul SM.pg 1 g) g

let q1_ok (_: unit)
  : Lemma (on_curve q1 /\ peq q1 (G.smul SM.pg (pow2 64) g))
  = assert_norm (on_curve q1);
    assert_norm (peq q1 (G.dblk SM.pg 64 g));
    g_ok ();
    g_on_curve ();
    G.dblk_ok SM.pg 64 1 g g;
    G.smul_ok SM.pg (pow2 64) g;
    peq_trans q1 (G.dblk SM.pg 64 g) (G.smul SM.pg (pow2 64) g)

let q2_ok (_: unit)
  : Lemma (on_curve q2 /\ peq q2 (G.smul SM.pg (pow2 128) g))
  = assert_norm (on_curve q2);
    assert_norm (peq q2 (G.dblk SM.pg 64 q1));
    q1_ok ();
    g_on_curve ();
    G.dblk_ok SM.pg 64 (pow2 64) g q1;
    Math.pow2_plus 64 64;
    G.smul_ok SM.pg (pow2 128) g;
    peq_trans q2 (G.dblk SM.pg 64 q1) (G.smul SM.pg (pow2 128) g)

let q3_ok (_: unit)
  : Lemma (on_curve q3 /\ peq q3 (G.smul SM.pg (pow2 192) g))
  = assert_norm (on_curve q3);
    assert_norm (peq q3 (G.dblk SM.pg 64 q2));
    q2_ok ();
    g_on_curve ();
    G.dblk_ok SM.pg 64 (pow2 128) g q2;
    Math.pow2_plus 64 128;
    G.smul_ok SM.pg (pow2 192) g;
    peq_trans q3 (G.dblk SM.pg 64 q2) (G.smul SM.pg (pow2 192) g)

#pop-options
