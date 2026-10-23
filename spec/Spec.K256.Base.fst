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

(** The three extra base points a fixed-base window needs, for secp256k1.

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
    which the table build is faster for.

    The six coordinates are [opaque_to_smt].  Everything said about them
    is settled by the normaliser, so the solver has no use for their
    values, and a handful of two-hundred-and-fifty-six-bit literals
    sharing one context is enough to make the routine limb-extraction
    lemmas in {!Hacl.K256.Tables52} time out.

    The scalar arithmetic it shares with {!Spec.P256.Base} lives in
    {!Spec.Group.Split4}. *)
module Spec.K256.Base

module G = Spec.Group.Smul
module Math = FStar.Math.Lemmas
module SM = Spec.K256.Smul

open Spec.K256
open Spec.K256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {3 [2^64] G} *)
[@@"opaque_to_smt"]
let q1x : felem =
  assert_norm (23129491278950567785970148376500648032717531886785241126168611397589814798013 < prime);
  23129491278950567785970148376500648032717531886785241126168611397589814798013
[@@"opaque_to_smt"]
let q1y : felem =
  assert_norm (39307099057880941662675806615359097347682728603444928455093651353540932186784 < prime);
  39307099057880941662675806615359097347682728603444928455093651353540932186784

let q1 : proj_point = (q1x, q1y, fone)

(** {3 [2^128] G} *)
[@@"opaque_to_smt"]
let q2x : felem =
  assert_norm (64865771952738249789114440545196421582918768733599534045195125031385885360346 < prime);
  64865771952738249789114440545196421582918768733599534045195125031385885360346
[@@"opaque_to_smt"]
let q2y : felem =
  assert_norm (46211216742671250426576585530459394900178019437443360579906162037052661563266 < prime);
  46211216742671250426576585530459394900178019437443360579906162037052661563266

let q2 : proj_point = (q2x, q2y, fone)

(** {3 [2^192] G} *)
[@@"opaque_to_smt"]
let q3x : felem =
  assert_norm (106135013536326263233204638779771538367307463662639765758785315935371743257267 < prime);
  106135013536326263233204638779771538367307463662639765758785315935371743257267
[@@"opaque_to_smt"]
let q3y : felem =
  assert_norm (86028625094535483850261571256264386723357163272666519397289099603747119225149 < prime);
  86028625094535483850261571256264386723357163272666519397289099603747119225149

let q3 : proj_point = (q3x, q3y, fone)

(** {2 What they are}

    Each is one [assert_norm] for the chain, one for the curve equation,
    and one application of {!Spec.Group.Smul.dblk_ok} to move from the
    chain to [smul].  The chains are linked: [q2] is sixty-four doublings
    of [q1], not a hundred and twenty-eight of [g], so the normaliser does
    sixty-four doublings three times rather than one, two and three times. *)

let g_ok (_: unit) : Lemma (on_curve g /\ peq g (G.smul SM.kg 1 g))
  = g_on_curve ();
    G.smul_one SM.kg g;
    G.smul_ok SM.kg 1 g;
    peq_sym (G.smul SM.kg 1 g) g

let q1_ok (_: unit)
  : Lemma (on_curve q1 /\ peq q1 (G.smul SM.kg (pow2 64) g))
  = assert_norm (on_curve q1);
    assert_norm (peq q1 (G.dblk SM.kg 64 g));
    g_ok ();
    g_on_curve ();
    G.dblk_ok SM.kg 64 1 g g;
    
    G.smul_ok SM.kg (pow2 64) g;
    peq_trans q1 (G.dblk SM.kg 64 g) (G.smul SM.kg (pow2 64) g)

let q2_ok (_: unit)
  : Lemma (on_curve q2 /\ peq q2 (G.smul SM.kg (pow2 128) g))
  = assert_norm (on_curve q2);
    assert_norm (peq q2 (G.dblk SM.kg 64 q1));
    q1_ok ();
    g_on_curve ();
    G.dblk_ok SM.kg 64 (pow2 64) g q1;
    Math.pow2_plus 64 64;
    G.smul_ok SM.kg (pow2 128) g;
    peq_trans q2 (G.dblk SM.kg 64 q1) (G.smul SM.kg (pow2 128) g)

let q3_ok (_: unit)
  : Lemma (on_curve q3 /\ peq q3 (G.smul SM.kg (pow2 192) g))
  = assert_norm (on_curve q3);
    assert_norm (peq q3 (G.dblk SM.kg 64 q2));
    q2_ok ();
    g_on_curve ();
    G.dblk_ok SM.kg 64 (pow2 128) g q2;
    Math.pow2_plus 64 128;
    G.smul_ok SM.kg (pow2 192) g;
    peq_trans q3 (G.dblk SM.kg 64 q2) (G.smul SM.kg (pow2 192) g)

#pop-options
