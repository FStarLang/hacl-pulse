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

(** The three extra base points a fixed-base window needs.

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
    field elements at typechecking time -- sixty-four doublings, about a
    second each chain -- and {!Spec.Group.Smul.dblk_ok} turns into a
    statement about [smul].

    The constants stored are the *affine* representatives [(x, y, 1, xy)]
    rather than whatever quadruple the chain happens to produce.  Nothing
    requires them to be the same quadruple: [point_equal] is projective
    equality, the normaliser decides it on concrete numbers just as
    readily, and an affine representative makes [z] a literal one, which
    the table build below is faster for.

    The nine coordinates are [opaque_to_smt].  Everything said about them
    is settled by the normaliser, so the solver has no use for their
    values, and nine two-hundred-and-fifty-bit literals sharing one
    context is enough to make the routine limb-extraction lemmas in
    {!Hacl.Ed25519.Tables} time out. *)
module Spec.Ed25519.Base

module G = Spec.Group.Smul
module Math = FStar.Math.Lemmas
module SM = Spec.Ed25519.Smul

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {3 [2^64] G} *)
[@@"opaque_to_smt"]
let b1x : elem =
  assert_norm (44388040078108422381599858079345000847427885062711346041771517276226329616898 < prime);
  44388040078108422381599858079345000847427885062711346041771517276226329616898
[@@"opaque_to_smt"]
let b1y : elem =
  assert_norm (1423604317745427322790381226394774763053130405907994130724317794966956167955 < prime);
  1423604317745427322790381226394774763053130405907994130724317794966956167955
[@@"opaque_to_smt"]
let b1t : elem =
  assert_norm (44572319132873595455842987266297020623526171197071652062676750099116673206361 < prime);
  44572319132873595455842987266297020623526171197071652062676750099116673206361

let b1 : ext_point = (b1x, b1y, one, b1t)

(** {3 [2^128] G} *)
[@@"opaque_to_smt"]
let b2x : elem =
  assert_norm (34445898214599204196824587830670445739267303633182408050117152659121903233060 < prime);
  34445898214599204196824587830670445739267303633182408050117152659121903233060
[@@"opaque_to_smt"]
let b2y : elem =
  assert_norm (43048524062920118298805915568484795959327268000798232147099016825120495085163 < prime);
  43048524062920118298805915568484795959327268000798232147099016825120495085163
[@@"opaque_to_smt"]
let b2t : elem =
  assert_norm (2546723617105803217066704043024384113612712956060210350476893017486688072586 < prime);
  2546723617105803217066704043024384113612712956060210350476893017486688072586

let b2 : ext_point = (b2x, b2y, one, b2t)

(** {3 [2^192] G} *)
[@@"opaque_to_smt"]
let b3x : elem =
  assert_norm (12565258097955692523285632157940150666933275725759344066053586092157591802509 < prime);
  12565258097955692523285632157940150666933275725759344066053586092157591802509
[@@"opaque_to_smt"]
let b3y : elem =
  assert_norm (44257820073692905562487031197842487206011716534849741297988353661581996935219 < prime);
  44257820073692905562487031197842487206011716534849741297988353661581996935219
[@@"opaque_to_smt"]
let b3t : elem =
  assert_norm (11852089489538718050497412370591090809284399797098271593925664457585805673159 < prime);
  11852089489538718050497412370591090809284399797098271593925664457585805673159

let b3 : ext_point = (b3x, b3y, one, b3t)

(** {2 What they are}

    Each is one [assert_norm] for the chain, one for the curve equation,
    and one application of {!Spec.Group.Smul.dblk_ok} to move from the
    chain to [smul].  The chains are linked: [b2] is sixty-four doublings
    of [b1], not a hundred and twenty-eight of [g], so the normaliser does
    sixty-four doublings three times rather than one, two and three times. *)

let g_ok (_: unit) : Lemma (on_curve g /\ point_equal g (G.smul SM.eg 1 g))
  = g_on_curve ();
    G.smul_one SM.eg g;
    G.smul_ok SM.eg 1 g;
    point_equal_sym (G.smul SM.eg 1 g) g

let b1_ok (_: unit)
  : Lemma (on_curve b1 /\ point_equal b1 (G.smul SM.eg (pow2 64) g))
  = assert_norm (on_curve b1);
    assert_norm (point_equal b1 (G.dblk SM.eg 64 g));
    g_ok ();
    G.dblk_ok SM.eg 64 1 g g;
    G.smul_ok SM.eg (pow2 64) g;
    point_equal_trans b1 (G.dblk SM.eg 64 g) (G.smul SM.eg (pow2 64) g)

let b2_ok (_: unit)
  : Lemma (on_curve b2 /\ point_equal b2 (G.smul SM.eg (pow2 128) g))
  = assert_norm (on_curve b2);
    assert_norm (point_equal b2 (G.dblk SM.eg 64 b1));
    b1_ok ();
    g_on_curve ();
    G.dblk_ok SM.eg 64 (pow2 64) g b1;
    Math.pow2_plus 64 64;
    G.smul_ok SM.eg (pow2 128) g;
    point_equal_trans b2 (G.dblk SM.eg 64 b1) (G.smul SM.eg (pow2 128) g)

let b3_ok (_: unit)
  : Lemma (on_curve b3 /\ point_equal b3 (G.smul SM.eg (pow2 192) g))
  = assert_norm (on_curve b3);
    assert_norm (point_equal b3 (G.dblk SM.eg 64 b2));
    b2_ok ();
    g_on_curve ();
    G.dblk_ok SM.eg 64 (pow2 128) g b2;
    Math.pow2_plus 64 128;
    G.smul_ok SM.eg (pow2 192) g;
    point_equal_trans b3 (G.dblk SM.eg 64 b2) (G.smul SM.eg (pow2 192) g)

#pop-options
