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

(** The sixteen multiples of [G], which is the first of the fixed-base
    window's four tables.

    {!Spec.K256.Base} says what the four base points are; this says what
    the table built from one of them holds, so that the table can be a
    constant in the binary rather than fifteen additions on every
    signature.

    The entries are the *affine* representatives, so [z] is one
    throughout.  Each is settled by two [assert_norm]s -- that it is on
    the curve, and that it is the previous entry plus the base point --
    and one application of {!Spec.K256.Smul.smul_add_congr}, which turns a
    chain of additions into a statement about [smul].  The chain is the
    reason the entries are stored affine: an [assert_norm] over a
    projective triple carries whatever denominators the previous addition
    happened to leave, and by the fifteenth entry the numbers have stopped
    being ones the normaliser can compare.

    The coordinates are [opaque_to_smt] for the reason {!Spec.K256.Base}'s
    are: everything said about them is settled by the normaliser, and
    twenty-eight two-hundred-and-fifty-six-bit literals in one solver
    context is not a context anything else terminates in. *)
module Spec.K256.Win0

module G = Spec.Group.Smul
module SM = Spec.K256.Smul
module Base = Spec.K256.Base
module Math = FStar.Math.Lemmas

open Spec.K256
open Spec.K256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d]-th multiple of [g]. *)
let n : nat = 1

(** [(k + 1) n] as [k n + n], which is the step the chain takes. *)
let step (k: nat) : Lemma (k * n + n == (k + 1) * n)
  = Math.distributivity_add_left k 1 n

(** {2 The first two entries}

    Nothing and the base point itself, both of which are already known. *)

let e0 : proj_point = point_at_infinity

let e0_ok (_: unit)
  : Lemma (on_curve e0 /\ peq e0 (SM.smul (0 * n) g))
  = point_at_infinity_on_curve ();
    SM.smul_zero g;
    peq_refl e0

let e1 : proj_point = g

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul (1 * n) g))
  = Base.g_ok ()

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : felem =
  assert_norm (89565891926547004231252920425935692360644145829622209833684329913297188986597 < prime);
  89565891926547004231252920425935692360644145829622209833684329913297188986597

[@@"opaque_to_smt"]
let e2y : felem =
  assert_norm (12158399299693830322967808612713398636155367887041628176798871954788371653930 < prime);
  12158399299693830322967808612713398636155367887041628176798871954788371653930

let e2 : proj_point = (e2x, e2y, fone)

let e2_ok (_: unit)
  : Lemma (on_curve e2 /\ peq e2 (SM.smul (2 * n) g))
  = assert_norm (on_curve e2);
    assert_norm (peq e2 (point_add e1 e1));
    e1_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (1 * n) n g e1 e1;
    step 1;
    SM.smul_ok (2 * n) g;
    peq_trans e2 (point_add e1 e1) (SM.smul (2 * n) g)

[@@"opaque_to_smt"]
let e3x : felem =
  assert_norm (112711660439710606056748659173929673102114977341539408544630613555209775888121 < prime);
  112711660439710606056748659173929673102114977341539408544630613555209775888121

[@@"opaque_to_smt"]
let e3y : felem =
  assert_norm (25583027980570883691656905877401976406448868254816295069919888960541586679410 < prime);
  25583027980570883691656905877401976406448868254816295069919888960541586679410

let e3 : proj_point = (e3x, e3y, fone)

let e3_ok (_: unit)
  : Lemma (on_curve e3 /\ peq e3 (SM.smul (3 * n) g))
  = assert_norm (on_curve e3);
    assert_norm (peq e3 (point_add e2 e1));
    e2_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (2 * n) n g e2 e1;
    step 2;
    SM.smul_ok (3 * n) g;
    peq_trans e3 (point_add e2 e1) (SM.smul (3 * n) g)

[@@"opaque_to_smt"]
let e4x : felem =
  assert_norm (103388573995635080359749164254216598308788835304023601477803095234286494993683 < prime);
  103388573995635080359749164254216598308788835304023601477803095234286494993683

[@@"opaque_to_smt"]
let e4y : felem =
  assert_norm (37057141145242123013015316630864329550140216928701153669873286428255828810018 < prime);
  37057141145242123013015316630864329550140216928701153669873286428255828810018

let e4 : proj_point = (e4x, e4y, fone)

let e4_ok (_: unit)
  : Lemma (on_curve e4 /\ peq e4 (SM.smul (4 * n) g))
  = assert_norm (on_curve e4);
    assert_norm (peq e4 (point_add e3 e1));
    e3_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (3 * n) n g e3 e1;
    step 3;
    SM.smul_ok (4 * n) g;
    peq_trans e4 (point_add e3 e1) (SM.smul (4 * n) g)

[@@"opaque_to_smt"]
let e5x : felem =
  assert_norm (21505829891763648114329055987619236494102133314575206970830385799158076338148 < prime);
  21505829891763648114329055987619236494102133314575206970830385799158076338148

[@@"opaque_to_smt"]
let e5y : felem =
  assert_norm (98003708678762621233683240503080860129026887322874138805529884920309963580118 < prime);
  98003708678762621233683240503080860129026887322874138805529884920309963580118

let e5 : proj_point = (e5x, e5y, fone)

let e5_ok (_: unit)
  : Lemma (on_curve e5 /\ peq e5 (SM.smul (5 * n) g))
  = assert_norm (on_curve e5);
    assert_norm (peq e5 (point_add e4 e1));
    e4_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (4 * n) n g e4 e1;
    step 4;
    SM.smul_ok (5 * n) g;
    peq_trans e5 (point_add e4 e1) (SM.smul (5 * n) g)

[@@"opaque_to_smt"]
let e6x : felem =
  assert_norm (115780575977492633039504758427830329241728645270042306223540962614150928364886 < prime);
  115780575977492633039504758427830329241728645270042306223540962614150928364886

[@@"opaque_to_smt"]
let e6y : felem =
  assert_norm (78735063515800386211891312544505775871260717697865196436804966483607426560663 < prime);
  78735063515800386211891312544505775871260717697865196436804966483607426560663

let e6 : proj_point = (e6x, e6y, fone)

let e6_ok (_: unit)
  : Lemma (on_curve e6 /\ peq e6 (SM.smul (6 * n) g))
  = assert_norm (on_curve e6);
    assert_norm (peq e6 (point_add e5 e1));
    e5_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (5 * n) n g e5 e1;
    step 5;
    SM.smul_ok (6 * n) g;
    peq_trans e6 (point_add e5 e1) (SM.smul (6 * n) g)

[@@"opaque_to_smt"]
let e7x : felem =
  assert_norm (41948375291644419605210209193538855353224492619856392092318293986323063962044 < prime);
  41948375291644419605210209193538855353224492619856392092318293986323063962044

[@@"opaque_to_smt"]
let e7y : felem =
  assert_norm (48361766907851246668144012348516735800090617714386977531302791340517493990618 < prime);
  48361766907851246668144012348516735800090617714386977531302791340517493990618

let e7 : proj_point = (e7x, e7y, fone)

let e7_ok (_: unit)
  : Lemma (on_curve e7 /\ peq e7 (SM.smul (7 * n) g))
  = assert_norm (on_curve e7);
    assert_norm (peq e7 (point_add e6 e1));
    e6_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (6 * n) n g e6 e1;
    step 6;
    SM.smul_ok (7 * n) g;
    peq_trans e7 (point_add e6 e1) (SM.smul (7 * n) g)

[@@"opaque_to_smt"]
let e8x : felem =
  assert_norm (21262057306151627953595685090280431278183829487175876377991189246716355947009 < prime);
  21262057306151627953595685090280431278183829487175876377991189246716355947009

[@@"opaque_to_smt"]
let e8y : felem =
  assert_norm (41749993296225487051377864631615517161996906063147759678534462689479575333124 < prime);
  41749993296225487051377864631615517161996906063147759678534462689479575333124

let e8 : proj_point = (e8x, e8y, fone)

let e8_ok (_: unit)
  : Lemma (on_curve e8 /\ peq e8 (SM.smul (8 * n) g))
  = assert_norm (on_curve e8);
    assert_norm (peq e8 (point_add e7 e1));
    e7_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (7 * n) n g e7 e1;
    step 7;
    SM.smul_ok (8 * n) g;
    peq_trans e8 (point_add e7 e1) (SM.smul (8 * n) g)

[@@"opaque_to_smt"]
let e9x : felem =
  assert_norm (78173298682877769088723994436027545680738210601369041078747105985693655485630 < prime);
  78173298682877769088723994436027545680738210601369041078747105985693655485630

[@@"opaque_to_smt"]
let e9y : felem =
  assert_norm (92362876758821804597230797234617159328445543067760556585160674174871431781431 < prime);
  92362876758821804597230797234617159328445543067760556585160674174871431781431

let e9 : proj_point = (e9x, e9y, fone)

let e9_ok (_: unit)
  : Lemma (on_curve e9 /\ peq e9 (SM.smul (9 * n) g))
  = assert_norm (on_curve e9);
    assert_norm (peq e9 (point_add e8 e1));
    e8_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (8 * n) n g e8 e1;
    step 8;
    SM.smul_ok (9 * n) g;
    peq_trans e9 (point_add e8 e1) (SM.smul (9 * n) g)

[@@"opaque_to_smt"]
let e10x : felem =
  assert_norm (72488970228380509287422715226575535698893157273063074627791787432852706183111 < prime);
  72488970228380509287422715226575535698893157273063074627791787432852706183111

[@@"opaque_to_smt"]
let e10y : felem =
  assert_norm (62070622898698443831883535403436258712770888294397026493185421712108624767191 < prime);
  62070622898698443831883535403436258712770888294397026493185421712108624767191

let e10 : proj_point = (e10x, e10y, fone)

let e10_ok (_: unit)
  : Lemma (on_curve e10 /\ peq e10 (SM.smul (10 * n) g))
  = assert_norm (on_curve e10);
    assert_norm (peq e10 (point_add e9 e1));
    e9_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (9 * n) n g e9 e1;
    step 9;
    SM.smul_ok (10 * n) g;
    peq_trans e10 (point_add e9 e1) (SM.smul (10 * n) g)

[@@"opaque_to_smt"]
let e11x : felem =
  assert_norm (53957576663012291606402345341061437133522758407718089353314528343643821967563 < prime);
  53957576663012291606402345341061437133522758407718089353314528343643821967563

[@@"opaque_to_smt"]
let e11y : felem =
  assert_norm (98386217607324929854432842186271083758341411730506808463586570492533445740059 < prime);
  98386217607324929854432842186271083758341411730506808463586570492533445740059

let e11 : proj_point = (e11x, e11y, fone)

let e11_ok (_: unit)
  : Lemma (on_curve e11 /\ peq e11 (SM.smul (11 * n) g))
  = assert_norm (on_curve e11);
    assert_norm (peq e11 (point_add e10 e1));
    e10_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (10 * n) n g e10 e1;
    step 10;
    SM.smul_ok (11 * n) g;
    peq_trans e11 (point_add e10 e1) (SM.smul (11 * n) g)

[@@"opaque_to_smt"]
let e12x : felem =
  assert_norm (94111259592240215275188773285036844871058226277992966241101117022315524122714 < prime);
  94111259592240215275188773285036844871058226277992966241101117022315524122714

[@@"opaque_to_smt"]
let e12y : felem =
  assert_norm (76870767327212528811304566602812752860184934880685532702451763239157141742375 < prime);
  76870767327212528811304566602812752860184934880685532702451763239157141742375

let e12 : proj_point = (e12x, e12y, fone)

let e12_ok (_: unit)
  : Lemma (on_curve e12 /\ peq e12 (SM.smul (12 * n) g))
  = assert_norm (on_curve e12);
    assert_norm (peq e12 (point_add e11 e1));
    e11_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (11 * n) n g e11 e1;
    step 11;
    SM.smul_ok (12 * n) g;
    peq_trans e12 (point_add e11 e1) (SM.smul (12 * n) g)

[@@"opaque_to_smt"]
let e13x : felem =
  assert_norm (109699032664856045668214896063362497021339186688470416858630178803463338613416 < prime);
  109699032664856045668214896063362497021339186688470416858630178803463338613416

[@@"opaque_to_smt"]
let e13y : felem =
  assert_norm (4835088675770141268294878046681321747490758260515711581034896622314066275713 < prime);
  4835088675770141268294878046681321747490758260515711581034896622314066275713

let e13 : proj_point = (e13x, e13y, fone)

let e13_ok (_: unit)
  : Lemma (on_curve e13 /\ peq e13 (SM.smul (13 * n) g))
  = assert_norm (on_curve e13);
    assert_norm (peq e13 (point_add e12 e1));
    e12_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (12 * n) n g e12 e1;
    step 12;
    SM.smul_ok (13 * n) g;
    peq_trans e13 (point_add e12 e1) (SM.smul (13 * n) g)

[@@"opaque_to_smt"]
let e14x : felem =
  assert_norm (33301309993451753050311554695703528430361259803437469669590207169100761277412 < prime);
  33301309993451753050311554695703528430361259803437469669590207169100761277412

[@@"opaque_to_smt"]
let e14y : felem =
  assert_norm (91711666877231500617203373035680263572492971120307578300405368749466283229019 < prime);
  91711666877231500617203373035680263572492971120307578300405368749466283229019

let e14 : proj_point = (e14x, e14y, fone)

let e14_ok (_: unit)
  : Lemma (on_curve e14 /\ peq e14 (SM.smul (14 * n) g))
  = assert_norm (on_curve e14);
    assert_norm (peq e14 (point_add e13 e1));
    e13_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (13 * n) n g e13 e1;
    step 13;
    SM.smul_ok (14 * n) g;
    peq_trans e14 (point_add e13 e1) (SM.smul (14 * n) g)

[@@"opaque_to_smt"]
let e15x : felem =
  assert_norm (97505755694356382817881959832717013755620551362654128955029190924747025549326 < prime);
  97505755694356382817881959832717013755620551362654128955029190924747025549326

[@@"opaque_to_smt"]
let e15y : felem =
  assert_norm (39856815248295663243990443767776362321337592747889787217974905533720651000664 < prime);
  39856815248295663243990443767776362321337592747889787217974905533720651000664

let e15 : proj_point = (e15x, e15y, fone)

let e15_ok (_: unit)
  : Lemma (on_curve e15 /\ peq e15 (SM.smul (15 * n) g))
  = assert_norm (on_curve e15);
    assert_norm (peq e15 (point_add e14 e1));
    e14_ok ();
    e1_ok ();
    g_on_curve ();
    SM.smul_add_congr (14 * n) n g e14 e1;
    step 14;
    SM.smul_ok (15 * n) g;
    peq_trans e15 (point_add e14 e1) (SM.smul (15 * n) g)

#pop-options
