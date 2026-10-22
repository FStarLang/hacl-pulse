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
(** The fixed-base window's third table: the sixteen multiples of
    [2^128 G].

    {!Spec.P256.Base} says what the base point is; this says what the
    table built from it holds, so that the table can be a constant in the
    binary rather than fifteen additions on every call.  The entries are
    affine, and each is settled by two [assert_norm]s -- that it is on the
    curve, and that it is the previous entry plus the base point -- and one
    application of {!Spec.P256.Smul.smul_add_congr}.

    This is {!Spec.K256.Win2} on a different curve. *)
module Spec.P256.Win2

module G = Spec.Group.Smul
module SM = Spec.P256.Smul
module Base = Spec.P256.Base
module Math = FStar.Math.Lemmas

open Spec.P256
open Spec.P256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d 2^128]-th multiple of [g]. *)
let n : nat = pow2 128

(** [(k + 1) n] as [k n + n], which is the step the chain takes. *)
let step (k: nat) : Lemma (k * n + n == (k + 1) * n)
  = Math.distributivity_add_left k 1 n

(** {2 The first two entries} *)

let e0 : proj_point = point_at_infinity

let e0_ok (_: unit)
  : Lemma (on_curve e0 /\ peq e0 (SM.smul (0 * n) g))
  = point_at_infinity_on_curve ();
    SM.smul_zero g;
    peq_refl e0

let e1 : proj_point = Base.q2

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul (1 * n) g) /\ peq e1 (SM.smul n g))
  = Base.q2_ok ()

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : felem =
  assert_norm (73450604269630675300143354721287867787104940331898087301873080305942319031902 < prime);
  73450604269630675300143354721287867787104940331898087301873080305942319031902

[@@"opaque_to_smt"]
let e2y : felem =
  assert_norm (61150582011930467138439561607227183610502048913145767873791961751611609242875 < prime);
  61150582011930467138439561607227183610502048913145767873791961751611609242875

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
  assert_norm (112495727131302244506157669471790202209849926651017016481532073180322115017576 < prime);
  112495727131302244506157669471790202209849926651017016481532073180322115017576

[@@"opaque_to_smt"]
let e3y : felem =
  assert_norm (88228053145992414849958298035823172674083888062809552550982514976029750463913 < prime);
  88228053145992414849958298035823172674083888062809552550982514976029750463913

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
  assert_norm (18348424709969931834174091430613018498698081298566264338878701168549980217100 < prime);
  18348424709969931834174091430613018498698081298566264338878701168549980217100

[@@"opaque_to_smt"]
let e4y : felem =
  assert_norm (47813918924079085448124957596124386029763830498939859267265976337216511217016 < prime);
  47813918924079085448124957596124386029763830498939859267265976337216511217016

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
  assert_norm (110057854901849053551963599269123617770351011376565878356873678711237774731091 < prime);
  110057854901849053551963599269123617770351011376565878356873678711237774731091

[@@"opaque_to_smt"]
let e5y : felem =
  assert_norm (53262433806948048836051074507666453919313300622218916858984573400786654175756 < prime);
  53262433806948048836051074507666453919313300622218916858984573400786654175756

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
  assert_norm (66319246301998730580303475764950480122057533598883472837408190527776899473722 < prime);
  66319246301998730580303475764950480122057533598883472837408190527776899473722

[@@"opaque_to_smt"]
let e6y : felem =
  assert_norm (18907407074987267616555985939638275204539820358791916938134460968016774983444 < prime);
  18907407074987267616555985939638275204539820358791916938134460968016774983444

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
  assert_norm (93997005483409056574292506670855998671122695415184921665307753867243029004670 < prime);
  93997005483409056574292506670855998671122695415184921665307753867243029004670

[@@"opaque_to_smt"]
let e7y : felem =
  assert_norm (82447652178856307637271643338242285051067413160973580514545415294389056307024 < prime);
  82447652178856307637271643338242285051067413160973580514545415294389056307024

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
  assert_norm (55881013555429575228667838642131238672304236081211634755366845332562345107012 < prime);
  55881013555429575228667838642131238672304236081211634755366845332562345107012

[@@"opaque_to_smt"]
let e8y : felem =
  assert_norm (63221592520063918995483689622179447143784318408606332570484522880814153536195 < prime);
  63221592520063918995483689622179447143784318408606332570484522880814153536195

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
  assert_norm (3317968300832170250262679874188701726794969352736461249532170707564638353504 < prime);
  3317968300832170250262679874188701726794969352736461249532170707564638353504

[@@"opaque_to_smt"]
let e9y : felem =
  assert_norm (114927546492308911530193275169287899159142770805390334460171644021816423389257 < prime);
  114927546492308911530193275169287899159142770805390334460171644021816423389257

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
  assert_norm (58907660477246598624012737458272246662348758783306483098131089031275125616770 < prime);
  58907660477246598624012737458272246662348758783306483098131089031275125616770

[@@"opaque_to_smt"]
let e10y : felem =
  assert_norm (44318971118060039042386730479334133667102325703167803473368357819418495670124 < prime);
  44318971118060039042386730479334133667102325703167803473368357819418495670124

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
  assert_norm (61959187583508928215122788769008856272341303587300237361444800247738273282667 < prime);
  61959187583508928215122788769008856272341303587300237361444800247738273282667

[@@"opaque_to_smt"]
let e11y : felem =
  assert_norm (36713200541894602909340208922158536510823493783587111323077668321599272088312 < prime);
  36713200541894602909340208922158536510823493783587111323077668321599272088312

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
  assert_norm (2686958844946040902231671854462711160306226305959818014206152149179009888466 < prime);
  2686958844946040902231671854462711160306226305959818014206152149179009888466

[@@"opaque_to_smt"]
let e12y : felem =
  assert_norm (23840713278941733643383365628008085001815546829228672010376666862196243884236 < prime);
  23840713278941733643383365628008085001815546829228672010376666862196243884236

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
  assert_norm (102054279059696205709729248414742695125755534325731481350010146811613419801771 < prime);
  102054279059696205709729248414742695125755534325731481350010146811613419801771

[@@"opaque_to_smt"]
let e13y : felem =
  assert_norm (101532591139388735011844224799093776110259518733839661196306107723992985077193 < prime);
  101532591139388735011844224799093776110259518733839661196306107723992985077193

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
  assert_norm (66069329310679293614386586714188175830082751723898912444608883942357135175866 < prime);
  66069329310679293614386586714188175830082751723898912444608883942357135175866

[@@"opaque_to_smt"]
let e14y : felem =
  assert_norm (104896112990701721076460740012507944784379984300743605244735111929828526842697 < prime);
  104896112990701721076460740012507944784379984300743605244735111929828526842697

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
  assert_norm (4935214691883965582191718901659083834192135906409251940576855037973981742122 < prime);
  4935214691883965582191718901659083834192135906409251940576855037973981742122

[@@"opaque_to_smt"]
let e15y : felem =
  assert_norm (50731416713822308357678305697901141284875337475230624166672204232009998403786 < prime);
  50731416713822308357678305697901141284875337475230624166672204232009998403786

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
