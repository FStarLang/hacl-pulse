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

(** The sixteen multiples of the generator, which is the first of the fixed-base
    window's four tables.

    {!Spec.Ed25519.Base} says what the four base points are; this says what
    the table built from one of them holds, so that the table can be a
    constant in the binary rather than sixty additions on every signature.

    The entries are the *affine* representatives, so [z] is one throughout
    and the fourth coordinate is the product of the first two.  Each is
    settled by two [assert_norm]s -- that it is on the curve, and that it
    is the previous entry plus the base point -- and one application of
    {!Spec.Group.Smul.smul_add_congr}, which turns a chain of additions
    into a statement about [smul].  The chain is the reason the entries
    are stored affine: an [assert_norm] over a projective quadruple
    carries whatever denominators the previous addition happened to leave,
    and by the fifteenth entry the numbers have stopped being numbers the
    normaliser can compare.

    The coordinates are [opaque_to_smt] for the reason
    {!Spec.Ed25519.Base}'s are: everything said about them is settled by
    the normaliser, and forty-two two-hundred-and-fifty-five-bit literals
    in one solver context is not a context anything else terminates in. *)
module Spec.Ed25519.Win0

module G = Spec.Group.Smul
module SM = Spec.Ed25519.Smul
module Base = Spec.Ed25519.Base
module Math = FStar.Math.Lemmas

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d 1]-th multiple of [g]. *)
let n : nat = 1

(** [(k + 1) n] as [k n + n], which is the step the chain takes. *)
let step (k: nat) : Lemma (k * n + n == (k + 1) * n)
  = Math.distributivity_add_left k 1 n

(** {2 The first two entries}

    Nothing and the base point itself, both of which are already known. *)

let e0 : ext_point = point_at_infinity

let e0_ok (_: unit)
  : Lemma (on_curve e0 /\ point_equal e0 (SM.smul (0 * n) g))
  = point_at_infinity_on_curve ();
    SM.smul_zero g;
    point_equal_refl e0

let e1 : ext_point = g

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ point_equal e1 (SM.smul (1 * n) g))
  = Base.g_ok ()

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : elem =
  assert_norm (24727413235106541002554574571675588834622768167397638456726423682521233608206 < prime);
  24727413235106541002554574571675588834622768167397638456726423682521233608206

[@@"opaque_to_smt"]
let e2y : elem =
  assert_norm (15549675580280190176352668710449542251549572066445060580507079593062643049417 < prime);
  15549675580280190176352668710449542251549572066445060580507079593062643049417

[@@"opaque_to_smt"]
let e2t : elem =
  assert_norm (16552979481334663544878610556091376071931149008662153799327195285289362371585 < prime);
  16552979481334663544878610556091376071931149008662153799327195285289362371585

let e2 : ext_point = (e2x, e2y, one, e2t)

let e2_ok (_: unit)
  : Lemma (on_curve e2 /\ point_equal e2 (SM.smul (2 * n) g))
  = assert_norm (on_curve e2);
    assert_norm (point_equal e2 (point_add e1 e1));
    e1_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (1 * n) n g e1 e1;
    step 1;
    SM.smul_ok (2 * n) g;
    point_equal_trans e2 (point_add e1 e1) (SM.smul (2 * n) g)

[@@"opaque_to_smt"]
let e3x : elem =
  assert_norm (46896733464454938657123544595386787789046198280132665686241321779790909858396 < prime);
  46896733464454938657123544595386787789046198280132665686241321779790909858396

[@@"opaque_to_smt"]
let e3y : elem =
  assert_norm (8324843778533443976490377120369201138301417226297555316741202210403726505172 < prime);
  8324843778533443976490377120369201138301417226297555316741202210403726505172

[@@"opaque_to_smt"]
let e3t : elem =
  assert_norm (19133203167024340156157901305709655404499344800967978305064989153409356768282 < prime);
  19133203167024340156157901305709655404499344800967978305064989153409356768282

let e3 : ext_point = (e3x, e3y, one, e3t)

let e3_ok (_: unit)
  : Lemma (on_curve e3 /\ point_equal e3 (SM.smul (3 * n) g))
  = assert_norm (on_curve e3);
    assert_norm (point_equal e3 (point_add e2 e1));
    e2_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (2 * n) n g e2 e1;
    step 2;
    SM.smul_ok (3 * n) g;
    point_equal_trans e3 (point_add e2 e1) (SM.smul (3 * n) g)

[@@"opaque_to_smt"]
let e4x : elem =
  assert_norm (14582954232372986451776170844943001818709880559417862259286374126315108956272 < prime);
  14582954232372986451776170844943001818709880559417862259286374126315108956272

[@@"opaque_to_smt"]
let e4y : elem =
  assert_norm (32483318716863467900234833297694612235682047836132991208333042722294373421359 < prime);
  32483318716863467900234833297694612235682047836132991208333042722294373421359

[@@"opaque_to_smt"]
let e4t : elem =
  assert_norm (15591078450528575260807955779595146919206594628260116491306850071973737403224 < prime);
  15591078450528575260807955779595146919206594628260116491306850071973737403224

let e4 : ext_point = (e4x, e4y, one, e4t)

let e4_ok (_: unit)
  : Lemma (on_curve e4 /\ point_equal e4 (SM.smul (4 * n) g))
  = assert_norm (on_curve e4);
    assert_norm (point_equal e4 (point_add e3 e1));
    e3_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (3 * n) n g e3 e1;
    step 3;
    SM.smul_ok (4 * n) g;
    point_equal_trans e4 (point_add e3 e1) (SM.smul (4 * n) g)

[@@"opaque_to_smt"]
let e5x : elem =
  assert_norm (33467004535436536005251147249499675200073690106659565782908757308821616914995 < prime);
  33467004535436536005251147249499675200073690106659565782908757308821616914995

[@@"opaque_to_smt"]
let e5y : elem =
  assert_norm (43097193783671926753355113395909008640284023746042808659097434958891230611693 < prime);
  43097193783671926753355113395909008640284023746042808659097434958891230611693

[@@"opaque_to_smt"]
let e5t : elem =
  assert_norm (52631435118507418230927645098360784166288333741771923328027903523704223039952 < prime);
  52631435118507418230927645098360784166288333741771923328027903523704223039952

let e5 : ext_point = (e5x, e5y, one, e5t)

let e5_ok (_: unit)
  : Lemma (on_curve e5 /\ point_equal e5 (SM.smul (5 * n) g))
  = assert_norm (on_curve e5);
    assert_norm (point_equal e5 (point_add e4 e1));
    e4_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (4 * n) n g e4 e1;
    step 4;
    SM.smul_ok (5 * n) g;
    point_equal_trans e5 (point_add e4 e1) (SM.smul (5 * n) g)

[@@"opaque_to_smt"]
let e6x : elem =
  assert_norm (34643617590234865996699167120328052565261792237873803846102513686264813449789 < prime);
  34643617590234865996699167120328052565261792237873803846102513686264813449789

[@@"opaque_to_smt"]
let e6y : elem =
  assert_norm (2399184961499513294557607325187831088545696902880432827228757905043131825908 < prime);
  2399184961499513294557607325187831088545696902880432827228757905043131825908

[@@"opaque_to_smt"]
let e6t : elem =
  assert_norm (27228768421258538231954343865440844652488997325483373020760696800100167381458 < prime);
  27228768421258538231954343865440844652488997325483373020760696800100167381458

let e6 : ext_point = (e6x, e6y, one, e6t)

let e6_ok (_: unit)
  : Lemma (on_curve e6 /\ point_equal e6 (SM.smul (6 * n) g))
  = assert_norm (on_curve e6);
    assert_norm (point_equal e6 (point_add e5 e1));
    e5_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (5 * n) n g e5 e1;
    step 5;
    SM.smul_ok (6 * n) g;
    point_equal_trans e6 (point_add e5 e1) (SM.smul (6 * n) g)

[@@"opaque_to_smt"]
let e7x : elem =
  assert_norm (9199134265559022971505535402808359556995554859516252602543778295037484220679 < prime);
  9199134265559022971505535402808359556995554859516252602543778295037484220679

[@@"opaque_to_smt"]
let e7y : elem =
  assert_norm (22512087849695599276028560866629687720820254811233262850576678203618951717560 < prime);
  22512087849695599276028560866629687720820254811233262850576678203618951717560

[@@"opaque_to_smt"]
let e7t : elem =
  assert_norm (7969306344939599448108779620249142998159244560978835759187616138611789393179 < prime);
  7969306344939599448108779620249142998159244560978835759187616138611789393179

let e7 : ext_point = (e7x, e7y, one, e7t)

let e7_ok (_: unit)
  : Lemma (on_curve e7 /\ point_equal e7 (SM.smul (7 * n) g))
  = assert_norm (on_curve e7);
    assert_norm (point_equal e7 (point_add e6 e1));
    e6_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (6 * n) n g e6 e1;
    step 6;
    SM.smul_ok (7 * n) g;
    point_equal_trans e7 (point_add e6 e1) (SM.smul (7 * n) g)

[@@"opaque_to_smt"]
let e8x : elem =
  assert_norm (46706390780465557264338673484185971070529246228527338942042475661633188627656 < prime);
  46706390780465557264338673484185971070529246228527338942042475661633188627656

[@@"opaque_to_smt"]
let e8y : elem =
  assert_norm (15299170165656271974649334809062094114079726227711063015095704409550798436788 < prime);
  15299170165656271974649334809062094114079726227711063015095704409550798436788

[@@"opaque_to_smt"]
let e8t : elem =
  assert_norm (20041966898814491726444579060880528788025287386839181497696933332457633763775 < prime);
  20041966898814491726444579060880528788025287386839181497696933332457633763775

let e8 : ext_point = (e8x, e8y, one, e8t)

let e8_ok (_: unit)
  : Lemma (on_curve e8 /\ point_equal e8 (SM.smul (8 * n) g))
  = assert_norm (on_curve e8);
    assert_norm (point_equal e8 (point_add e7 e1));
    e7_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (7 * n) n g e7 e1;
    step 7;
    SM.smul_ok (8 * n) g;
    point_equal_trans e8 (point_add e7 e1) (SM.smul (8 * n) g)

[@@"opaque_to_smt"]
let e9x : elem =
  assert_norm (24193060302538010417230488029838514081720802923509845138863968807030823940444 < prime);
  24193060302538010417230488029838514081720802923509845138863968807030823940444

[@@"opaque_to_smt"]
let e9y : elem =
  assert_norm (57551756252899625001155759838357770487605224608455116862194664796369308545472 < prime);
  57551756252899625001155759838357770487605224608455116862194664796369308545472

[@@"opaque_to_smt"]
let e9t : elem =
  assert_norm (41812410146810177838232618347187858057822209473536282119740688245908349056101 < prime);
  41812410146810177838232618347187858057822209473536282119740688245908349056101

let e9 : ext_point = (e9x, e9y, one, e9t)

let e9_ok (_: unit)
  : Lemma (on_curve e9 /\ point_equal e9 (SM.smul (9 * n) g))
  = assert_norm (on_curve e9);
    assert_norm (point_equal e9 (point_add e8 e1));
    e8_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (8 * n) n g e8 e1;
    step 8;
    SM.smul_ok (9 * n) g;
    point_equal_trans e9 (point_add e8 e1) (SM.smul (9 * n) g)

[@@"opaque_to_smt"]
let e10x : elem =
  assert_norm (43500613248243327786121022071801015118933854441360174117148262713429272820047 < prime);
  43500613248243327786121022071801015118933854441360174117148262713429272820047

[@@"opaque_to_smt"]
let e10y : elem =
  assert_norm (45005105423099817237495816771148012388779685712352441364231470781391834741548 < prime);
  45005105423099817237495816771148012388779685712352441364231470781391834741548

[@@"opaque_to_smt"]
let e10t : elem =
  assert_norm (24821324590696316218023342309218542169263958968336678574020759857624812078654 < prime);
  24821324590696316218023342309218542169263958968336678574020759857624812078654

let e10 : ext_point = (e10x, e10y, one, e10t)

let e10_ok (_: unit)
  : Lemma (on_curve e10 /\ point_equal e10 (SM.smul (10 * n) g))
  = assert_norm (on_curve e10);
    assert_norm (point_equal e10 (point_add e9 e1));
    e9_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (9 * n) n g e9 e1;
    step 9;
    SM.smul_ok (10 * n) g;
    point_equal_trans e10 (point_add e9 e1) (SM.smul (10 * n) g)

[@@"opaque_to_smt"]
let e11x : elem =
  assert_norm (9451145793506787353375160377761530931587019091193333050860601958827395183563 < prime);
  9451145793506787353375160377761530931587019091193333050860601958827395183563

[@@"opaque_to_smt"]
let e11y : elem =
  assert_norm (20609402718286069808115703540855311742885093522056241285814584245966805874451 < prime);
  20609402718286069808115703540855311742885093522056241285814584245966805874451

[@@"opaque_to_smt"]
let e11t : elem =
  assert_norm (41115672721981046446137450827132502570366877864937539642265045489017153122004 < prime);
  41115672721981046446137450827132502570366877864937539642265045489017153122004

let e11 : ext_point = (e11x, e11y, one, e11t)

let e11_ok (_: unit)
  : Lemma (on_curve e11 /\ point_equal e11 (SM.smul (11 * n) g))
  = assert_norm (on_curve e11);
    assert_norm (point_equal e11 (point_add e10 e1));
    e10_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (10 * n) n g e10 e1;
    step 10;
    SM.smul_ok (11 * n) g;
    point_equal_trans e11 (point_add e10 e1) (SM.smul (11 * n) g)

[@@"opaque_to_smt"]
let e12x : elem =
  assert_norm (32159939716063394567822525359727347405356413309540137282993608327129696604205 < prime);
  32159939716063394567822525359727347405356413309540137282993608327129696604205

[@@"opaque_to_smt"]
let e12y : elem =
  assert_norm (29147333543209904737197244325450674102993621692520459538942544703173373584633 < prime);
  29147333543209904737197244325450674102993621692520459538942544703173373584633

[@@"opaque_to_smt"]
let e12t : elem =
  assert_norm (19541867741520148118751118771412993529806969384857531365223040978324730617035 < prime);
  19541867741520148118751118771412993529806969384857531365223040978324730617035

let e12 : ext_point = (e12x, e12y, one, e12t)

let e12_ok (_: unit)
  : Lemma (on_curve e12 /\ point_equal e12 (SM.smul (12 * n) g))
  = assert_norm (on_curve e12);
    assert_norm (point_equal e12 (point_add e11 e1));
    e11_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (11 * n) n g e11 e1;
    step 11;
    SM.smul_ok (12 * n) g;
    point_equal_trans e12 (point_add e11 e1) (SM.smul (12 * n) g)

[@@"opaque_to_smt"]
let e13x : elem =
  assert_norm (7442235066513780790779899786332475485840754593728627195931759107337804079085 < prime);
  7442235066513780790779899786332475485840754593728627195931759107337804079085

[@@"opaque_to_smt"]
let e13y : elem =
  assert_norm (8529785864514984411577036536286432879603480171865651918962709025066066124672 < prime);
  8529785864514984411577036536286432879603480171865651918962709025066066124672

[@@"opaque_to_smt"]
let e13t : elem =
  assert_norm (29471055441072170259805152731682457644447474860555123755684575143128358334291 < prime);
  29471055441072170259805152731682457644447474860555123755684575143128358334291

let e13 : ext_point = (e13x, e13y, one, e13t)

let e13_ok (_: unit)
  : Lemma (on_curve e13 /\ point_equal e13 (SM.smul (13 * n) g))
  = assert_norm (on_curve e13);
    assert_norm (point_equal e13 (point_add e12 e1));
    e12_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (12 * n) n g e12 e1;
    step 12;
    SM.smul_ok (13 * n) g;
    point_equal_trans e13 (point_add e12 e1) (SM.smul (13 * n) g)

[@@"opaque_to_smt"]
let e14x : elem =
  assert_norm (14642270634066990240227516988620748386040643134865523775420225321890511918521 < prime);
  14642270634066990240227516988620748386040643134865523775420225321890511918521

[@@"opaque_to_smt"]
let e14y : elem =
  assert_norm (35422008320351900419562335198749713095866812710345432231966142485751234570297 < prime);
  35422008320351900419562335198749713095866812710345432231966142485751234570297

[@@"opaque_to_smt"]
let e14t : elem =
  assert_norm (46254600437113092920986864060763897395415604951161981300247173016751552185056 < prime);
  46254600437113092920986864060763897395415604951161981300247173016751552185056

let e14 : ext_point = (e14x, e14y, one, e14t)

let e14_ok (_: unit)
  : Lemma (on_curve e14 /\ point_equal e14 (SM.smul (14 * n) g))
  = assert_norm (on_curve e14);
    assert_norm (point_equal e14 (point_add e13 e1));
    e13_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (13 * n) n g e13 e1;
    step 13;
    SM.smul_ok (14 * n) g;
    point_equal_trans e14 (point_add e13 e1) (SM.smul (14 * n) g)

[@@"opaque_to_smt"]
let e15x : elem =
  assert_norm (35771902585589234259498423420223840099331465042459337605611172842168536632769 < prime);
  35771902585589234259498423420223840099331465042459337605611172842168536632769

[@@"opaque_to_smt"]
let e15y : elem =
  assert_norm (8502034780705657720897159939055122322178084209392286764802307224484658961631 < prime);
  8502034780705657720897159939055122322178084209392286764802307224484658961631

[@@"opaque_to_smt"]
let e15t : elem =
  assert_norm (42609173769455554086108030252596314253679554082059705507322920389417832202025 < prime);
  42609173769455554086108030252596314253679554082059705507322920389417832202025

let e15 : ext_point = (e15x, e15y, one, e15t)

let e15_ok (_: unit)
  : Lemma (on_curve e15 /\ point_equal e15 (SM.smul (15 * n) g))
  = assert_norm (on_curve e15);
    assert_norm (point_equal e15 (point_add e14 e1));
    e14_ok ();
    e1_ok ();
    g_on_curve ();
    G.smul_add_congr SM.eg (14 * n) n g e14 e1;
    step 14;
    SM.smul_ok (15 * n) g;
    point_equal_trans e15 (point_add e14 e1) (SM.smul (15 * n) g)


#pop-options
