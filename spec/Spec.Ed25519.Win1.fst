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

(** The sixteen multiples of [2^64 g], which is the second of the fixed-base
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
module Spec.Ed25519.Win1

module G = Spec.Group.Smul
module SM = Spec.Ed25519.Smul
module Base = Spec.Ed25519.Base
module Math = FStar.Math.Lemmas

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d pow2 64]-th multiple of [g]. *)
let n : nat = pow2 64

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

let e1 : ext_point = Base.b1

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ point_equal e1 (SM.smul (1 * n) g))
  = Base.b1_ok ()

(** The same, with the multiple written [n] as the chain below uses it. *)
let e1_ok_n (_: unit)
  : Lemma (on_curve e1 /\ point_equal e1 (SM.smul n g))
  = e1_ok ();
    assert (1 * n == n)

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : elem =
  assert_norm (1010247752756362260881243234901448331704228065985397871388404881884689704343 < prime);
  1010247752756362260881243234901448331704228065985397871388404881884689704343

[@@"opaque_to_smt"]
let e2y : elem =
  assert_norm (34905110436806704375115117043721051740842418404017689336019589974414716422638 < prime);
  34905110436806704375115117043721051740842418404017689336019589974414716422638

[@@"opaque_to_smt"]
let e2t : elem =
  assert_norm (19849296478328768495495805247695997168837367132856874395156421056346847466394 < prime);
  19849296478328768495495805247695997168837367132856874395156421056346847466394

let e2 : ext_point = (e2x, e2y, one, e2t)

let e2_ok (_: unit)
  : Lemma (on_curve e2 /\ point_equal e2 (SM.smul (2 * n) g))
  = assert_norm (on_curve e2);
    assert_norm (point_equal e2 (point_add e1 e1));
    e1_ok_n ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (1 * n) n g e1 e1;
    step 1;
    SM.smul_ok (2 * n) g;
    point_equal_trans e2 (point_add e1 e1) (SM.smul (2 * n) g)

[@@"opaque_to_smt"]
let e3x : elem =
  assert_norm (8668195667617162713602608175515147103660941879429511114053709036044027311207 < prime);
  8668195667617162713602608175515147103660941879429511114053709036044027311207

[@@"opaque_to_smt"]
let e3y : elem =
  assert_norm (37681485510013466138918998841666858165213744209089186872109760116369856650799 < prime);
  37681485510013466138918998841666858165213744209089186872109760116369856650799

[@@"opaque_to_smt"]
let e3t : elem =
  assert_norm (8987285660766590138219011762984157073474138416691091583362974629489246270471 < prime);
  8987285660766590138219011762984157073474138416691091583362974629489246270471

let e3 : ext_point = (e3x, e3y, one, e3t)

let e3_ok (_: unit)
  : Lemma (on_curve e3 /\ point_equal e3 (SM.smul (3 * n) g))
  = assert_norm (on_curve e3);
    assert_norm (point_equal e3 (point_add e2 e1));
    e2_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (2 * n) n g e2 e1;
    step 2;
    SM.smul_ok (3 * n) g;
    point_equal_trans e3 (point_add e2 e1) (SM.smul (3 * n) g)

[@@"opaque_to_smt"]
let e4x : elem =
  assert_norm (49444157831517844751255683186086055092391671187830014667142777982061391761769 < prime);
  49444157831517844751255683186086055092391671187830014667142777982061391761769

[@@"opaque_to_smt"]
let e4y : elem =
  assert_norm (38325651754372413483217343763106935496036760575967773049932675282070249514007 < prime);
  38325651754372413483217343763106935496036760575967773049932675282070249514007

[@@"opaque_to_smt"]
let e4t : elem =
  assert_norm (43678687874783753989238000938645889054046194408155765536265092054211996908656 < prime);
  43678687874783753989238000938645889054046194408155765536265092054211996908656

let e4 : ext_point = (e4x, e4y, one, e4t)

let e4_ok (_: unit)
  : Lemma (on_curve e4 /\ point_equal e4 (SM.smul (4 * n) g))
  = assert_norm (on_curve e4);
    assert_norm (point_equal e4 (point_add e3 e1));
    e3_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (3 * n) n g e3 e1;
    step 3;
    SM.smul_ok (4 * n) g;
    point_equal_trans e4 (point_add e3 e1) (SM.smul (4 * n) g)

[@@"opaque_to_smt"]
let e5x : elem =
  assert_norm (24424117292259436307685934938063848544019468200375892548716527440009604940493 < prime);
  24424117292259436307685934938063848544019468200375892548716527440009604940493

[@@"opaque_to_smt"]
let e5y : elem =
  assert_norm (36583979248234726752743779762394860626104356418177578515410668973021968894858 < prime);
  36583979248234726752743779762394860626104356418177578515410668973021968894858

[@@"opaque_to_smt"]
let e5t : elem =
  assert_norm (23089229879023823317650486648615261113639661965809164793311284521221055636439 < prime);
  23089229879023823317650486648615261113639661965809164793311284521221055636439

let e5 : ext_point = (e5x, e5y, one, e5t)

let e5_ok (_: unit)
  : Lemma (on_curve e5 /\ point_equal e5 (SM.smul (5 * n) g))
  = assert_norm (on_curve e5);
    assert_norm (point_equal e5 (point_add e4 e1));
    e4_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (4 * n) n g e4 e1;
    step 4;
    SM.smul_ok (5 * n) g;
    point_equal_trans e5 (point_add e4 e1) (SM.smul (5 * n) g)

[@@"opaque_to_smt"]
let e6x : elem =
  assert_norm (49025407799462363586681626888639698365893077756861158880615624267162821984787 < prime);
  49025407799462363586681626888639698365893077756861158880615624267162821984787

[@@"opaque_to_smt"]
let e6y : elem =
  assert_norm (12818500738744348816718749150692681836882431285482295854460275860287501158274 < prime);
  12818500738744348816718749150692681836882431285482295854460275860287501158274

[@@"opaque_to_smt"]
let e6t : elem =
  assert_norm (26006868771002328881253046589605913386852383210104504704200133552093254321232 < prime);
  26006868771002328881253046589605913386852383210104504704200133552093254321232

let e6 : ext_point = (e6x, e6y, one, e6t)

let e6_ok (_: unit)
  : Lemma (on_curve e6 /\ point_equal e6 (SM.smul (6 * n) g))
  = assert_norm (on_curve e6);
    assert_norm (point_equal e6 (point_add e5 e1));
    e5_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (5 * n) n g e5 e1;
    step 5;
    SM.smul_ok (6 * n) g;
    point_equal_trans e6 (point_add e5 e1) (SM.smul (6 * n) g)

[@@"opaque_to_smt"]
let e7x : elem =
  assert_norm (47365806204061385358548986132911778319470339734863904634944103996966447908817 < prime);
  47365806204061385358548986132911778319470339734863904634944103996966447908817

[@@"opaque_to_smt"]
let e7y : elem =
  assert_norm (13815220452364022765430582649306621386616680709785487953250526715757190547494 < prime);
  13815220452364022765430582649306621386616680709785487953250526715757190547494

[@@"opaque_to_smt"]
let e7t : elem =
  assert_norm (53574871283165553125314121006188091071578967551114640432034301183164885326658 < prime);
  53574871283165553125314121006188091071578967551114640432034301183164885326658

let e7 : ext_point = (e7x, e7y, one, e7t)

let e7_ok (_: unit)
  : Lemma (on_curve e7 /\ point_equal e7 (SM.smul (7 * n) g))
  = assert_norm (on_curve e7);
    assert_norm (point_equal e7 (point_add e6 e1));
    e6_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (6 * n) n g e6 e1;
    step 6;
    SM.smul_ok (7 * n) g;
    point_equal_trans e7 (point_add e6 e1) (SM.smul (7 * n) g)

[@@"opaque_to_smt"]
let e8x : elem =
  assert_norm (48577842308630573365019333121847151099247213871386595032531930153824808034985 < prime);
  48577842308630573365019333121847151099247213871386595032531930153824808034985

[@@"opaque_to_smt"]
let e8y : elem =
  assert_norm (11698818496297094926714371527533498792080572905846263409223249541482347665093 < prime);
  11698818496297094926714371527533498792080572905846263409223249541482347665093

[@@"opaque_to_smt"]
let e8t : elem =
  assert_norm (46361589381050185680625026890177279253421462440776560773133113149222398787011 < prime);
  46361589381050185680625026890177279253421462440776560773133113149222398787011

let e8 : ext_point = (e8x, e8y, one, e8t)

let e8_ok (_: unit)
  : Lemma (on_curve e8 /\ point_equal e8 (SM.smul (8 * n) g))
  = assert_norm (on_curve e8);
    assert_norm (point_equal e8 (point_add e7 e1));
    e7_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (7 * n) n g e7 e1;
    step 7;
    SM.smul_ok (8 * n) g;
    point_equal_trans e8 (point_add e7 e1) (SM.smul (8 * n) g)

[@@"opaque_to_smt"]
let e9x : elem =
  assert_norm (13222046488766299514364610635437108363097903213218282608219742825881857234330 < prime);
  13222046488766299514364610635437108363097903213218282608219742825881857234330

[@@"opaque_to_smt"]
let e9y : elem =
  assert_norm (47420742890012183825412571504240435215708071406103861595174136388033735282873 < prime);
  47420742890012183825412571504240435215708071406103861595174136388033735282873

[@@"opaque_to_smt"]
let e9t : elem =
  assert_norm (2067233660098317162223538913144742441128454701867759828076670184168334903155 < prime);
  2067233660098317162223538913144742441128454701867759828076670184168334903155

let e9 : ext_point = (e9x, e9y, one, e9t)

let e9_ok (_: unit)
  : Lemma (on_curve e9 /\ point_equal e9 (SM.smul (9 * n) g))
  = assert_norm (on_curve e9);
    assert_norm (point_equal e9 (point_add e8 e1));
    e8_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (8 * n) n g e8 e1;
    step 8;
    SM.smul_ok (9 * n) g;
    point_equal_trans e9 (point_add e8 e1) (SM.smul (9 * n) g)

[@@"opaque_to_smt"]
let e10x : elem =
  assert_norm (11792182095377046280292607218491330984512111209047371812327617470585742042113 < prime);
  11792182095377046280292607218491330984512111209047371812327617470585742042113

[@@"opaque_to_smt"]
let e10y : elem =
  assert_norm (13130519911778611427704109750743368240508601344361713395372825573397458734889 < prime);
  13130519911778611427704109750743368240508601344361713395372825573397458734889

[@@"opaque_to_smt"]
let e10t : elem =
  assert_norm (37636635765299053122580863734444105913579915752174681732794933324582045132253 < prime);
  37636635765299053122580863734444105913579915752174681732794933324582045132253

let e10 : ext_point = (e10x, e10y, one, e10t)

let e10_ok (_: unit)
  : Lemma (on_curve e10 /\ point_equal e10 (SM.smul (10 * n) g))
  = assert_norm (on_curve e10);
    assert_norm (point_equal e10 (point_add e9 e1));
    e9_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (9 * n) n g e9 e1;
    step 9;
    SM.smul_ok (10 * n) g;
    point_equal_trans e10 (point_add e9 e1) (SM.smul (10 * n) g)

[@@"opaque_to_smt"]
let e11x : elem =
  assert_norm (10855098635758441430313689636497201170123253545015034342080851602335987402359 < prime);
  10855098635758441430313689636497201170123253545015034342080851602335987402359

[@@"opaque_to_smt"]
let e11y : elem =
  assert_norm (47818830870481122424288682493047260963410649396724694018664888930706645227637 < prime);
  47818830870481122424288682493047260963410649396724694018664888930706645227637

[@@"opaque_to_smt"]
let e11t : elem =
  assert_norm (39461041460775791314297826146393298084003042052838593535554184990730947805979 < prime);
  39461041460775791314297826146393298084003042052838593535554184990730947805979

let e11 : ext_point = (e11x, e11y, one, e11t)

let e11_ok (_: unit)
  : Lemma (on_curve e11 /\ point_equal e11 (SM.smul (11 * n) g))
  = assert_norm (on_curve e11);
    assert_norm (point_equal e11 (point_add e10 e1));
    e10_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (10 * n) n g e10 e1;
    step 10;
    SM.smul_ok (11 * n) g;
    point_equal_trans e11 (point_add e10 e1) (SM.smul (11 * n) g)

[@@"opaque_to_smt"]
let e12x : elem =
  assert_norm (50210437508936563612088547663111947689549164143986527154977065834504072446541 < prime);
  50210437508936563612088547663111947689549164143986527154977065834504072446541

[@@"opaque_to_smt"]
let e12y : elem =
  assert_norm (45586019548737311473039817728866341223061601575962934652814543884809892582944 < prime);
  45586019548737311473039817728866341223061601575962934652814543884809892582944

[@@"opaque_to_smt"]
let e12t : elem =
  assert_norm (5679111159433034892781296917463183770637899055840282659218554675912631545800 < prime);
  5679111159433034892781296917463183770637899055840282659218554675912631545800

let e12 : ext_point = (e12x, e12y, one, e12t)

let e12_ok (_: unit)
  : Lemma (on_curve e12 /\ point_equal e12 (SM.smul (12 * n) g))
  = assert_norm (on_curve e12);
    assert_norm (point_equal e12 (point_add e11 e1));
    e11_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (11 * n) n g e11 e1;
    step 11;
    SM.smul_ok (12 * n) g;
    point_equal_trans e12 (point_add e11 e1) (SM.smul (12 * n) g)

[@@"opaque_to_smt"]
let e13x : elem =
  assert_norm (33616366928889074968873567717836375813714298715676008230485514855908177894597 < prime);
  33616366928889074968873567717836375813714298715676008230485514855908177894597

[@@"opaque_to_smt"]
let e13y : elem =
  assert_norm (48178172581996375444100428200735720625774279145737689574213477038241439061117 < prime);
  48178172581996375444100428200735720625774279145737689574213477038241439061117

[@@"opaque_to_smt"]
let e13t : elem =
  assert_norm (25687523000380708910048216778386125946503922555990971288295719638534129558612 < prime);
  25687523000380708910048216778386125946503922555990971288295719638534129558612

let e13 : ext_point = (e13x, e13y, one, e13t)

let e13_ok (_: unit)
  : Lemma (on_curve e13 /\ point_equal e13 (SM.smul (13 * n) g))
  = assert_norm (on_curve e13);
    assert_norm (point_equal e13 (point_add e12 e1));
    e12_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (12 * n) n g e12 e1;
    step 12;
    SM.smul_ok (13 * n) g;
    point_equal_trans e13 (point_add e12 e1) (SM.smul (13 * n) g)

[@@"opaque_to_smt"]
let e14x : elem =
  assert_norm (56719776318220971800106543829839144076483576359333918902652489316218531471878 < prime);
  56719776318220971800106543829839144076483576359333918902652489316218531471878

[@@"opaque_to_smt"]
let e14y : elem =
  assert_norm (20990174859038521554516944625883728525404913511350227244172041291915035286249 < prime);
  20990174859038521554516944625883728525404913511350227244172041291915035286249

[@@"opaque_to_smt"]
let e14t : elem =
  assert_norm (29662718152312053710923063605020694611853594443752768757757867269136740469821 < prime);
  29662718152312053710923063605020694611853594443752768757757867269136740469821

let e14 : ext_point = (e14x, e14y, one, e14t)

let e14_ok (_: unit)
  : Lemma (on_curve e14 /\ point_equal e14 (SM.smul (14 * n) g))
  = assert_norm (on_curve e14);
    assert_norm (point_equal e14 (point_add e13 e1));
    e13_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (13 * n) n g e13 e1;
    step 13;
    SM.smul_ok (14 * n) g;
    point_equal_trans e14 (point_add e13 e1) (SM.smul (14 * n) g)

[@@"opaque_to_smt"]
let e15x : elem =
  assert_norm (19395763221897016278836929030896682409047235399585944047897808432981729573333 < prime);
  19395763221897016278836929030896682409047235399585944047897808432981729573333

[@@"opaque_to_smt"]
let e15y : elem =
  assert_norm (50554338297416887190495274275556067851439024893117496234220772938417219539764 < prime);
  50554338297416887190495274275556067851439024893117496234220772938417219539764

[@@"opaque_to_smt"]
let e15t : elem =
  assert_norm (28128842489434711332019030454051415288638221331015249698275022662207005509299 < prime);
  28128842489434711332019030454051415288638221331015249698275022662207005509299

let e15 : ext_point = (e15x, e15y, one, e15t)

let e15_ok (_: unit)
  : Lemma (on_curve e15 /\ point_equal e15 (SM.smul (15 * n) g))
  = assert_norm (on_curve e15);
    assert_norm (point_equal e15 (point_add e14 e1));
    e14_ok ();
    e1_ok_n ();
    g_on_curve ();
    G.smul_add_congr SM.eg (14 * n) n g e14 e1;
    step 14;
    SM.smul_ok (15 * n) g;
    point_equal_trans e15 (point_add e14 e1) (SM.smul (15 * n) g)


#pop-options
