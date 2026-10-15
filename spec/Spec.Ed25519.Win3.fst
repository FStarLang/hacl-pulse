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

(** The sixteen multiples of [2^192 g], which is the fourth of the fixed-base
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
module Spec.Ed25519.Win3

module G = Spec.Group.Smul
module SM = Spec.Ed25519.Smul
module Base = Spec.Ed25519.Base
module Math = FStar.Math.Lemmas

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d pow2 192]-th multiple of [g]. *)
let n : nat = pow2 192

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

let e1 : ext_point = Base.b3

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ point_equal e1 (SM.smul (1 * n) g))
  = Base.b3_ok ()

(** The same, with the multiple written [n] as the chain below uses it. *)
let e1_ok_n (_: unit)
  : Lemma (on_curve e1 /\ point_equal e1 (SM.smul n g))
  = e1_ok ();
    assert (1 * n == n)

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : elem =
  assert_norm (3047606020786028284132832726733152544116871735530526064566846233255159694164 < prime);
  3047606020786028284132832726733152544116871735530526064566846233255159694164

[@@"opaque_to_smt"]
let e2y : elem =
  assert_norm (27659277246517583802849237030891922618695698372984029484026220602549726330981 < prime);
  27659277246517583802849237030891922618695698372984029484026220602549726330981

[@@"opaque_to_smt"]
let e2t : elem =
  assert_norm (55463775194011380630519341519966098496461783503061503682191147761899681696535 < prime);
  55463775194011380630519341519966098496461783503061503682191147761899681696535

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
  assert_norm (53552365276772365554195944740419579336567243280359406876316960824458060850735 < prime);
  53552365276772365554195944740419579336567243280359406876316960824458060850735

[@@"opaque_to_smt"]
let e3y : elem =
  assert_norm (35650629018577479097518351282106281449357234554211723107920870271722340764833 < prime);
  35650629018577479097518351282106281449357234554211723107920870271722340764833

[@@"opaque_to_smt"]
let e3t : elem =
  assert_norm (48725770576057524395922610931165644107855277515890288558662755606729480475579 < prime);
  48725770576057524395922610931165644107855277515890288558662755606729480475579

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
  assert_norm (4540268506733343188936218306036274493398883371137067909932234450545784837367 < prime);
  4540268506733343188936218306036274493398883371137067909932234450545784837367

[@@"opaque_to_smt"]
let e4y : elem =
  assert_norm (26524790429314500794899586613374338447541369717354753326410262160257197201702 < prime);
  26524790429314500794899586613374338447541369717354753326410262160257197201702

[@@"opaque_to_smt"]
let e4t : elem =
  assert_norm (27064340452433824408075231212490175399137716169065836278056371689335065722963 < prime);
  27064340452433824408075231212490175399137716169065836278056371689335065722963

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
  assert_norm (12865836731680429964870836876539877689269983855221154391518173579833909670750 < prime);
  12865836731680429964870836876539877689269983855221154391518173579833909670750

[@@"opaque_to_smt"]
let e5y : elem =
  assert_norm (54505106968788366538694296953949362645181563690709832428447247381558104164043 < prime);
  54505106968788366538694296953949362645181563690709832428447247381558104164043

[@@"opaque_to_smt"]
let e5t : elem =
  assert_norm (54735226163646743872339795177233226952890802639235013584865684982131766866604 < prime);
  54735226163646743872339795177233226952890802639235013584865684982131766866604

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
  assert_norm (27309233825399062195904921979329113981086661526986937618719936163677276457174 < prime);
  27309233825399062195904921979329113981086661526986937618719936163677276457174

[@@"opaque_to_smt"]
let e6y : elem =
  assert_norm (23664340815210348297365347644997035152878505257530141761514215389790732085864 < prime);
  23664340815210348297365347644997035152878505257530141761514215389790732085864

[@@"opaque_to_smt"]
let e6t : elem =
  assert_norm (3235134023935946813960854593986148891597252708842439093051900113464250020957 < prime);
  3235134023935946813960854593986148891597252708842439093051900113464250020957

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
  assert_norm (3893115083351436905873278555138652971300169012092045419646561460555609943456 < prime);
  3893115083351436905873278555138652971300169012092045419646561460555609943456

[@@"opaque_to_smt"]
let e7y : elem =
  assert_norm (46558973982744083198660515712826007542465058910371209402946353543638590221192 < prime);
  46558973982744083198660515712826007542465058910371209402946353543638590221192

[@@"opaque_to_smt"]
let e7t : elem =
  assert_norm (5958418225845540917624462516639059268261615213494792378291789379969028156712 < prime);
  5958418225845540917624462516639059268261615213494792378291789379969028156712

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
  assert_norm (3446437814019273288244656713869208063996426786897354522951255709425681080283 < prime);
  3446437814019273288244656713869208063996426786897354522951255709425681080283

[@@"opaque_to_smt"]
let e8y : elem =
  assert_norm (10094282458565215422345041182173095708589654183994461384883702800600720181143 < prime);
  10094282458565215422345041182173095708589654183994461384883702800600720181143

[@@"opaque_to_smt"]
let e8t : elem =
  assert_norm (11143155699431656097381813171938507259196561272355038274301729945349223173674 < prime);
  11143155699431656097381813171938507259196561272355038274301729945349223173674

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
  assert_norm (9166983860573597536678994407454154394017163512765362417400042609013149907663 < prime);
  9166983860573597536678994407454154394017163512765362417400042609013149907663

[@@"opaque_to_smt"]
let e9y : elem =
  assert_norm (19314160636716930199278277812036949895874831496930780059179058068909835188156 < prime);
  19314160636716930199278277812036949895874831496930780059179058068909835188156

[@@"opaque_to_smt"]
let e9t : elem =
  assert_norm (25062627729687412262552920275437817334066088327911077216223299165824524151979 < prime);
  25062627729687412262552920275437817334066088327911077216223299165824524151979

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
  assert_norm (55697478570441008950922507637041902228958156438530598090234534650453947176888 < prime);
  55697478570441008950922507637041902228958156438530598090234534650453947176888

[@@"opaque_to_smt"]
let e10y : elem =
  assert_norm (54122029519256159014869894536816319630932421863407459643034369620543805678960 < prime);
  54122029519256159014869894536816319630932421863407459643034369620543805678960

[@@"opaque_to_smt"]
let e10t : elem =
  assert_norm (46814427880570000336376461353117244660803238463084371460635389152811754253617 < prime);
  46814427880570000336376461353117244660803238463084371460635389152811754253617

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
  assert_norm (32809162818583714370097548850185470268450645293186358655754349228844494036316 < prime);
  32809162818583714370097548850185470268450645293186358655754349228844494036316

[@@"opaque_to_smt"]
let e11y : elem =
  assert_norm (56007733665041789361753497513987510591721299036032530128556011168495316780048 < prime);
  56007733665041789361753497513987510591721299036032530128556011168495316780048

[@@"opaque_to_smt"]
let e11t : elem =
  assert_norm (43493064105923627382309315826169085771377261213540461738767557936059921748210 < prime);
  43493064105923627382309315826169085771377261213540461738767557936059921748210

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
  assert_norm (16097701074275810017366746124367400002217729733931900886785731604976207255321 < prime);
  16097701074275810017366746124367400002217729733931900886785731604976207255321

[@@"opaque_to_smt"]
let e12y : elem =
  assert_norm (46746043558516156302823940907474934567988950601114410109241077294930377326046 < prime);
  46746043558516156302823940907474934567988950601114410109241077294930377326046

[@@"opaque_to_smt"]
let e12t : elem =
  assert_norm (29564909742514976249328697001587551975819153137442781611480936070816454211947 < prime);
  29564909742514976249328697001587551975819153137442781611480936070816454211947

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
  assert_norm (15660450697042569228815718642864186748712671912160905715621523041979210123000 < prime);
  15660450697042569228815718642864186748712671912160905715621523041979210123000

[@@"opaque_to_smt"]
let e13y : elem =
  assert_norm (13238850225096250076353054986339586628569676144824916040173550721263082374576 < prime);
  13238850225096250076353054986339586628569676144824916040173550721263082374576

[@@"opaque_to_smt"]
let e13t : elem =
  assert_norm (53664160615630833833974672415145194779636975427848379002125073427195541700555 < prime);
  53664160615630833833974672415145194779636975427848379002125073427195541700555

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
  assert_norm (34596107221481471698104952204895248605738930239568844986874979118875719668676 < prime);
  34596107221481471698104952204895248605738930239568844986874979118875719668676

[@@"opaque_to_smt"]
let e14y : elem =
  assert_norm (34639871971964728338754175327004920292584999772041602087887656932501562480449 < prime);
  34639871971964728338754175327004920292584999772041602087887656932501562480449

[@@"opaque_to_smt"]
let e14t : elem =
  assert_norm (57362755044350300784043866216805398915211824406073895096158578201211264447707 < prime);
  57362755044350300784043866216805398915211824406073895096158578201211264447707

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
  assert_norm (19130711150077455363880604883372097405367460614627341371334126839732996501418 < prime);
  19130711150077455363880604883372097405367460614627341371334126839732996501418

[@@"opaque_to_smt"]
let e15y : elem =
  assert_norm (8884869138970675676268250483944966380228562936698039602120528374782801861274 < prime);
  8884869138970675676268250483944966380228562936698039602120528374782801861274

[@@"opaque_to_smt"]
let e15t : elem =
  assert_norm (38882282200986912724444878887037360847290948280489661621042256185896271447947 < prime);
  38882282200986912724444878887037360847290948280489661621042256185896271447947

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
