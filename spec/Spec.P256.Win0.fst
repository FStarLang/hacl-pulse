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
(** The fixed-base window's first table: the sixteen multiples of
    [G].

    {!Spec.P256.Base} says what the base point is; this says what the
    table built from it holds, so that the table can be a constant in the
    binary rather than fifteen additions on every call.  The entries are
    affine, and each is settled by two [assert_norm]s -- that it is on the
    curve, and that it is the previous entry plus the base point -- and one
    application of {!Spec.P256.Smul.smul_add_congr}.

    This is {!Spec.K256.Win0} on a different curve. *)
module Spec.P256.Win0

module G = Spec.Group.Smul
module SM = Spec.P256.Smul
module Base = Spec.P256.Base
module Math = FStar.Math.Lemmas

open Spec.P256
open Spec.P256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d]-th multiple of [g]. *)
let n : nat = 1

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

let e1 : proj_point = g

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul (1 * n) g))
  = Base.g_ok ()

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : felem =
  assert_norm (56515219790691171413109057904011688695424810155802929973526481321309856242040 < prime);
  56515219790691171413109057904011688695424810155802929973526481321309856242040

[@@"opaque_to_smt"]
let e2y : felem =
  assert_norm (3377031843712258259223711451491452598088675519751548567112458094635497583569 < prime);
  3377031843712258259223711451491452598088675519751548567112458094635497583569

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
  assert_norm (42877656971275811310262564894490210024759287182177196162425349131675946712428 < prime);
  42877656971275811310262564894490210024759287182177196162425349131675946712428

[@@"opaque_to_smt"]
let e3y : felem =
  assert_norm (61154801112014214504178281461992570017247172004704277041681093927569603776562 < prime);
  61154801112014214504178281461992570017247172004704277041681093927569603776562

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
  assert_norm (102369864249653057322725350723741461599905180004905897298779971437827381725266 < prime);
  102369864249653057322725350723741461599905180004905897298779971437827381725266

[@@"opaque_to_smt"]
let e4y : felem =
  assert_norm (101744491111635190512325668403432589740384530506764148840112137220732283181254 < prime);
  101744491111635190512325668403432589740384530506764148840112137220732283181254

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
  assert_norm (36794669340896883012101473439538929759152396476648692591795318194054580155373 < prime);
  36794669340896883012101473439538929759152396476648692591795318194054580155373

[@@"opaque_to_smt"]
let e5y : felem =
  assert_norm (101659946828913883886577915207667153874746613498030835602133042203824767462820 < prime);
  101659946828913883886577915207667153874746613498030835602133042203824767462820

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
  assert_norm (79653159259317329199152975905021693207262715618295428672027927511489832980905 < prime);
  79653159259317329199152975905021693207262715618295428672027927511489832980905

[@@"opaque_to_smt"]
let e6y : felem =
  assert_norm (105099244361861367422779349381909628134794498213392835359532911141293690159074 < prime);
  105099244361861367422779349381909628134794498213392835359532911141293690159074

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
  assert_norm (64375483017717711348634889601793836329966447963510648681625681211348943876771 < prime);
  64375483017717711348634889601793836329966447963510648681625681211348943876771

[@@"opaque_to_smt"]
let e7y : felem =
  assert_norm (52431391916983504423217627849020916729601969409053901192561322805962577543348 < prime);
  52431391916983504423217627849020916729601969409053901192561322805962577543348

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
  assert_norm (44710890534849379681007195543719586089737754824560621976448707498688874787731 < prime);
  44710890534849379681007195543719586089737754824560621976448707498688874787731

[@@"opaque_to_smt"]
let e8y : felem =
  assert_norm (78410552107786285403689301656392479612049391334024095564584156230482213311870 < prime);
  78410552107786285403689301656392479612049391334024095564584156230482213311870

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
  assert_norm (106026447472237217594103756757091873528548576106367144586170196380839010672352 < prime);
  106026447472237217594103756757091873528548576106367144586170196380839010672352

[@@"opaque_to_smt"]
let e9y : felem =
  assert_norm (19066521425813101412078385704618669688199787690556935461623958781864528857338 < prime);
  19066521425813101412078385704618669688199787690556935461623958781864528857338

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
  assert_norm (93611846365601674425599200647886473617443872040541410036779615417472400060991 < prime);
  93611846365601674425599200647886473617443872040541410036779615417472400060991

[@@"opaque_to_smt"]
let e10y : felem =
  assert_norm (61299672808462629900136024686264045542397545919962042795596947287593974695795 < prime);
  61299672808462629900136024686264045542397545919962042795596947287593974695795

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
  assert_norm (28412803729898893058558238221310261427084375743576167377786533380249859400145 < prime);
  28412803729898893058558238221310261427084375743576167377786533380249859400145

[@@"opaque_to_smt"]
let e11y : felem =
  assert_norm (65403602826180996396520286939226973026599920614829401631985882360676038096704 < prime);
  65403602826180996396520286939226973026599920614829401631985882360676038096704

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
  assert_norm (52521004185641536627266600536804816931535329133355539962020980193802383057860 < prime);
  52521004185641536627266600536804816931535329133355539962020980193802383057860

[@@"opaque_to_smt"]
let e12y : felem =
  assert_norm (3365321999886721389269937144276711091585627196865605815969312301872807444947 < prime);
  3365321999886721389269937144276711091585627196865605815969312301872807444947

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
  assert_norm (10623191994993397449217730442198332685419647040822028787120372345201232391169 < prime);
  10623191994993397449217730442198332685419647040822028787120372345201232391169

[@@"opaque_to_smt"]
let e13y : felem =
  assert_norm (45109985299617300571846506882481132822837374452436097494820998411881657384920 < prime);
  45109985299617300571846506882481132822837374452436097494820998411881657384920

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
  assert_norm (38403262968984431726992065809397801166868659563255596809893498026441953153547 < prime);
  38403262968984431726992065809397801166868659563255596809893498026441953153547

[@@"opaque_to_smt"]
let e14y : felem =
  assert_norm (111088643870609220449345638248812642769306967281233677460251511569904126964597 < prime);
  111088643870609220449345638248812642769306967281233677460251511569904126964597

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
  assert_norm (108677532895904936863904823330600106055145041255062888673713681538132314135903 < prime);
  108677532895904936863904823330600106055145041255062888673713681538132314135903

[@@"opaque_to_smt"]
let e15y : felem =
  assert_norm (82195926338128401624329850334826772981689991100719104119047727086732126146358 < prime);
  82195926338128401624329850334826772981689991100719104119047727086732126146358

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
