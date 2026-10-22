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
(** The fixed-base window's second table: the sixteen multiples of
    [2^64 G].

    {!Spec.P256.Base} says what the base point is; this says what the
    table built from it holds, so that the table can be a constant in the
    binary rather than fifteen additions on every call.  The entries are
    affine, and each is settled by two [assert_norm]s -- that it is on the
    curve, and that it is the previous entry plus the base point -- and one
    application of {!Spec.P256.Smul.smul_add_congr}.

    This is {!Spec.K256.Win1} on a different curve. *)
module Spec.P256.Win1

module G = Spec.Group.Smul
module SM = Spec.P256.Smul
module Base = Spec.P256.Base
module Math = FStar.Math.Lemmas

open Spec.P256
open Spec.P256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d 2^64]-th multiple of [g]. *)
let n : nat = pow2 64

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

let e1 : proj_point = Base.q1

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul (1 * n) g))
  = Base.q1_ok ()

(** [e1_ok] for [n] rather than [1 n], which is what every step of the chain
    needs.  Z3 does not reliably get from one to the other with a point's
    coordinates in context. *)
let e1_ok_n (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul n g))
  = Base.q1_ok ()

let double (_: unit) : Lemma (n + n == 2 * n) = ()

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : felem =
  assert_norm (1403810242890032554906673779515655599274985018625350083539101873235480762293 < prime);
  1403810242890032554906673779515655599274985018625350083539101873235480762293

[@@"opaque_to_smt"]
let e2y : felem =
  assert_norm (61617330936628764714622260330634195070720938392958707125897027654601041724413 < prime);
  61617330936628764714622260330634195070720938392958707125897027654601041724413

let e2 : proj_point = (e2x, e2y, fone)

let e2_ok (_: unit)
  : Lemma (on_curve e2 /\ peq e2 (SM.smul (2 * n) g))
  = assert_norm (on_curve e2);
    assert_norm (peq e2 (point_add e1 e1));
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr n n g e1 e1;
    double ();
    SM.smul_ok (2 * n) g;
    peq_trans e2 (point_add e1 e1) (SM.smul (2 * n) g)

[@@"opaque_to_smt"]
let e3x : felem =
  assert_norm (60473435497312592592524991715327725357125756095698969950324109024595597839852 < prime);
  60473435497312592592524991715327725357125756095698969950324109024595597839852

[@@"opaque_to_smt"]
let e3y : felem =
  assert_norm (111401747310810620924422534071530345651107380198228147864621110719293207869471 < prime);
  111401747310810620924422534071530345651107380198228147864621110719293207869471

let e3 : proj_point = (e3x, e3y, fone)

let e3_ok (_: unit)
  : Lemma (on_curve e3 /\ peq e3 (SM.smul (3 * n) g))
  = assert_norm (on_curve e3);
    assert_norm (peq e3 (point_add e2 e1));
    e2_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (2 * n) n g e2 e1;
    step 2;
    SM.smul_ok (3 * n) g;
    peq_trans e3 (point_add e2 e1) (SM.smul (3 * n) g)

[@@"opaque_to_smt"]
let e4x : felem =
  assert_norm (75575531629274745007335764177410035508313646274703454097862075897420372976418 < prime);
  75575531629274745007335764177410035508313646274703454097862075897420372976418

[@@"opaque_to_smt"]
let e4y : felem =
  assert_norm (21955907770975270990108027390670941864966904856959906600160357358861987348457 < prime);
  21955907770975270990108027390670941864966904856959906600160357358861987348457

let e4 : proj_point = (e4x, e4y, fone)

let e4_ok (_: unit)
  : Lemma (on_curve e4 /\ peq e4 (SM.smul (4 * n) g))
  = assert_norm (on_curve e4);
    assert_norm (peq e4 (point_add e3 e1));
    e3_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (3 * n) n g e3 e1;
    step 3;
    SM.smul_ok (4 * n) g;
    peq_trans e4 (point_add e3 e1) (SM.smul (4 * n) g)

[@@"opaque_to_smt"]
let e5x : felem =
  assert_norm (7708777650782902633007262051276824707288637194502561338083280096541591187504 < prime);
  7708777650782902633007262051276824707288637194502561338083280096541591187504

[@@"opaque_to_smt"]
let e5y : felem =
  assert_norm (59823975132316221763674026123039736069757084059793129648044915811654039600186 < prime);
  59823975132316221763674026123039736069757084059793129648044915811654039600186

let e5 : proj_point = (e5x, e5y, fone)

let e5_ok (_: unit)
  : Lemma (on_curve e5 /\ peq e5 (SM.smul (5 * n) g))
  = assert_norm (on_curve e5);
    assert_norm (peq e5 (point_add e4 e1));
    e4_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (4 * n) n g e4 e1;
    step 4;
    SM.smul_ok (5 * n) g;
    peq_trans e5 (point_add e4 e1) (SM.smul (5 * n) g)

[@@"opaque_to_smt"]
let e6x : felem =
  assert_norm (27338901838627493488565759030399108681837356224136687130142329231925841182752 < prime);
  27338901838627493488565759030399108681837356224136687130142329231925841182752

[@@"opaque_to_smt"]
let e6y : felem =
  assert_norm (57459670637887324399022615836894581609375682238106613034896504576559889258069 < prime);
  57459670637887324399022615836894581609375682238106613034896504576559889258069

let e6 : proj_point = (e6x, e6y, fone)

let e6_ok (_: unit)
  : Lemma (on_curve e6 /\ peq e6 (SM.smul (6 * n) g))
  = assert_norm (on_curve e6);
    assert_norm (peq e6 (point_add e5 e1));
    e5_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (5 * n) n g e5 e1;
    step 5;
    SM.smul_ok (6 * n) g;
    peq_trans e6 (point_add e5 e1) (SM.smul (6 * n) g)

[@@"opaque_to_smt"]
let e7x : felem =
  assert_norm (11068070200049197394052243630400658803491612707623465304327140927465461346056 < prime);
  11068070200049197394052243630400658803491612707623465304327140927465461346056

[@@"opaque_to_smt"]
let e7y : felem =
  assert_norm (63986238749487320301906623642417499885098023516489380698410407047318619703699 < prime);
  63986238749487320301906623642417499885098023516489380698410407047318619703699

let e7 : proj_point = (e7x, e7y, fone)

let e7_ok (_: unit)
  : Lemma (on_curve e7 /\ peq e7 (SM.smul (7 * n) g))
  = assert_norm (on_curve e7);
    assert_norm (peq e7 (point_add e6 e1));
    e6_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (6 * n) n g e6 e1;
    step 6;
    SM.smul_ok (7 * n) g;
    peq_trans e7 (point_add e6 e1) (SM.smul (7 * n) g)

[@@"opaque_to_smt"]
let e8x : felem =
  assert_norm (12664176886671006937092610814702120170909999477704514076958036156844397994624 < prime);
  12664176886671006937092610814702120170909999477704514076958036156844397994624

[@@"opaque_to_smt"]
let e8y : felem =
  assert_norm (18775773912656001976453433019659509194737985910615436289323902351500805640801 < prime);
  18775773912656001976453433019659509194737985910615436289323902351500805640801

let e8 : proj_point = (e8x, e8y, fone)

let e8_ok (_: unit)
  : Lemma (on_curve e8 /\ peq e8 (SM.smul (8 * n) g))
  = assert_norm (on_curve e8);
    assert_norm (peq e8 (point_add e7 e1));
    e7_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (7 * n) n g e7 e1;
    step 7;
    SM.smul_ok (8 * n) g;
    peq_trans e8 (point_add e7 e1) (SM.smul (8 * n) g)

[@@"opaque_to_smt"]
let e9x : felem =
  assert_norm (40091484486856408830941681030915055054805795507119489963777728949457324584321 < prime);
  40091484486856408830941681030915055054805795507119489963777728949457324584321

[@@"opaque_to_smt"]
let e9y : felem =
  assert_norm (3016703443469711351361248557723072123973501006397350601588689295370194294164 < prime);
  3016703443469711351361248557723072123973501006397350601588689295370194294164

let e9 : proj_point = (e9x, e9y, fone)

let e9_ok (_: unit)
  : Lemma (on_curve e9 /\ peq e9 (SM.smul (9 * n) g))
  = assert_norm (on_curve e9);
    assert_norm (peq e9 (point_add e8 e1));
    e8_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (8 * n) n g e8 e1;
    step 8;
    SM.smul_ok (9 * n) g;
    peq_trans e9 (point_add e8 e1) (SM.smul (9 * n) g)

[@@"opaque_to_smt"]
let e10x : felem =
  assert_norm (98448958124189804686765260954111755389952415390572340668108924587228784774260 < prime);
  98448958124189804686765260954111755389952415390572340668108924587228784774260

[@@"opaque_to_smt"]
let e10y : felem =
  assert_norm (32970171112413497373344419410163909685773376033892105889180492141242680051857 < prime);
  32970171112413497373344419410163909685773376033892105889180492141242680051857

let e10 : proj_point = (e10x, e10y, fone)

let e10_ok (_: unit)
  : Lemma (on_curve e10 /\ peq e10 (SM.smul (10 * n) g))
  = assert_norm (on_curve e10);
    assert_norm (peq e10 (point_add e9 e1));
    e9_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (9 * n) n g e9 e1;
    step 9;
    SM.smul_ok (10 * n) g;
    peq_trans e10 (point_add e9 e1) (SM.smul (10 * n) g)

[@@"opaque_to_smt"]
let e11x : felem =
  assert_norm (13993655561862634954656937319023025182277694409756645987948739214545419314563 < prime);
  13993655561862634954656937319023025182277694409756645987948739214545419314563

[@@"opaque_to_smt"]
let e11y : felem =
  assert_norm (40376808338783394121910433405048919317108317864020742657382520865564242417582 < prime);
  40376808338783394121910433405048919317108317864020742657382520865564242417582

let e11 : proj_point = (e11x, e11y, fone)

let e11_ok (_: unit)
  : Lemma (on_curve e11 /\ peq e11 (SM.smul (11 * n) g))
  = assert_norm (on_curve e11);
    assert_norm (peq e11 (point_add e10 e1));
    e10_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (10 * n) n g e10 e1;
    step 10;
    SM.smul_ok (11 * n) g;
    peq_trans e11 (point_add e10 e1) (SM.smul (11 * n) g)

[@@"opaque_to_smt"]
let e12x : felem =
  assert_norm (46436825433609964390483093431545434229943688231034893237754213978463533115838 < prime);
  46436825433609964390483093431545434229943688231034893237754213978463533115838

[@@"opaque_to_smt"]
let e12y : felem =
  assert_norm (7587492663664152951480972692587902992206250853147509120230771775685823388313 < prime);
  7587492663664152951480972692587902992206250853147509120230771775685823388313

let e12 : proj_point = (e12x, e12y, fone)

let e12_ok (_: unit)
  : Lemma (on_curve e12 /\ peq e12 (SM.smul (12 * n) g))
  = assert_norm (on_curve e12);
    assert_norm (peq e12 (point_add e11 e1));
    e11_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (11 * n) n g e11 e1;
    step 11;
    SM.smul_ok (12 * n) g;
    peq_trans e12 (point_add e11 e1) (SM.smul (12 * n) g)

[@@"opaque_to_smt"]
let e13x : felem =
  assert_norm (35412041887015401996901336309631860799368561008662388956072714619798029440399 < prime);
  35412041887015401996901336309631860799368561008662388956072714619798029440399

[@@"opaque_to_smt"]
let e13y : felem =
  assert_norm (16941664009689718571036802852294908448020691345400409703564697257940925771658 < prime);
  16941664009689718571036802852294908448020691345400409703564697257940925771658

let e13 : proj_point = (e13x, e13y, fone)

let e13_ok (_: unit)
  : Lemma (on_curve e13 /\ peq e13 (SM.smul (13 * n) g))
  = assert_norm (on_curve e13);
    assert_norm (peq e13 (point_add e12 e1));
    e12_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (12 * n) n g e12 e1;
    step 12;
    SM.smul_ok (13 * n) g;
    peq_trans e13 (point_add e12 e1) (SM.smul (13 * n) g)

[@@"opaque_to_smt"]
let e14x : felem =
  assert_norm (102726705849139632724841433199754712059447851536802811059374850766785769322687 < prime);
  102726705849139632724841433199754712059447851536802811059374850766785769322687

[@@"opaque_to_smt"]
let e14y : felem =
  assert_norm (112475938433074430267545019167310037797417588897666269708803942881210920399216 < prime);
  112475938433074430267545019167310037797417588897666269708803942881210920399216

let e14 : proj_point = (e14x, e14y, fone)

let e14_ok (_: unit)
  : Lemma (on_curve e14 /\ peq e14 (SM.smul (14 * n) g))
  = assert_norm (on_curve e14);
    assert_norm (peq e14 (point_add e13 e1));
    e13_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (13 * n) n g e13 e1;
    step 13;
    SM.smul_ok (14 * n) g;
    peq_trans e14 (point_add e13 e1) (SM.smul (14 * n) g)

[@@"opaque_to_smt"]
let e15x : felem =
  assert_norm (111534720007738963967453878781936997977361096743077936920156643355160611085749 < prime);
  111534720007738963967453878781936997977361096743077936920156643355160611085749

[@@"opaque_to_smt"]
let e15y : felem =
  assert_norm (84154725751269074505436890045395227950677294757918332516143851972170777782328 < prime);
  84154725751269074505436890045395227950677294757918332516143851972170777782328

let e15 : proj_point = (e15x, e15y, fone)

let e15_ok (_: unit)
  : Lemma (on_curve e15 /\ peq e15 (SM.smul (15 * n) g))
  = assert_norm (on_curve e15);
    assert_norm (peq e15 (point_add e14 e1));
    e14_ok ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (14 * n) n g e14 e1;
    step 14;
    SM.smul_ok (15 * n) g;
    peq_trans e15 (point_add e14 e1) (SM.smul (15 * n) g)

#pop-options
