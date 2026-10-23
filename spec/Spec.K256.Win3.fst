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

(** The sixteen multiples of [2^192 G], which is the fourth of the fixed-base
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
module Spec.K256.Win3

module G = Spec.Group.Smul
module SM = Spec.K256.Smul
module Base = Spec.K256.Base
module Math = FStar.Math.Lemmas

open Spec.K256
open Spec.K256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d 2^192]-th multiple of [g]. *)
let n : nat = pow2 192

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

let e1 : proj_point = Base.q3

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul (1 * n) g))
  = Base.q3_ok ()

(** The same, with the multiple written [n] as the chain below uses it. *)
let e1_ok_n (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul n g))
  = e1_ok ();
    assert (1 * n == n)

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : felem =
  assert_norm (26622173145108500381473837459513401868318671376325266944487505521378511663272 < prime);
  26622173145108500381473837459513401868318671376325266944487505521378511663272

[@@"opaque_to_smt"]
let e2y : felem =
  assert_norm (25015334278771650323507319424566501275290669267697587988960111333611631525338 < prime);
  25015334278771650323507319424566501275290669267697587988960111333611631525338

let e2 : proj_point = (e2x, e2y, fone)

let e2_ok (_: unit)
  : Lemma (on_curve e2 /\ peq e2 (SM.smul (2 * n) g))
  = assert_norm (on_curve e2);
    assert_norm (peq e2 (point_add e1 e1));
    e1_ok_n ();
    e1_ok_n ();
    g_on_curve ();
    SM.smul_add_congr (1 * n) n g e1 e1;
    step 1;
    SM.smul_ok (2 * n) g;
    peq_trans e2 (point_add e1 e1) (SM.smul (2 * n) g)

[@@"opaque_to_smt"]
let e3x : felem =
  assert_norm (34126029279385212794256078005192016817950599148547558828153074850437339678477 < prime);
  34126029279385212794256078005192016817950599148547558828153074850437339678477

[@@"opaque_to_smt"]
let e3y : felem =
  assert_norm (40535207616763615445334633616848698938874560190478572057459037628564081858432 < prime);
  40535207616763615445334633616848698938874560190478572057459037628564081858432

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
  assert_norm (8421370599800668602652103103676786751239058426611888163586601660098353727225 < prime);
  8421370599800668602652103103676786751239058426611888163586601660098353727225

[@@"opaque_to_smt"]
let e4y : felem =
  assert_norm (29567823868173186762768009528067406508648153893486721194867955006028793890909 < prime);
  29567823868173186762768009528067406508648153893486721194867955006028793890909

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
  assert_norm (76887138232176023528961824138070621094527136794395443494385848818423455439132 < prime);
  76887138232176023528961824138070621094527136794395443494385848818423455439132

[@@"opaque_to_smt"]
let e5y : felem =
  assert_norm (70640141513165939613750861833902344224656889919760435956423610093624952275676 < prime);
  70640141513165939613750861833902344224656889919760435956423610093624952275676

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
  assert_norm (77093071474622673584213674950479259826192820954289885091496063438507468198636 < prime);
  77093071474622673584213674950479259826192820954289885091496063438507468198636

[@@"opaque_to_smt"]
let e6y : felem =
  assert_norm (89814029647215600683432897311309534380900900524058890115039828672310772193656 < prime);
  89814029647215600683432897311309534380900900524058890115039828672310772193656

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
  assert_norm (91027971024946132080753945053473842846822601913448659826526139060631031417689 < prime);
  91027971024946132080753945053473842846822601913448659826526139060631031417689

[@@"opaque_to_smt"]
let e7y : felem =
  assert_norm (26165474999802344120686641115629148062893568192976491390127795158043456795387 < prime);
  26165474999802344120686641115629148062893568192976491390127795158043456795387

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
  assert_norm (43457843735276724612075728233726406612249501219998543099634755887188281768154 < prime);
  43457843735276724612075728233726406612249501219998543099634755887188281768154

[@@"opaque_to_smt"]
let e8y : felem =
  assert_norm (63192765102271790090487849294643355539231117908172846139915612801187217034173 < prime);
  63192765102271790090487849294643355539231117908172846139915612801187217034173

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
  assert_norm (14256216991277326476188515598059036355385564491440040760535275304126838944562 < prime);
  14256216991277326476188515598059036355385564491440040760535275304126838944562

[@@"opaque_to_smt"]
let e9y : felem =
  assert_norm (107852631011885344787477492443348359649212419674940583445530420421457340847406 < prime);
  107852631011885344787477492443348359649212419674940583445530420421457340847406

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
  assert_norm (28020098683150752368891219579767439216616467949968395582981395176707677694923 < prime);
  28020098683150752368891219579767439216616467949968395582981395176707677694923

[@@"opaque_to_smt"]
let e10y : felem =
  assert_norm (99732676372475944025225621882264665419852998816972679641956034299872551963103 < prime);
  99732676372475944025225621882264665419852998816972679641956034299872551963103

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
  assert_norm (6819812508650761449107353555470128357725229525740112440401844776355752814990 < prime);
  6819812508650761449107353555470128357725229525740112440401844776355752814990

[@@"opaque_to_smt"]
let e11y : felem =
  assert_norm (78626695497138609442260027981297634950672392962723882829388586695082576996199 < prime);
  78626695497138609442260027981297634950672392962723882829388586695082576996199

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
  assert_norm (34193938424810668442547326862401260093498711266114513507501074549719035974364 < prime);
  34193938424810668442547326862401260093498711266114513507501074549719035974364

[@@"opaque_to_smt"]
let e12y : felem =
  assert_norm (102744733146548476076162338741335049999200029391847730170952583322218426621094 < prime);
  102744733146548476076162338741335049999200029391847730170952583322218426621094

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
  assert_norm (100359685336710082794626954235097416506517867164167411211797312716884346772331 < prime);
  100359685336710082794626954235097416506517867164167411211797312716884346772331

[@@"opaque_to_smt"]
let e13y : felem =
  assert_norm (41238179218653649130693378312885173674351775893287407364135085296439995864080 < prime);
  41238179218653649130693378312885173674351775893287407364135085296439995864080

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
  assert_norm (59599309982011045964365287187449322698987936812917948516665771243958850305771 < prime);
  59599309982011045964365287187449322698987936812917948516665771243958850305771

[@@"opaque_to_smt"]
let e14y : felem =
  assert_norm (18699204683866996931516569803713783513364965991789947435810080763924613233489 < prime);
  18699204683866996931516569803713783513364965991789947435810080763924613233489

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
  assert_norm (43271859630404386633156385771794735476352936395592067120352888086729645799065 < prime);
  43271859630404386633156385771794735476352936395592067120352888086729645799065

[@@"opaque_to_smt"]
let e15y : felem =
  assert_norm (20629667954634819581477631650146691647841927324880342488285729944395514823594 < prime);
  20629667954634819581477631650146691647841927324880342488285729944395514823594

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
