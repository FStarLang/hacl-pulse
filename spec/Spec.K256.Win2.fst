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

(** The sixteen multiples of [2^128 G], which is the third of the fixed-base
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
    context is not a context anything else terminates in.

    This is {!Spec.Ed25519.Win0} on a different curve. *)
module Spec.K256.Win2

module G = Spec.Group.Smul
module SM = Spec.K256.Smul
module Base = Spec.K256.Base
module Math = FStar.Math.Lemmas

open Spec.K256
open Spec.K256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d 2^128]-th multiple of [g]. *)
let n : nat = pow2 128

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

let e1 : proj_point = Base.q2

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul (1 * n) g))
  = Base.q2_ok ()

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : felem =
  assert_norm (34958276914040952500699582748843894357474821914666173518868387777824232206454 < prime);
  34958276914040952500699582748843894357474821914666173518868387777824232206454

[@@"opaque_to_smt"]
let e2y : felem =
  assert_norm (92814217969284136468346182500006122495187572087944979217112043851363214063646 < prime);
  92814217969284136468346182500006122495187572087944979217112043851363214063646

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
  assert_norm (25428668234201962184229241411366530728328042190169473198540501746374887868922 < prime);
  25428668234201962184229241411366530728328042190169473198540501746374887868922

[@@"opaque_to_smt"]
let e3y : felem =
  assert_norm (103415636398384512747388366987601943617426894933627999324871309752393592204626 < prime);
  103415636398384512747388366987601943617426894933627999324871309752393592204626

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
  assert_norm (53097865109432700015174734468294135156387483155245154627764610227234210717734 < prime);
  53097865109432700015174734468294135156387483155245154627764610227234210717734

[@@"opaque_to_smt"]
let e4y : felem =
  assert_norm (87675404738916139099090938273911264414778058285600924992648328889621933853939 < prime);
  87675404738916139099090938273911264414778058285600924992648328889621933853939

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
  assert_norm (33086248297739526934458931492661326379900806660982412712669701980170506904336 < prime);
  33086248297739526934458931492661326379900806660982412712669701980170506904336

[@@"opaque_to_smt"]
let e5y : felem =
  assert_norm (8692718135312534860350627675795223179574281447240636661273027551763383181008 < prime);
  8692718135312534860350627675795223179574281447240636661273027551763383181008

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
  assert_norm (48125892519771628779410019569828464756009467541678709596948188154899099696548 < prime);
  48125892519771628779410019569828464756009467541678709596948188154899099696548

[@@"opaque_to_smt"]
let e6y : felem =
  assert_norm (31029494791458167156216921981799219070008429485385569445931985694429479183044 < prime);
  31029494791458167156216921981799219070008429485385569445931985694429479183044

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
  assert_norm (102686215038121447173099356122339392703079051772879281028813598973792096169265 < prime);
  102686215038121447173099356122339392703079051772879281028813598973792096169265

[@@"opaque_to_smt"]
let e7y : felem =
  assert_norm (6637049801758052694260031564524980575071323026576836565057350028885442719300 < prime);
  6637049801758052694260031564524980575071323026576836565057350028885442719300

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
  assert_norm (14944996539173920287535718879437473208319387726469358424706553507748318061176 < prime);
  14944996539173920287535718879437473208319387726469358424706553507748318061176

[@@"opaque_to_smt"]
let e8y : felem =
  assert_norm (46613147883270029947538528514141525607759085017677379708440701301821571539505 < prime);
  46613147883270029947538528514141525607759085017677379708440701301821571539505

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
  assert_norm (26965730711836533784896736703167360916118156688701798809694509940035747395248 < prime);
  26965730711836533784896736703167360916118156688701798809694509940035747395248

[@@"opaque_to_smt"]
let e9y : felem =
  assert_norm (113522740395427968348262660971489373396619149122206223537180765179722516380810 < prime);
  113522740395427968348262660971489373396619149122206223537180765179722516380810

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
  assert_norm (55597007876455378703793426948860709512052340076283268295708172624740192621134 < prime);
  55597007876455378703793426948860709512052340076283268295708172624740192621134

[@@"opaque_to_smt"]
let e10y : felem =
  assert_norm (101181334457553172788276528205012805175653461768479902249797741867970569838129 < prime);
  101181334457553172788276528205012805175653461768479902249797741867970569838129

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
  assert_norm (84601367137830590751481041104108666606171453738850788689913869038213619277119 < prime);
  84601367137830590751481041104108666606171453738850788689913869038213619277119

[@@"opaque_to_smt"]
let e11y : felem =
  assert_norm (106027804441192285414202582502247328126206577290868190811057736818824136817013 < prime);
  106027804441192285414202582502247328126206577290868190811057736818824136817013

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
  assert_norm (38631854155932151852101536107882242268454920644678553277021052520123597685086 < prime);
  38631854155932151852101536107882242268454920644678553277021052520123597685086

[@@"opaque_to_smt"]
let e12y : felem =
  assert_norm (55418872951385267997041723840879373810830995230011393751576760382649268186608 < prime);
  55418872951385267997041723840879373810830995230011393751576760382649268186608

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
  assert_norm (54745830735720555968307177149044499109841803436505862043928212874325631536585 < prime);
  54745830735720555968307177149044499109841803436505862043928212874325631536585

[@@"opaque_to_smt"]
let e13y : felem =
  assert_norm (106144125390252346996944383170367660412628060374053462008508015554498530043845 < prime);
  106144125390252346996944383170367660412628060374053462008508015554498530043845

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
  assert_norm (43476133025998067296484786954986961816907342007605505933522699857008986988744 < prime);
  43476133025998067296484786954986961816907342007605505933522699857008986988744

[@@"opaque_to_smt"]
let e14y : felem =
  assert_norm (40923950968744058730957415695829536286242976689580849242509799556109620536663 < prime);
  40923950968744058730957415695829536286242976689580849242509799556109620536663

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
  assert_norm (104704252072756959575982561954256935687262144465597954318445311372513463289809 < prime);
  104704252072756959575982561954256935687262144465597954318445311372513463289809

[@@"opaque_to_smt"]
let e15y : felem =
  assert_norm (26600023855525489394721376223668930769380954305729080861466649031959312278601 < prime);
  26600023855525489394721376223668930769380954305729080861466649031959312278601

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
