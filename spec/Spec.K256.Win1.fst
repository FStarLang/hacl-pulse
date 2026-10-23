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

(** The sixteen multiples of [2^64 G], which is the second of the fixed-base
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
module Spec.K256.Win1

module G = Spec.Group.Smul
module SM = Spec.K256.Smul
module Base = Spec.K256.Base
module Math = FStar.Math.Lemmas

open Spec.K256
open Spec.K256.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d 2^64]-th multiple of [g]. *)
let n : nat = pow2 64

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

let e1 : proj_point = Base.q1

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul (1 * n) g))
  = Base.q1_ok ()

(** The same, with the multiple written [n] as the chain below uses it. *)
let e1_ok_n (_: unit)
  : Lemma (on_curve e1 /\ peq e1 (SM.smul n g))
  = e1_ok ();
    assert (1 * n == n)

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : felem =
  assert_norm (63843472757015161619640823952764524318291830965488059905636263767209969312866 < prime);
  63843472757015161619640823952764524318291830965488059905636263767209969312866

[@@"opaque_to_smt"]
let e2y : felem =
  assert_norm (106712674239183055714747170770237410600716249238757184591428740534726428083980 < prime);
  106712674239183055714747170770237410600716249238757184591428740534726428083980

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
  assert_norm (54607389741061642657371323268129044001813125251607218919816798278797898724505 < prime);
  54607389741061642657371323268129044001813125251607218919816798278797898724505

[@@"opaque_to_smt"]
let e3y : felem =
  assert_norm (78384160646254247810484869804956964085575263908905713945630016471619164215293 < prime);
  78384160646254247810484869804956964085575263908905713945630016471619164215293

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
  assert_norm (8241903038354912941099822707985246210294044712473769251710198461880050574899 < prime);
  8241903038354912941099822707985246210294044712473769251710198461880050574899

[@@"opaque_to_smt"]
let e4y : felem =
  assert_norm (62697784033925076403474224442689974679135179320309080987220280194454804723717 < prime);
  62697784033925076403474224442689974679135179320309080987220280194454804723717

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
  assert_norm (50406283761918851715737480243526773721571954600618067989106304614101919640806 < prime);
  50406283761918851715737480243526773721571954600618067989106304614101919640806

[@@"opaque_to_smt"]
let e5y : felem =
  assert_norm (54783813841179121941300430723996820776706436721463465897211553238110674539998 < prime);
  54783813841179121941300430723996820776706436721463465897211553238110674539998

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
  assert_norm (10743222706764111638505481352462913519517002169526285806519999741685800981369 < prime);
  10743222706764111638505481352462913519517002169526285806519999741685800981369

[@@"opaque_to_smt"]
let e6y : felem =
  assert_norm (98154966002157958217367539162400668710605290356404337509281752649653398588709 < prime);
  98154966002157958217367539162400668710605290356404337509281752649653398588709

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
  assert_norm (101928728709625065799132077417462976690419417160896068084753138409157379889984 < prime);
  101928728709625065799132077417462976690419417160896068084753138409157379889984

[@@"opaque_to_smt"]
let e7y : felem =
  assert_norm (54820641198095574872636280264107475271035517492645931279356128069097465287590 < prime);
  54820641198095574872636280264107475271035517492645931279356128069097465287590

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
  assert_norm (17692067919141883746474430216313318912323253047795385992074267436472656099942 < prime);
  17692067919141883746474430216313318912323253047795385992074267436472656099942

[@@"opaque_to_smt"]
let e8y : felem =
  assert_norm (42168706312448760835164198288963124085049274787903511949048046806853155067687 < prime);
  42168706312448760835164198288963124085049274787903511949048046806853155067687

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
  assert_norm (84601969681168457265008103515305184678816137380777756394024192676336104377406 < prime);
  84601969681168457265008103515305184678816137380777756394024192676336104377406

[@@"opaque_to_smt"]
let e9y : felem =
  assert_norm (29131583536456764559580259437949590196915613820108904969144286795366739040821 < prime);
  29131583536456764559580259437949590196915613820108904969144286795366739040821

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
  assert_norm (77873422769881137182786752733915073314346773341582340022783338979916014756791 < prime);
  77873422769881137182786752733915073314346773341582340022783338979916014756791

[@@"opaque_to_smt"]
let e10y : felem =
  assert_norm (53606599048177863696033810900574782758112346875769975054059677917073061519526 < prime);
  53606599048177863696033810900574782758112346875769975054059677917073061519526

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
  assert_norm (99668293836163455957618421209977847218149550704829055972289895633850560492262 < prime);
  99668293836163455957618421209977847218149550704829055972289895633850560492262

[@@"opaque_to_smt"]
let e11y : felem =
  assert_norm (33901658607340517440296858455679574291918646400653238008304662046244621425081 < prime);
  33901658607340517440296858455679574291918646400653238008304662046244621425081

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
  assert_norm (61583647755996023436124144983914864801842838823383906965674515701942719450542 < prime);
  61583647755996023436124144983914864801842838823383906965674515701942719450542

[@@"opaque_to_smt"]
let e12y : felem =
  assert_norm (97292961154111606721201828893124924376755031992293068055704247673299729807321 < prime);
  97292961154111606721201828893124924376755031992293068055704247673299729807321

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
  assert_norm (9693098566605345120490949986210028913891998342387486223750309279061999151051 < prime);
  9693098566605345120490949986210028913891998342387486223750309279061999151051

[@@"opaque_to_smt"]
let e13y : felem =
  assert_norm (48737686882793418220967746673259445790885182240936749335528060831927380544055 < prime);
  48737686882793418220967746673259445790885182240936749335528060831927380544055

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
  assert_norm (9824063440844129147294930472062832953383960664852480236407149114638473962511 < prime);
  9824063440844129147294930472062832953383960664852480236407149114638473962511

[@@"opaque_to_smt"]
let e14y : felem =
  assert_norm (54470031874182377020884542801165300662442697118379307861645205500782015082570 < prime);
  54470031874182377020884542801165300662442697118379307861645205500782015082570

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
  assert_norm (30039470051780808856992151963231995460930709987090271017478012900675981693898 < prime);
  30039470051780808856992151963231995460930709987090271017478012900675981693898

[@@"opaque_to_smt"]
let e15y : felem =
  assert_norm (107274313501645546690240416406649680740234305956385566947878456150586709037927 < prime);
  107274313501645546690240416406649680740234305956385566947878456150586709037927

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
