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

(** The sixteen multiples of [2^128 g], which is the third of the fixed-base
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
module Spec.Ed25519.Win2

module G = Spec.Group.Smul
module SM = Spec.Ed25519.Smul
module Base = Spec.Ed25519.Base
module Math = FStar.Math.Lemmas

open Spec.Curve25519
open Spec.Ed25519
open Spec.Ed25519.Group

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** The table's scale: entry [d] is the [d pow2 128]-th multiple of [g]. *)
let n : nat = pow2 128

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

let e1 : ext_point = Base.b2

let e1_ok (_: unit)
  : Lemma (on_curve e1 /\ point_equal e1 (SM.smul (1 * n) g))
  = Base.b2_ok ()

(** The same, with the multiple written [n] as the chain below uses it. *)
let e1_ok_n (_: unit)
  : Lemma (on_curve e1 /\ point_equal e1 (SM.smul n g))
  = e1_ok ();
    assert (1 * n == n)

(** {2 The chain} *)

[@@"opaque_to_smt"]
let e2x : elem =
  assert_norm (54468161356533199495368251232949756902362822455729558615345521844455465083013 < prime);
  54468161356533199495368251232949756902362822455729558615345521844455465083013

[@@"opaque_to_smt"]
let e2y : elem =
  assert_norm (45786733715774964106052639328220628713810319567465451448853998335128869152566 < prime);
  45786733715774964106052639328220628713810319567465451448853998335128869152566

[@@"opaque_to_smt"]
let e2t : elem =
  assert_norm (8493667445341245648361292062270796651158721786810104163590154947632220300488 < prime);
  8493667445341245648361292062270796651158721786810104163590154947632220300488

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
  assert_norm (4412746692151443821523268063185684387212441150931176163599595845239453239239 < prime);
  4412746692151443821523268063185684387212441150931176163599595845239453239239

[@@"opaque_to_smt"]
let e3y : elem =
  assert_norm (43972740745976811175176257864391345069695511571436714679879334460061323560495 < prime);
  43972740745976811175176257864391345069695511571436714679879334460061323560495

[@@"opaque_to_smt"]
let e3t : elem =
  assert_norm (39429793009095178565915118939096967879375587605173578703268984407783849784162 < prime);
  39429793009095178565915118939096967879375587605173578703268984407783849784162

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
  assert_norm (15376680214472594388297076775801069075796453668683777673974256464718742858259 < prime);
  15376680214472594388297076775801069075796453668683777673974256464718742858259

[@@"opaque_to_smt"]
let e4y : elem =
  assert_norm (36205286238381305703459570197756276983310200040700818089343846617668540962560 < prime);
  36205286238381305703459570197756276983310200040700818089343846617668540962560

[@@"opaque_to_smt"]
let e4t : elem =
  assert_norm (11543757158601053623050530508501701193774440978633598706901758191197578559992 < prime);
  11543757158601053623050530508501701193774440978633598706901758191197578559992

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
  assert_norm (33552643783428748950402828607752795289608997377287090122096841711038568943383 < prime);
  33552643783428748950402828607752795289608997377287090122096841711038568943383

[@@"opaque_to_smt"]
let e5y : elem =
  assert_norm (48961350984589746204023233509239121202812045655202442846113442238752062992324 < prime);
  48961350984589746204023233509239121202812045655202442846113442238752062992324

[@@"opaque_to_smt"]
let e5t : elem =
  assert_norm (20747607484505391756240397195583583804917874632534122868199174546614822467192 < prime);
  20747607484505391756240397195583583804917874632534122868199174546614822467192

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
  assert_norm (42399442938455531623261734790075802706903319205440937767137281092036923765860 < prime);
  42399442938455531623261734790075802706903319205440937767137281092036923765860

[@@"opaque_to_smt"]
let e6y : elem =
  assert_norm (39333490461136029727899638725695807748678920801781508139753544244281903045495 < prime);
  39333490461136029727899638725695807748678920801781508139753544244281903045495

[@@"opaque_to_smt"]
let e6t : elem =
  assert_norm (39925368598239139555428165036531959804003303529316568234937157052373320803689 < prime);
  39925368598239139555428165036531959804003303529316568234937157052373320803689

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
  assert_norm (34020654150955289924352052102572547756238841423233570276978675036237125736069 < prime);
  34020654150955289924352052102572547756238841423233570276978675036237125736069

[@@"opaque_to_smt"]
let e7y : elem =
  assert_norm (38084804761088375484846448810418007531017181516754376621904739824085009807392 < prime);
  38084804761088375484846448810418007531017181516754376621904739824085009807392

[@@"opaque_to_smt"]
let e7t : elem =
  assert_norm (13168179154942715776557344185809233775662045677124711417245584554272960624104 < prime);
  13168179154942715776557344185809233775662045677124711417245584554272960624104

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
  assert_norm (54274963091825622044577791478482498515145581213046587691569496957317047301087 < prime);
  54274963091825622044577791478482498515145581213046587691569496957317047301087

[@@"opaque_to_smt"]
let e8y : elem =
  assert_norm (27285522798141530128504086038099622016723351071236115824010547114802360418886 < prime);
  27285522798141530128504086038099622016723351071236115824010547114802360418886

[@@"opaque_to_smt"]
let e8t : elem =
  assert_norm (17023168053045613828573237880834348116297780257693827116166718009290689522988 < prime);
  17023168053045613828573237880834348116297780257693827116166718009290689522988

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
  assert_norm (28027671521824585639565556962361942879177032460226106994547616916734338780704 < prime);
  28027671521824585639565556962361942879177032460226106994547616916734338780704

[@@"opaque_to_smt"]
let e9y : elem =
  assert_norm (56905778350264350980852911115294243427463271771279934635413881828004627872408 < prime);
  56905778350264350980852911115294243427463271771279934635413881828004627872408

[@@"opaque_to_smt"]
let e9t : elem =
  assert_norm (32009291873999293585910564495502172651246355590549956171023318544587760396725 < prime);
  32009291873999293585910564495502172651246355590549956171023318544587760396725

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
  assert_norm (4057470565985525529319509897905014251856080445026885253186795750419024262832 < prime);
  4057470565985525529319509897905014251856080445026885253186795750419024262832

[@@"opaque_to_smt"]
let e10y : elem =
  assert_norm (8127557164291997904758589263654886784031946313369332131861444830794939156612 < prime);
  8127557164291997904758589263654886784031946313369332131861444830794939156612

[@@"opaque_to_smt"]
let e10t : elem =
  assert_norm (21955171261691190446610704877626516613209547245565340928469526823147411890358 < prime);
  21955171261691190446610704877626516613209547245565340928469526823147411890358

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
  assert_norm (34801223990698370535329863300556394101860826629410823252193897829330789286668 < prime);
  34801223990698370535329863300556394101860826629410823252193897829330789286668

[@@"opaque_to_smt"]
let e11y : elem =
  assert_norm (166006844256722794136677593242087472511918765458138001691392985479370479413 < prime);
  166006844256722794136677593242087472511918765458138001691392985479370479413

[@@"opaque_to_smt"]
let e11t : elem =
  assert_norm (17132578894860187227106973862066098503361937009599285972127281064171051850952 < prime);
  17132578894860187227106973862066098503361937009599285972127281064171051850952

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
  assert_norm (38373209679500362751821244835993566390096837005599795795759800836389804226219 < prime);
  38373209679500362751821244835993566390096837005599795795759800836389804226219

[@@"opaque_to_smt"]
let e12y : elem =
  assert_norm (43239234650706108198304600506649220355430709106345833470525995242038951003673 < prime);
  43239234650706108198304600506649220355430709106345833470525995242038951003673

[@@"opaque_to_smt"]
let e12t : elem =
  assert_norm (18400884072406386708481337387088609750482565650158957410739853773941894267410 < prime);
  18400884072406386708481337387088609750482565650158957410739853773941894267410

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
  assert_norm (25789039763049693505099165551489099695263315209509080020595973547897023469971 < prime);
  25789039763049693505099165551489099695263315209509080020595973547897023469971

[@@"opaque_to_smt"]
let e13y : elem =
  assert_norm (47692579570826826006731565903709119194699617371610937928342488402358055264090 < prime);
  47692579570826826006731565903709119194699617371610937928342488402358055264090

[@@"opaque_to_smt"]
let e13t : elem =
  assert_norm (57310823328505133498469008608283878413148569164512491428906203942819139661419 < prime);
  57310823328505133498469008608283878413148569164512491428906203942819139661419

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
  assert_norm (9135310492617555490435552262374764352743596780602448790657612647530571395312 < prime);
  9135310492617555490435552262374764352743596780602448790657612647530571395312

[@@"opaque_to_smt"]
let e14y : elem =
  assert_norm (50183560959099319032261613678217014540532899655163175026136221753167762103507 < prime);
  50183560959099319032261613678217014540532899655163175026136221753167762103507

[@@"opaque_to_smt"]
let e14t : elem =
  assert_norm (33688857620210197244437107495897753202368586670900971028346688424232131270842 < prime);
  33688857620210197244437107495897753202368586670900971028346688424232131270842

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
  assert_norm (18857138683912167434595188014909886450282063683794934945045153457808237156324 < prime);
  18857138683912167434595188014909886450282063683794934945045153457808237156324

[@@"opaque_to_smt"]
let e15y : elem =
  assert_norm (26077938642733815250718316307462034604076874803922471999344460051920786411036 < prime);
  26077938642733815250718316307462034604076874803922471999344460051920786411036

[@@"opaque_to_smt"]
let e15t : elem =
  assert_norm (30882628577371758093673457846262206954386142441664533470668076434713538570571 < prime);
  30882628577371758093673457846262206954386142441664533470668076434713538570571

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
