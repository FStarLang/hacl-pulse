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

(** The roots of unity for the ML-DSA transform, and their Shoup
    companions, as [static const] arrays.

    Built the same way as {!Hacl.MLKEM.Tables}: the literals are checked
    against the specification's [zetas i = zeta^BitRev8(i)] by
    normalization, and the equation lives in the arrays' types.  With 256
    entries a single check is one SMT query too many, so it is cut into
    eight queries of 32 entries each.  Entry 0 is never read by the
    transform (the layers use indices 1 to 255) but is kept so that an
    index is the specification's index. *)
module Hacl.MLDSA.Tables

open Spec.MLDSA.Zq
open Spec.MLDSA.NTT
open Hacl.Impl.MLDSA.Zq

module G = Pulse.Lib.GlobalArray
module L = FStar.List.Tot
module Seq = FStar.Seq
module S32 = Hacl.Secret.UInt32

#set-options "--fuel 0 --ifuel 0"

#push-options "--fuel 1 --ifuel 1"

let rec ldrop (#a: Type) (k: nat) (l: list a) : list a
  = if k = 0 then l else match l with [] -> [] | _ :: tl -> ldrop (k - 1) tl

let rec ldrop_index (#a: Type) (k: nat) (l: list a) (j: nat)
  : Lemma (requires k <= j /\ j < L.length l)
          (ensures k <= L.length l /\ L.length (ldrop k l) == L.length l - k /\
                   L.index (ldrop k l) (j - k) == L.index l j)
          (decreases k)
  = if k = 0 then () else match l with _ :: tl -> ldrop_index (k - 1) tl (j - 1)

(** The first [k] entries of [l] are [f i], [f (i + 1)], ... *)
let rec ok_n (#a: Type) (pr: a -> GTot nat) (f: nat -> GTot nat) (i: nat) (l: list a) (k: nat)
  : GTot bool (decreases k)
  = k = 0 || (match l with
              | [] -> false
              | x :: tl -> pr x = f i && ok_n pr f (i + 1) tl (k - 1))

let rec ok_n_index (#a: Type) (pr: a -> GTot nat) (f: nat -> GTot nat) (i: nat) (l: list a)
                   (k: nat) (j: nat)
  : Lemma (requires ok_n pr f i l k /\ j < k)
          (ensures j < L.length l /\ pr (L.index l j) == f (i + j))
          (decreases k)
  = match l with x :: tl -> if j > 0 then ok_n_index pr f (i + 1) tl (k - 1) (j - 1)

let ok_at (#a: Type) (pr: a -> GTot nat) (f: nat -> GTot nat) (l: list a) (i: nat)
  : Lemma (requires L.length l == 256 /\ i < 256 /\
                    ok_n pr f (32 * (i / 32)) (ldrop (32 * (i / 32)) l) 32)
          (ensures pr (L.index l i) == f i)
  = let c = 32 * (i / 32) in
    ok_n_index pr f c (ldrop c l) 32 (i - c);
    ldrop_index c l i

#pop-options

let zeta_f (i: nat) : GTot nat = if i < 256 then zetas i else 0

let shoup_f (i: nat) : GTot nat = if i < 256 then (zetas i * 4294967296) / 8380417 else 0

let vz (x: zqt) : GTot nat = S32.v x
let vs (x: S32.t) : GTot nat = S32.v x

[@@"opaque_to_smt"]
let zeta_list : list zqt = [
  S32.classify 1ul; S32.classify 4808194ul; S32.classify 3765607ul; S32.classify 3761513ul; S32.classify 5178923ul; S32.classify 5496691ul; S32.classify 5234739ul; S32.classify 5178987ul;
  S32.classify 7778734ul; S32.classify 3542485ul; S32.classify 2682288ul; S32.classify 2129892ul; S32.classify 3764867ul; S32.classify 7375178ul; S32.classify 557458ul; S32.classify 7159240ul;
  S32.classify 5010068ul; S32.classify 4317364ul; S32.classify 2663378ul; S32.classify 6705802ul; S32.classify 4855975ul; S32.classify 7946292ul; S32.classify 676590ul; S32.classify 7044481ul;
  S32.classify 5152541ul; S32.classify 1714295ul; S32.classify 2453983ul; S32.classify 1460718ul; S32.classify 7737789ul; S32.classify 4795319ul; S32.classify 2815639ul; S32.classify 2283733ul;
  S32.classify 3602218ul; S32.classify 3182878ul; S32.classify 2740543ul; S32.classify 4793971ul; S32.classify 5269599ul; S32.classify 2101410ul; S32.classify 3704823ul; S32.classify 1159875ul;
  S32.classify 394148ul; S32.classify 928749ul; S32.classify 1095468ul; S32.classify 4874037ul; S32.classify 2071829ul; S32.classify 4361428ul; S32.classify 3241972ul; S32.classify 2156050ul;
  S32.classify 3415069ul; S32.classify 1759347ul; S32.classify 7562881ul; S32.classify 4805951ul; S32.classify 3756790ul; S32.classify 6444618ul; S32.classify 6663429ul; S32.classify 4430364ul;
  S32.classify 5483103ul; S32.classify 3192354ul; S32.classify 556856ul; S32.classify 3870317ul; S32.classify 2917338ul; S32.classify 1853806ul; S32.classify 3345963ul; S32.classify 1858416ul;
  S32.classify 3073009ul; S32.classify 1277625ul; S32.classify 5744944ul; S32.classify 3852015ul; S32.classify 4183372ul; S32.classify 5157610ul; S32.classify 5258977ul; S32.classify 8106357ul;
  S32.classify 2508980ul; S32.classify 2028118ul; S32.classify 1937570ul; S32.classify 4564692ul; S32.classify 2811291ul; S32.classify 5396636ul; S32.classify 7270901ul; S32.classify 4158088ul;
  S32.classify 1528066ul; S32.classify 482649ul; S32.classify 1148858ul; S32.classify 5418153ul; S32.classify 7814814ul; S32.classify 169688ul; S32.classify 2462444ul; S32.classify 5046034ul;
  S32.classify 4213992ul; S32.classify 4892034ul; S32.classify 1987814ul; S32.classify 5183169ul; S32.classify 1736313ul; S32.classify 235407ul; S32.classify 5130263ul; S32.classify 3258457ul;
  S32.classify 5801164ul; S32.classify 1787943ul; S32.classify 5989328ul; S32.classify 6125690ul; S32.classify 3482206ul; S32.classify 4197502ul; S32.classify 7080401ul; S32.classify 6018354ul;
  S32.classify 7062739ul; S32.classify 2461387ul; S32.classify 3035980ul; S32.classify 621164ul; S32.classify 3901472ul; S32.classify 7153756ul; S32.classify 2925816ul; S32.classify 3374250ul;
  S32.classify 1356448ul; S32.classify 5604662ul; S32.classify 2683270ul; S32.classify 5601629ul; S32.classify 4912752ul; S32.classify 2312838ul; S32.classify 7727142ul; S32.classify 7921254ul;
  S32.classify 348812ul; S32.classify 8052569ul; S32.classify 1011223ul; S32.classify 6026202ul; S32.classify 4561790ul; S32.classify 6458164ul; S32.classify 6143691ul; S32.classify 1744507ul;
  S32.classify 1753ul; S32.classify 6444997ul; S32.classify 5720892ul; S32.classify 6924527ul; S32.classify 2660408ul; S32.classify 6600190ul; S32.classify 8321269ul; S32.classify 2772600ul;
  S32.classify 1182243ul; S32.classify 87208ul; S32.classify 636927ul; S32.classify 4415111ul; S32.classify 4423672ul; S32.classify 6084020ul; S32.classify 5095502ul; S32.classify 4663471ul;
  S32.classify 8352605ul; S32.classify 822541ul; S32.classify 1009365ul; S32.classify 5926272ul; S32.classify 6400920ul; S32.classify 1596822ul; S32.classify 4423473ul; S32.classify 4620952ul;
  S32.classify 6695264ul; S32.classify 4969849ul; S32.classify 2678278ul; S32.classify 4611469ul; S32.classify 4829411ul; S32.classify 635956ul; S32.classify 8129971ul; S32.classify 5925040ul;
  S32.classify 4234153ul; S32.classify 6607829ul; S32.classify 2192938ul; S32.classify 6653329ul; S32.classify 2387513ul; S32.classify 4768667ul; S32.classify 8111961ul; S32.classify 5199961ul;
  S32.classify 3747250ul; S32.classify 2296099ul; S32.classify 1239911ul; S32.classify 4541938ul; S32.classify 3195676ul; S32.classify 2642980ul; S32.classify 1254190ul; S32.classify 8368000ul;
  S32.classify 2998219ul; S32.classify 141835ul; S32.classify 8291116ul; S32.classify 2513018ul; S32.classify 7025525ul; S32.classify 613238ul; S32.classify 7070156ul; S32.classify 6161950ul;
  S32.classify 7921677ul; S32.classify 6458423ul; S32.classify 4040196ul; S32.classify 4908348ul; S32.classify 2039144ul; S32.classify 6500539ul; S32.classify 7561656ul; S32.classify 6201452ul;
  S32.classify 6757063ul; S32.classify 2105286ul; S32.classify 6006015ul; S32.classify 6346610ul; S32.classify 586241ul; S32.classify 7200804ul; S32.classify 527981ul; S32.classify 5637006ul;
  S32.classify 6903432ul; S32.classify 1994046ul; S32.classify 2491325ul; S32.classify 6987258ul; S32.classify 507927ul; S32.classify 7192532ul; S32.classify 7655613ul; S32.classify 6545891ul;
  S32.classify 5346675ul; S32.classify 8041997ul; S32.classify 2647994ul; S32.classify 3009748ul; S32.classify 5767564ul; S32.classify 4148469ul; S32.classify 749577ul; S32.classify 4357667ul;
  S32.classify 3980599ul; S32.classify 2569011ul; S32.classify 6764887ul; S32.classify 1723229ul; S32.classify 1665318ul; S32.classify 2028038ul; S32.classify 1163598ul; S32.classify 5011144ul;
  S32.classify 3994671ul; S32.classify 8368538ul; S32.classify 7009900ul; S32.classify 3020393ul; S32.classify 3363542ul; S32.classify 214880ul; S32.classify 545376ul; S32.classify 7609976ul;
  S32.classify 3105558ul; S32.classify 7277073ul; S32.classify 508145ul; S32.classify 7826699ul; S32.classify 860144ul; S32.classify 3430436ul; S32.classify 140244ul; S32.classify 6866265ul;
  S32.classify 6195333ul; S32.classify 3123762ul; S32.classify 2358373ul; S32.classify 6187330ul; S32.classify 5365997ul; S32.classify 6663603ul; S32.classify 2926054ul; S32.classify 7987710ul;
  S32.classify 8077412ul; S32.classify 3531229ul; S32.classify 4405932ul; S32.classify 4606686ul; S32.classify 1900052ul; S32.classify 7598542ul; S32.classify 1054478ul; S32.classify 7648983ul ]

let zeta_len : squash (L.length zeta_list == 256) = assert_norm (L.length zeta_list == 256)

#push-options "--z3rlimit 100"
[@@"opaque_to_smt"]
let zeta_chunk_pred (c: nat) : prop = ok_n vz zeta_f (32 * c) (ldrop (32 * c) zeta_list) 32

let zeta_chunk_0 : squash (zeta_chunk_pred 0)
  = reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred 0);
    assert_norm (ok_n vz zeta_f 0 (ldrop 0 zeta_list) 32)
let zeta_chunk_1 : squash (zeta_chunk_pred 1)
  = reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred 1);
    assert_norm (ok_n vz zeta_f 32 (ldrop 32 zeta_list) 32)
let zeta_chunk_2 : squash (zeta_chunk_pred 2)
  = reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred 2);
    assert_norm (ok_n vz zeta_f 64 (ldrop 64 zeta_list) 32)
let zeta_chunk_3 : squash (zeta_chunk_pred 3)
  = reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred 3);
    assert_norm (ok_n vz zeta_f 96 (ldrop 96 zeta_list) 32)
let zeta_chunk_4 : squash (zeta_chunk_pred 4)
  = reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred 4);
    assert_norm (ok_n vz zeta_f 128 (ldrop 128 zeta_list) 32)
let zeta_chunk_5 : squash (zeta_chunk_pred 5)
  = reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred 5);
    assert_norm (ok_n vz zeta_f 160 (ldrop 160 zeta_list) 32)
let zeta_chunk_6 : squash (zeta_chunk_pred 6)
  = reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred 6);
    assert_norm (ok_n vz zeta_f 192 (ldrop 192 zeta_list) 32)
let zeta_chunk_7 : squash (zeta_chunk_pred 7)
  = reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred 7);
    assert_norm (ok_n vz zeta_f 224 (ldrop 224 zeta_list) 32)

let zeta_chunk_at (c: nat { c < 8 }) : Lemma (ok_n vz zeta_f (32 * c) (ldrop (32 * c) zeta_list) 32)
  = (match c with
     | 0 -> zeta_chunk_0
     | 1 -> zeta_chunk_1
     | 2 -> zeta_chunk_2
     | 3 -> zeta_chunk_3
     | 4 -> zeta_chunk_4
     | 5 -> zeta_chunk_5
     | 6 -> zeta_chunk_6
     | _ -> zeta_chunk_7);
    reveal_opaque (`%zeta_chunk_pred) (zeta_chunk_pred c)
#pop-options

let zeta_table : Seq.lseq zqt 256 = Seq.seq_of_list zeta_list

let zeta_table_index (i: nat { i < 256 })
  : Lemma (S32.v (Seq.index zeta_table i) == zetas i)
          [SMTPat (Seq.index zeta_table i)]
  = zeta_chunk_at (i / 32);
    ok_at vz zeta_f zeta_list i;
    Seq.lemma_seq_of_list_index zeta_list i

let zeta_arr : (a: G.static_array zqt
                  { G.static_array_elems a == (zeta_table <: Seq.seq zqt) })
  = G.mk_static_array zeta_list

/// The companions [floor(zeta_i 2^32 / q)], for
/// {!Hacl.Impl.MLDSA.Zq.zq_mul_shoup}.

[@@"opaque_to_smt"]
let zeta_shoup_list : list S32.t = [
  S32.classify 512ul; S32.classify 2464201481ul; S32.classify 1929875197ul; S32.classify 1927777020ul; S32.classify 2654200252ul; S32.classify 2817056487ul; S32.classify 2682805975ul; S32.classify 2654233052ul;
  S32.classify 3986604501ul; S32.classify 1815525077ul; S32.classify 1374673746ul; S32.classify 1091570560ul; S32.classify 1929495947ul; S32.classify 3779781878ul; S32.classify 285697463ul; S32.classify 3669113561ul;
  S32.classify 2567661992ul; S32.classify 2212650896ul; S32.classify 1364982363ul; S32.classify 3436726392ul; S32.classify 2488689263ul; S32.classify 4072478047ul; S32.classify 346752664ul; S32.classify 3610299524ul;
  S32.classify 2640679465ul; S32.classify 878576920ul; S32.classify 1257667336ul; S32.classify 748618599ul; S32.classify 3965620171ul; S32.classify 2457603037ul; S32.classify 1443016191ul; S32.classify 1170414139ul;
  S32.classify 1846138265ul; S32.classify 1631226336ul; S32.classify 1404529459ul; S32.classify 2456912187ul; S32.classify 2700671740ul; S32.classify 1076973523ul; S32.classify 1898723371ul; S32.classify 594436433ul;
  S32.classify 202001018ul; S32.classify 475984259ul; S32.classify 561427818ul; S32.classify 2497946046ul; S32.classify 1061813248ul; S32.classify 2235233714ul; S32.classify 1661512036ul; S32.classify 1104976546ul;
  S32.classify 1750224322ul; S32.classify 901666089ul; S32.classify 3875979746ul; S32.classify 2463051942ul; S32.classify 1925356481ul; S32.classify 3302869480ul; S32.classify 3415010211ul; S32.classify 2270563444ul;
  S32.classify 2810092632ul; S32.classify 1636082790ul; S32.classify 285388938ul; S32.classify 1983539117ul; S32.classify 1495136972ul; S32.classify 950076367ul; S32.classify 1714807468ul; S32.classify 952438994ul;
  S32.classify 1574918426ul; S32.classify 654783358ul; S32.classify 2944286256ul; S32.classify 1974159334ul; S32.classify 2143979938ul; S32.classify 2643277330ul; S32.classify 2695227961ul; S32.classify 4154511428ul;
  S32.classify 1285853322ul; S32.classify 1039411342ul; S32.classify 993005453ul; S32.classify 2339406601ul; S32.classify 1440787839ul; S32.classify 2765778257ul; S32.classify 3726339871ul; S32.classify 2131021878ul;
  S32.classify 783134478ul; S32.classify 247357818ul; S32.classify 588790216ul; S32.classify 2776805729ul; S32.classify 4005095516ul; S32.classify 86965172ul; S32.classify 1262003602ul; S32.classify 2586094582ul;
  S32.classify 2159672701ul; S32.classify 2507169516ul; S32.classify 1018755524ul; S32.classify 2656376328ul; S32.classify 889861154ul; S32.classify 120646188ul; S32.classify 2629261981ul; S32.classify 1669960605ul;
  S32.classify 2973099030ul; S32.classify 916321552ul; S32.classify 3069533161ul; S32.classify 3139418744ul; S32.classify 1784632064ul; S32.classify 2151221569ul; S32.classify 3628708540ul; S32.classify 3084408998ul;
  S32.classify 3619656757ul; S32.classify 1261461889ul; S32.classify 1555941048ul; S32.classify 318346815ul; S32.classify 1999506068ul; S32.classify 3666303008ul; S32.classify 1499481951ul; S32.classify 1729304567ul;
  S32.classify 695180180ul; S32.classify 2872391671ul; S32.classify 1375177022ul; S32.classify 2870837257ul; S32.classify 2517787500ul; S32.classify 1185330463ul; S32.classify 3960163579ul; S32.classify 4059646062ul;
  S32.classify 178766299ul; S32.classify 4126945055ul; S32.classify 518252219ul; S32.classify 3088431101ul; S32.classify 2337919325ul; S32.classify 3309811811ul; S32.classify 3148644264ul; S32.classify 894060583ul;
  S32.classify 898413ul; S32.classify 3303063718ul; S32.classify 2931959596ul; S32.classify 3548823048ul; S32.classify 1363460237ul; S32.classify 3382600197ul; S32.classify 4264653920ul; S32.classify 1420958685ul;
  S32.classify 605900043ul; S32.classify 44694137ul; S32.classify 326425359ul; S32.classify 2262746275ul; S32.classify 2267133791ul; S32.classify 3118062851ul; S32.classify 2611446953ul; S32.classify 2390030881ul;
  S32.classify 4280713634ul; S32.classify 421552614ul; S32.classify 517299994ul; S32.classify 3037216934ul; S32.classify 3280474237ul; S32.classify 818371957ul; S32.classify 2267031803ul; S32.classify 2368239875ul;
  S32.classify 3431325662ul; S32.classify 2547049737ul; S32.classify 1372618620ul; S32.classify 2363379834ul; S32.classify 2475075202ul; S32.classify 325927721ul; S32.classify 4166613613ul; S32.classify 3036585533ul;
  S32.classify 2170005223ul; S32.classify 3386515188ul; S32.classify 1123881662ul; S32.classify 3409833957ul; S32.classify 1223601433ul; S32.classify 2443943876ul; S32.classify 4157383481ul; S32.classify 2664982236ul;
  S32.classify 1920467227ul; S32.classify 1176751719ul; S32.classify 635454917ul; S32.classify 2327745167ul; S32.classify 1637785316ul; S32.classify 1354528380ul; S32.classify 642772911ul; S32.classify 4288603578ul;
  S32.classify 1536588519ul; S32.classify 72690498ul; S32.classify 4249200495ul; S32.classify 1287922799ul; S32.classify 3600584566ul; S32.classify 314284737ul; S32.classify 3623457973ul; S32.classify 3158002009ul;
  S32.classify 4059862849ul; S32.classify 3309944549ul; S32.classify 2070602177ul; S32.classify 2515530448ul; S32.classify 1045062171ul; S32.classify 3331529017ul; S32.classify 3875351933ul; S32.classify 3178246801ul;
  S32.classify 3462997676ul; S32.classify 1078959975ul; S32.classify 3078085255ul; S32.classify 3252640338ul; S32.classify 300448763ul; S32.classify 3690415129ul; S32.classify 270590488ul; S32.classify 2888967985ul;
  S32.classify 3538011851ul; S32.classify 1021949427ul; S32.classify 1276805127ul; S32.classify 3580972712ul; S32.classify 260312804ul; S32.classify 3686175725ul; S32.classify 3923504936ul; S32.classify 3354771936ul;
  S32.classify 2740173223ul; S32.classify 4121526901ul; S32.classify 1357098057ul; S32.classify 1542497136ul; S32.classify 2955879016ul; S32.classify 2126092136ul; S32.classify 384158533ul; S32.classify 2233306200ul;
  S32.classify 2040058689ul; S32.classify 1316619236ul; S32.classify 3467007480ul; S32.classify 883155599ul; S32.classify 853476187ul; S32.classify 1039370342ul; S32.classify 596344472ul; S32.classify 2568213442ul;
  S32.classify 2047270595ul; S32.classify 4288879303ul; S32.classify 3592576747ul; S32.classify 1547952704ul; S32.classify 1723816713ul; S32.classify 110126091ul; S32.classify 279505433ul; S32.classify 3900115954ul;
  S32.classify 1591599802ul; S32.classify 3729503024ul; S32.classify 260424529ul; S32.classify 4011186584ul; S32.classify 440824167ul; S32.classify 1758099916ul; S32.classify 71875109ul; S32.classify 3518963748ul;
  S32.classify 3175110811ul; S32.classify 1600929360ul; S32.classify 1208667170ul; S32.classify 3171009270ul; S32.classify 2750075757ul; S32.classify 3415099386ul; S32.classify 1499603926ul; S32.classify 4093704790ul;
  S32.classify 4139677103ul; S32.classify 1809756372ul; S32.classify 2258042033ul; S32.classify 2360928544ul; S32.classify 973777462ul; S32.classify 3894256024ul; S32.classify 540420425ul; S32.classify 3920107058ul ]

let zeta_shoup_len : squash (L.length zeta_shoup_list == 256)
  = assert_norm (L.length zeta_shoup_list == 256)

#push-options "--z3rlimit 100"
[@@"opaque_to_smt"]
let shoup_chunk_pred (c: nat) : prop = ok_n vs shoup_f (32 * c) (ldrop (32 * c) zeta_shoup_list) 32

let shoup_chunk_0 : squash (shoup_chunk_pred 0)
  = reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred 0);
    assert_norm (ok_n vs shoup_f 0 (ldrop 0 zeta_shoup_list) 32)
let shoup_chunk_1 : squash (shoup_chunk_pred 1)
  = reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred 1);
    assert_norm (ok_n vs shoup_f 32 (ldrop 32 zeta_shoup_list) 32)
let shoup_chunk_2 : squash (shoup_chunk_pred 2)
  = reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred 2);
    assert_norm (ok_n vs shoup_f 64 (ldrop 64 zeta_shoup_list) 32)
let shoup_chunk_3 : squash (shoup_chunk_pred 3)
  = reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred 3);
    assert_norm (ok_n vs shoup_f 96 (ldrop 96 zeta_shoup_list) 32)
let shoup_chunk_4 : squash (shoup_chunk_pred 4)
  = reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred 4);
    assert_norm (ok_n vs shoup_f 128 (ldrop 128 zeta_shoup_list) 32)
let shoup_chunk_5 : squash (shoup_chunk_pred 5)
  = reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred 5);
    assert_norm (ok_n vs shoup_f 160 (ldrop 160 zeta_shoup_list) 32)
let shoup_chunk_6 : squash (shoup_chunk_pred 6)
  = reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred 6);
    assert_norm (ok_n vs shoup_f 192 (ldrop 192 zeta_shoup_list) 32)
let shoup_chunk_7 : squash (shoup_chunk_pred 7)
  = reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred 7);
    assert_norm (ok_n vs shoup_f 224 (ldrop 224 zeta_shoup_list) 32)

let shoup_chunk_at (c: nat { c < 8 }) : Lemma (ok_n vs shoup_f (32 * c) (ldrop (32 * c) zeta_shoup_list) 32)
  = (match c with
     | 0 -> shoup_chunk_0
     | 1 -> shoup_chunk_1
     | 2 -> shoup_chunk_2
     | 3 -> shoup_chunk_3
     | 4 -> shoup_chunk_4
     | 5 -> shoup_chunk_5
     | 6 -> shoup_chunk_6
     | _ -> shoup_chunk_7);
    reveal_opaque (`%shoup_chunk_pred) (shoup_chunk_pred c)
#pop-options

let zeta_shoup_table : Seq.lseq S32.t 256 = Seq.seq_of_list zeta_shoup_list

let zeta_shoup_table_index (i: nat { i < 256 })
  : Lemma (S32.v (Seq.index zeta_shoup_table i) == shoup_of (S32.v (Seq.index zeta_table i)))
          [SMTPat (Seq.index zeta_shoup_table i)]
  = assert_norm (pow2 32 == 4294967296);
    shoup_chunk_at (i / 32);
    ok_at vs shoup_f zeta_shoup_list i;
    Seq.lemma_seq_of_list_index zeta_shoup_list i;
    zeta_table_index i

let zeta_shoup_arr : (a: G.static_array S32.t
                        { G.static_array_elems a == (zeta_shoup_table <: Seq.seq S32.t) })
  = G.mk_static_array zeta_shoup_list
