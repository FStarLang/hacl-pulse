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

(** The zeta table, as a [static const] array in the program image.

    FIPS 203 tabulates these 128 constants in appendix A, but the
    specification defines them as [zeta^BitRev7(i)] rather than as
    literals, so the two have to be tied together.  That is done by
    normalization: both sides reduce to the same list of classified
    literals, and the equation lives in {!zeta_arr}'s type rather than in
    a lemma the caller has to remember to apply.

    The element type is the refined {!Hacl.Impl.MLKEM.Zq.zqt}, so reading
    a root out of the array hands the caller its bound instead of leaving
    it to be recovered.  The refinement erases, and the emitted array is a
    [static const uint16_t[128]].

    There is no table for the [gamma] of [BaseCaseMultiply]:
    [gamma_i = zeta_i^2 * zeta], so two multiplications recover it from
    the table that is already here, and a second 128-entry table would be
    256 bytes of cache for nothing. *)
module Hacl.MLKEM.Tables

open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq

module G = Pulse.Lib.GlobalArray
module L = FStar.List.Tot
module Seq = FStar.Seq
module U16 = FStar.UInt16
module S16 = Hacl.Secret.UInt16

/// A computable check that a list of secret words holds the roots
/// [zeta^BitRev7(i)], [zeta^BitRev7(i+1)], ...  It is a [GTot] boolean
/// because [S16.v] is ghost, but it still normalizes, which is the whole
/// point: [zeta_list_ok] below is discharged by computation.
let rec zeta_ok (i: nat) (l: list zqt)
  : GTot bool (decreases l)
  = match l with
    | [] -> i = 128
    | x :: tl -> i < 128 && S16.v x = zetas i && zeta_ok (i + 1) tl

let rec zeta_ok_index (i: nat) (l: list zqt) (j: nat { j < L.length l })
  : Lemma (requires zeta_ok i l)
          (ensures i + j < 128 /\ S16.v (L.index l j) == zetas (i + j))
          (decreases j)
  = match l with
    | x :: tl -> if j = 0 then () else zeta_ok_index (i + 1) tl (j - 1)

let zeta_list : list zqt = [
  S16.classify 1us; S16.classify 1729us; S16.classify 2580us; S16.classify 3289us; S16.classify 2642us; S16.classify 630us; S16.classify 1897us; S16.classify 848us;
  S16.classify 1062us; S16.classify 1919us; S16.classify 193us; S16.classify 797us; S16.classify 2786us; S16.classify 3260us; S16.classify 569us; S16.classify 1746us;
  S16.classify 296us; S16.classify 2447us; S16.classify 1339us; S16.classify 1476us; S16.classify 3046us; S16.classify 56us; S16.classify 2240us; S16.classify 1333us;
  S16.classify 1426us; S16.classify 2094us; S16.classify 535us; S16.classify 2882us; S16.classify 2393us; S16.classify 2879us; S16.classify 1974us; S16.classify 821us;
  S16.classify 289us; S16.classify 331us; S16.classify 3253us; S16.classify 1756us; S16.classify 1197us; S16.classify 2304us; S16.classify 2277us; S16.classify 2055us;
  S16.classify 650us; S16.classify 1977us; S16.classify 2513us; S16.classify 632us; S16.classify 2865us; S16.classify 33us; S16.classify 1320us; S16.classify 1915us;
  S16.classify 2319us; S16.classify 1435us; S16.classify 807us; S16.classify 452us; S16.classify 1438us; S16.classify 2868us; S16.classify 1534us; S16.classify 2402us;
  S16.classify 2647us; S16.classify 2617us; S16.classify 1481us; S16.classify 648us; S16.classify 2474us; S16.classify 3110us; S16.classify 1227us; S16.classify 910us;
  S16.classify 17us; S16.classify 2761us; S16.classify 583us; S16.classify 2649us; S16.classify 1637us; S16.classify 723us; S16.classify 2288us; S16.classify 1100us;
  S16.classify 1409us; S16.classify 2662us; S16.classify 3281us; S16.classify 233us; S16.classify 756us; S16.classify 2156us; S16.classify 3015us; S16.classify 3050us;
  S16.classify 1703us; S16.classify 1651us; S16.classify 2789us; S16.classify 1789us; S16.classify 1847us; S16.classify 952us; S16.classify 1461us; S16.classify 2687us;
  S16.classify 939us; S16.classify 2308us; S16.classify 2437us; S16.classify 2388us; S16.classify 733us; S16.classify 2337us; S16.classify 268us; S16.classify 641us;
  S16.classify 1584us; S16.classify 2298us; S16.classify 2037us; S16.classify 3220us; S16.classify 375us; S16.classify 2549us; S16.classify 2090us; S16.classify 1645us;
  S16.classify 1063us; S16.classify 319us; S16.classify 2773us; S16.classify 757us; S16.classify 2099us; S16.classify 561us; S16.classify 2466us; S16.classify 2594us;
  S16.classify 2804us; S16.classify 1092us; S16.classify 403us; S16.classify 1026us; S16.classify 1143us; S16.classify 2150us; S16.classify 2775us; S16.classify 886us;
  S16.classify 1722us; S16.classify 1212us; S16.classify 1874us; S16.classify 1029us; S16.classify 2110us; S16.classify 2935us; S16.classify 885us; S16.classify 2154us ]

#push-options "--z3rlimit 100"
let zeta_list_ok : squash (zeta_ok 0 zeta_list /\ L.length zeta_list == 128)
  = assert_norm (zeta_ok 0 zeta_list);
    assert_norm (L.length zeta_list == 128)

#pop-options

let zeta_table : Seq.lseq zqt 128 = Seq.seq_of_list zeta_list

let zeta_table_index (i: nat { i < 128 })
  : Lemma (S16.v (Seq.index zeta_table i) == zetas i)
          [SMTPat (Seq.index zeta_table i)]
  = zeta_ok_index 0 zeta_list i

let zeta_arr : (a: G.static_array zqt
                  { G.static_array_elems a == (zeta_table <: Seq.seq zqt) })
  = G.mk_static_array zeta_list

/// The Shoup companions [floor(zeta_i 2^16 / q)] of the roots, for
/// {!Hacl.Impl.MLKEM.Zq.zq_mul_shoup}.  Checked the same way.

let rec shoup_ok (i: nat) (l: list S16.t)
  : GTot bool (decreases l)
  = match l with
    | [] -> i = 128
    | x :: tl -> i < 128 && S16.v x = (zetas i * 65536) / 3329 && shoup_ok (i + 1) tl

let rec shoup_ok_index (i: nat) (l: list S16.t) (j: nat { j < L.length l })
  : Lemma (requires shoup_ok i l)
          (ensures i + j < 128 /\ S16.v (L.index l j) == (zetas (i + j) * 65536) / 3329)
          (decreases j)
  = match l with
    | x :: tl -> if j > 0 then shoup_ok_index (i + 1) tl (j - 1)

let zeta_shoup_list : list S16.t = [
  S16.classify 19us; S16.classify 34037us; S16.classify 50790us; S16.classify 64748us; S16.classify 52011us; S16.classify 12402us; S16.classify 37345us; S16.classify 16694us;
  S16.classify 20906us; S16.classify 37778us; S16.classify 3799us; S16.classify 15690us; S16.classify 54846us; S16.classify 64177us; S16.classify 11201us; S16.classify 34372us;
  S16.classify 5827us; S16.classify 48172us; S16.classify 26360us; S16.classify 29057us; S16.classify 59964us; S16.classify 1102us; S16.classify 44097us; S16.classify 26241us;
  S16.classify 28072us; S16.classify 41223us; S16.classify 10532us; S16.classify 56736us; S16.classify 47109us; S16.classify 56677us; S16.classify 38860us; S16.classify 16162us;
  S16.classify 5689us; S16.classify 6516us; S16.classify 64039us; S16.classify 34569us; S16.classify 23564us; S16.classify 45357us; S16.classify 44825us; S16.classify 40455us;
  S16.classify 12796us; S16.classify 38919us; S16.classify 49471us; S16.classify 12441us; S16.classify 56401us; S16.classify 649us; S16.classify 25986us; S16.classify 37699us;
  S16.classify 45652us; S16.classify 28249us; S16.classify 15886us; S16.classify 8898us; S16.classify 28309us; S16.classify 56460us; S16.classify 30198us; S16.classify 47286us;
  S16.classify 52109us; S16.classify 51519us; S16.classify 29155us; S16.classify 12756us; S16.classify 48704us; S16.classify 61224us; S16.classify 24155us; S16.classify 17914us;
  S16.classify 334us; S16.classify 54354us; S16.classify 11477us; S16.classify 52149us; S16.classify 32226us; S16.classify 14233us; S16.classify 45042us; S16.classify 21655us;
  S16.classify 27738us; S16.classify 52405us; S16.classify 64591us; S16.classify 4586us; S16.classify 14882us; S16.classify 42443us; S16.classify 59354us; S16.classify 60043us;
  S16.classify 33525us; S16.classify 32502us; S16.classify 54905us; S16.classify 35218us; S16.classify 36360us; S16.classify 18741us; S16.classify 28761us; S16.classify 52897us;
  S16.classify 18485us; S16.classify 45436us; S16.classify 47975us; S16.classify 47011us; S16.classify 14430us; S16.classify 46007us; S16.classify 5275us; S16.classify 12618us;
  S16.classify 31183us; S16.classify 45239us; S16.classify 40101us; S16.classify 63390us; S16.classify 7382us; S16.classify 50180us; S16.classify 41144us; S16.classify 32384us;
  S16.classify 20926us; S16.classify 6279us; S16.classify 54590us; S16.classify 14902us; S16.classify 41321us; S16.classify 11044us; S16.classify 48546us; S16.classify 51066us;
  S16.classify 55200us; S16.classify 21497us; S16.classify 7933us; S16.classify 20198us; S16.classify 22501us; S16.classify 42325us; S16.classify 54629us; S16.classify 17442us;
  S16.classify 33899us; S16.classify 23859us; S16.classify 36892us; S16.classify 20257us; S16.classify 41538us; S16.classify 57779us; S16.classify 17422us; S16.classify 42404us ]

#push-options "--z3rlimit 100"
let zeta_shoup_list_ok : squash (shoup_ok 0 zeta_shoup_list /\ L.length zeta_shoup_list == 128)
  = assert_norm (shoup_ok 0 zeta_shoup_list);
    assert_norm (L.length zeta_shoup_list == 128)
#pop-options

let zeta_shoup_table : Seq.lseq S16.t 128 = Seq.seq_of_list zeta_shoup_list

let zeta_shoup_table_index (i: nat { i < 128 })
  : Lemma (S16.v (Seq.index zeta_shoup_table i) == (S16.v (Seq.index zeta_table i) * pow2 16) / q)
          [SMTPat (Seq.index zeta_shoup_table i)]
  = assert_norm (pow2 16 == 65536);
    shoup_ok_index 0 zeta_shoup_list i;
    zeta_table_index i;
    Seq.lemma_seq_of_list_index zeta_shoup_list i;
    let z = S16.v (Seq.index zeta_table i) in
    assert (S16.v (Seq.index zeta_shoup_table i) == (z * 65536) / 3329)

let zeta_shoup_arr : (a: G.static_array S16.t
                        { G.static_array_elems a == (zeta_shoup_table <: Seq.seq S16.t) })
  = G.mk_static_array zeta_shoup_list
