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
