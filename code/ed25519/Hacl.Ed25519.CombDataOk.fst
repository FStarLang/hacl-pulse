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

(** The whole compiled-in comb table is what {!Hacl.Ed25519.CombEnt}
    says it should be: the eight generated proof modules, collected. *)
module Hacl.Ed25519.CombDataOk

open Hacl.Ed25519.CombEnt
open Hacl.Ed25519.CombData

module Seq = FStar.Seq
module G = Pulse.Lib.GlobalArray
module CT = Spec.Ed25519.CombTable
module Classical = FStar.Classical

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

let all_ok (_: unit)
  : Lemma (forall (j: nat { j < 32 }) (m: nat { m < 9 }). lent tbl_list j m)
  = Hacl.Ed25519.CombData0.grp_ok ();
    Hacl.Ed25519.CombData1.grp_ok ();
    Hacl.Ed25519.CombData2.grp_ok ();
    Hacl.Ed25519.CombData3.grp_ok ();
    Hacl.Ed25519.CombData4.grp_ok ();
    Hacl.Ed25519.CombData5.grp_ok ();
    Hacl.Ed25519.CombData6.grp_ok ();
    Hacl.Ed25519.CombData7.grp_ok ()

let tbl_ok (_: unit) : Lemma (ntok (G.static_array_elems tbl_arr))
  = reveal_opaque (`%tbl_seq) tbl_seq;
    all_ok ();
    let aux (j: nat { j < 32 }) (m: nat { m < 9 })
      : Lemma (nent tbl_seq (eoff j m) (CT.tp j m))
      = lent_elim tbl_list j m in
    Classical.forall_intro_2 aux

#pop-options
