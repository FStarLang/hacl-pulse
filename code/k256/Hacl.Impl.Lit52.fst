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

(** Writing a radix-[2^52] constant down as a list of limbs.

    [Hacl.Impl.Lit4] does this at radix [2^64] and this is the same
    induction at radix [2^52]: a list of literals adds up to a number, and
    a bounded list of the right length that adds up to [x] is the sequence
    of digits of [x], which is what [Spec.K256.Freeze.limbs_of] names and
    what the curve-constant tables have to be shown to hold.

    The public half of [Hacl.Impl.Lit4] has no counterpart here: the only
    exponents in secp256k1 are scalar-field ones, and the scalar field
    stays on the four-limb Montgomery core. *)
module Hacl.Impl.Lit52

open Spec.Bignum52
open Spec.K256.Freeze
open Hacl.Impl.Limb4

module Seq = FStar.Seq
module L = FStar.List.Tot
module Classical = FStar.Classical
module S64 = Hacl.Secret.UInt64
module U64 = FStar.UInt64

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 A list of limbs} *)

let rec leval (l: list S64.t) : GTot nat =
  match l with
  | [] -> 0
  | h :: t -> S64.v h + base * leval t

let rec lbnd (l: list S64.t) : GTot bool =
  match l with
  | [] -> true
  | h :: t -> S64.v h < base && lbnd t

(** One induction carries both across [Seq.seq_of_list]. *)
let rec lit_ok (l: list S64.t)
  : Lemma (ensures eval (vals (Seq.seq_of_list l)) == leval l /\
                   (lbnd l ==> bnd (vals (Seq.seq_of_list l)) base))
          (decreases l)
  = match l with
    | [] -> Seq.lemma_eq_intro (Seq.seq_of_list l) Seq.empty
    | h :: t ->
      lit_ok t;
      let s = vals (Seq.seq_of_list l) in
      let n = Seq.length s in
      Classical.forall_intro (Seq.lemma_seq_of_list_index l);
      Classical.forall_intro (Seq.lemma_seq_of_list_index t);
      Seq.lemma_eq_intro (Seq.slice s 1 n) (vals (Seq.seq_of_list t))

(** A bounded sequence is determined by the number it evaluates to, so the
    literals are the limbs as soon as they add up. *)
let lit_limbs (l: list S64.t) (x: nat)
  : Lemma (requires L.length l == nl /\ lbnd l /\ leval l == x /\ x < pow2 256)
          (ensures vals (Seq.seq_of_list l) == limbs_of x)
  = lit_ok l;
    let s = vals (Seq.seq_of_list l) in
    let aux (k: nat { k < nl }) : Lemma (Seq.index s k == Seq.index (limbs_of x) k)
      = eval_digit s k;
        limbs_index x k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro s (limbs_of x)

#pop-options
