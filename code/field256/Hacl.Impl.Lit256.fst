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

(** Connecting a limb literal to the number it denotes.

    A table of constants is written as a list of sixteen literals, and what
    it has to prove is that those literals are [Spec.Field256]'s [limbs x]
    -- that is, [Seq.init nl (fun i -> x / 2^16i mod 2^16)].  Proving it
    index by index means sixteen case splits inside a query that also
    carries [Seq.init], which is slow enough to be unusable.

    Going through the value instead costs nothing.  [leval] and [lbnd] are
    the evaluation and the bound written as recursions on the {i list},
    which the normaliser computes in one step and with no sequence axioms at
    all; [lit_ok] relates them to their sequence counterparts by one generic
    induction; and [lit_limbs] closes the loop with [eval_digit], which says
    that a bounded sequence is determined by the number it evaluates to.
    Each table then needs three [assert_norm]s on concrete arithmetic and
    one generic lemma call.

    The [u] half is the same for the public limbs an exponent is made of,
    which are [FStar.UInt64] rather than secret words because the
    exponentiation loop reads them. *)
module Hacl.Impl.Lit256

open Spec.Bignum256
open Spec.Field256
open Hacl.Impl.Limb

module Seq = FStar.Seq
module L = FStar.List.Tot
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
          (ensures vals (Seq.seq_of_list l) == limbs x)
  = lit_ok l;
    let s = vals (Seq.seq_of_list l) in
    let aux (k: nat { k < nl }) : Lemma (Seq.index s k == Seq.index (limbs x) k)
      = eval_digit s k;
        Seq.init_index_ #nat nl (fun i -> x / pow2 (rad * i) % base) k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro s (limbs x)

(** {2 Public limbs}

    An exponent is not a secret: the three that appear here -- [p - 2],
    [(p + 1) / 4] and [n - 2] -- are in the standard.  Keeping them public
    is what lets the exponentiation loop branch on a bit rather than
    multiply unconditionally, which halves it.  The machinery is the same
    as above with [U64] in place of [S64]. *)

let pvals (v: Seq.seq U64.t)
  : GTot (s: Seq.seq nat { Seq.length s == Seq.length v /\
                           (forall (i: nat). i < Seq.length v ==>
                              Seq.index s i == U64.v (Seq.index v i)) })
  = Seq.init_ghost (Seq.length v) (fun i -> (U64.v (Seq.index v i) <: nat))

let rec uleval (l: list U64.t) : GTot nat =
  match l with
  | [] -> 0
  | h :: t -> U64.v h + base * uleval t

let rec ulbnd (l: list U64.t) : GTot bool =
  match l with
  | [] -> true
  | h :: t -> U64.v h < base && ulbnd t

let rec ulit_ok (l: list U64.t)
  : Lemma (ensures eval (pvals (Seq.seq_of_list l)) == uleval l /\
                   (ulbnd l ==> bnd (pvals (Seq.seq_of_list l)) base))
          (decreases l)
  = match l with
    | [] -> Seq.lemma_eq_intro (Seq.seq_of_list l) Seq.empty
    | h :: t ->
      ulit_ok t;
      let s = pvals (Seq.seq_of_list l) in
      let n = Seq.length s in
      Classical.forall_intro (Seq.lemma_seq_of_list_index l);
      Classical.forall_intro (Seq.lemma_seq_of_list_index t);
      Seq.lemma_eq_intro (Seq.slice s 1 n) (pvals (Seq.seq_of_list t))

let ulit_limbs (l: list U64.t) (x: nat)
  : Lemma (requires L.length l == nl /\ ulbnd l /\ uleval l == x /\ x < pow2 256)
          (ensures pvals (Seq.seq_of_list l) == limbs x)
  = ulit_ok l;
    let s = pvals (Seq.seq_of_list l) in
    let aux (k: nat { k < nl }) : Lemma (Seq.index s k == Seq.index (limbs x) k)
      = eval_digit s k;
        Seq.init_index_ #nat nl (fun i -> x / pow2 (rad * i) % base) k in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro s (limbs x)

#pop-options
