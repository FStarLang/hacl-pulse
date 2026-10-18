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

(** Reading and writing bit windows of a radix-52 number.

    The twin of [Spec.Bignum51.Window], one bit wider.  secp256k1's field
    holds five fifty-two-bit limbs and its byte layer is proved in
    [Spec.Bignum4] on four sixty-four-bit ones, so a load has to read
    fifty-two-bit windows off sixty-four-bit limbs -- that is
    [Spec.Bignum4.Window] -- and a store has to rebuild sixty-four-bit
    limbs from the fifty-two-bit ones, which is {!eval_windows} here.
    Neither statement mentions [nl].

    This is a separate module rather than more of [Spec.Bignum52] only so
    that nothing else has to be reverified when it changes. *)
module Spec.Bignum52.Window

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical

open Spec.Bignum52

(** This module is arithmetic-heavy, and the default SMT encoding boxes
    every integer operation, which hides the structure of the products from
    Z3's arithmetic solver.  Encoding linear arithmetic natively and leaving
    only the nonlinear operators wrapped is measurably faster here. *)
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

#push-options "--fuel 1 --ifuel 1 --z3rlimit 150"

(** The [w] bits of [v] starting at bit [a]. *)
let win (v: nat) (a w: nat) : nat = (v / pow2 a) % pow2 w

(** The tail of a sequence, total. *)
let tl (t: Seq.seq nat) : Seq.seq nat =
  if Seq.length t = 0 then t else Seq.slice t 1 (Seq.length t)

let eval_head (t: Seq.seq nat) : Lemma (eval t == vat t 0 + base * eval (tl t)) = ()

let tl_vat (t: Seq.seq nat) (i: nat) : Lemma (vat (tl t) i == vat t (i + 1)) = ()

(** [eval] in terms of its three lowest limbs and a remainder. *)
let eval_head3 (t: Seq.seq nat)
  : Lemma (eval t == vat t 0 + pow2 rad * vat t 1 + pow2 (2 * rad) * vat t 2 +
                     pow2 (3 * rad) * eval (tl (tl (tl t))))
  = let t1 = tl t in
    let t2 = tl t1 in
    let t3 = tl t2 in
    eval_head t; eval_head t1; eval_head t2;
    tl_vat t 0; tl_vat t1 0;
    Math.pow2_plus rad rad;
    Math.pow2_plus rad (2 * rad);
    Math.distributivity_add_right base (vat t 1) (base * eval t2);
    Math.distributivity_add_right base (vat t 2) (base * eval t3);
    Math.paren_mul_right base base (eval t2);
    Math.paren_mul_right base base (vat t 2);
    Math.paren_mul_right (pow2 (2 * rad)) base (eval t3)

(** Shifting the whole number down by [j] limbs drops the low [j] limbs. *)
let eval_shift (s: Seq.seq nat) (j: nat { j <= Seq.length s })
  : Lemma (requires bnd s base)
          (ensures eval s / pow2 (rad * j) == eval (Seq.slice s j (Seq.length s)))
  = let n = Seq.length s in
    eval_split s j;
    let p = Seq.slice s 0 j in
    eval_bnd p;
    Math.lemma_div_plus (eval p) (eval (Seq.slice s j n)) (pow2 (rad * j));
    Math.small_div (eval p) (pow2 (rad * j))

(** A window of at most [3 * rad - off] bits starting [off] bits into limb
    [j] is read off limbs [j], [j + 1] and [j + 2] and nothing else. *)
let eval_win (s: Seq.seq nat) (j: nat { j <= Seq.length s }) (off: nat) (w: nat)
  : Lemma (requires bnd s base /\ off <= rad /\ w + off <= 3 * rad)
          (ensures win (eval s) (rad * j + off) w ==
                   (vat s j / pow2 off + pow2 (rad - off) * vat s (j + 1) +
                    pow2 (2 * rad - off) * vat s (j + 2)) % pow2 w)
  = let n = Seq.length s in
    let t = Seq.slice s j n in
    eval_shift s j;
    Math.pow2_plus (rad * j) off;
    Math.division_multiplication_lemma (eval s) (pow2 (rad * j)) (pow2 off);
    eval_head3 t;
    let r = eval (tl (tl (tl t))) in
    assert (vat t 0 == vat s j /\ vat t 1 == vat s (j + 1) /\ vat t 2 == vat s (j + 2));
    Math.pow2_plus off (rad - off);
    Math.pow2_plus off (2 * rad - off);
    Math.pow2_plus off (3 * rad - off);
    Math.paren_mul_right (pow2 off) (pow2 (rad - off)) (vat s (j + 1));
    Math.paren_mul_right (pow2 off) (pow2 (2 * rad - off)) (vat s (j + 2));
    Math.paren_mul_right (pow2 off) (pow2 (3 * rad - off)) r;
    Math.distributivity_add_right (pow2 off) (pow2 (rad - off) * vat s (j + 1))
      (pow2 (2 * rad - off) * vat s (j + 2) + pow2 (3 * rad - off) * r);
    Math.distributivity_add_right (pow2 off) (pow2 (2 * rad - off) * vat s (j + 2))
      (pow2 (3 * rad - off) * r);
    assert (eval t == vat s j + pow2 off *
              (pow2 (rad - off) * vat s (j + 1) + pow2 (2 * rad - off) * vat s (j + 2) +
               pow2 (3 * rad - off) * r));
    Math.lemma_div_plus (vat s j)
      (pow2 (rad - off) * vat s (j + 1) + pow2 (2 * rad - off) * vat s (j + 2) +
       pow2 (3 * rad - off) * r) (pow2 off);
    Math.pow2_plus w (3 * rad - off - w);
    Math.paren_mul_right (pow2 w) (pow2 (3 * rad - off - w)) r;
    Math.lemma_mod_plus (vat s j / pow2 off + pow2 (rad - off) * vat s (j + 1) +
                         pow2 (2 * rad - off) * vat s (j + 2))
                        (pow2 (3 * rad - off - w) * r) (pow2 w)

(** The common case: a window short enough to lie inside two limbs. *)
let eval_win2 (s: Seq.seq nat) (j: nat { j <= Seq.length s }) (off: nat) (w: nat)
  : Lemma (requires bnd s base /\ off <= rad /\ w + off <= 2 * rad)
          (ensures win (eval s) (rad * j + off) w ==
                   (vat s j / pow2 off + pow2 (rad - off) * vat s (j + 1)) % pow2 w)
  = eval_win s j off w;
    Math.pow2_plus w (2 * rad - off - w);
    Math.paren_mul_right (pow2 w) (pow2 (2 * rad - off - w)) (vat s (j + 2));
    Math.lemma_mod_plus (vat s j / pow2 off + pow2 (rad - off) * vat s (j + 1))
                        (pow2 (2 * rad - off - w) * vat s (j + 2)) (pow2 w)

(** The last step of [eval_windows], in a small context. *)
private let eval_windows_head (v: nat) (s: Seq.seq nat)
  : Lemma (requires Seq.length s > 0 /\ Seq.index s 0 == win v (rad * 0) rad /\
                    eval (tl s) == v / base)
          (ensures eval s == v)
  = eval_head s;
    assert_norm (pow2 0 == 1);
    assert (Seq.index s 0 == v % base);
    Math.swap_mul base (v / base);
    Math.euclidean_division_definition v base

(** The converse: a sequence whose limbs are the successive windows of [v]
    evaluates to [v]. *)
let rec eval_windows (v: nat) (s: Seq.seq nat)
  : Lemma (requires v < pow2 (rad * Seq.length s) /\
                    (forall (k: nat). k < Seq.length s ==>
                       Seq.index s k == win v (rad * k) rad))
          (ensures eval s == v /\ bnd s base)
          (decreases Seq.length s)
  = let n = Seq.length s in
    if n = 0 then ()
    else begin
      let t = Seq.slice s 1 n in
      let v' = v / base in
      Math.distributivity_sub_right rad n 1;
      Math.pow2_plus rad (rad * (n - 1));
      Math.lemma_div_lt_nat v (rad * n) rad;
      assert (v' < pow2 (rad * (n - 1)));
      let aux (k: nat { k < n - 1 }) : Lemma (Seq.index t k == win v' (rad * k) rad) =
        assert (Seq.index t k == Seq.index s (k + 1));
        Math.distributivity_add_right rad k 1;
        assert (Seq.index s (k + 1) == win v (rad * k + rad) rad);
        Math.pow2_plus (rad * k) rad;
        Math.division_multiplication_lemma v (pow2 (rad * k)) base;
        Math.division_multiplication_lemma v base (pow2 (rad * k)) in
      Classical.forall_intro aux;
      eval_windows v' t;
      assert (Seq.index s 0 == win v (rad * 0) rad);
      eval_windows_head v s
    end

#pop-options
