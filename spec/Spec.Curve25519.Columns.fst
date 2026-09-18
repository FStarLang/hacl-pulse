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

(** The five folded columns of the schoolbook product, written out.

    [Spec.Curve25519.Field] describes [fmul] as a nine-column schoolbook
    product [part a b nl] whose top four columns are then folded down
    against [19] by [fold19].  That is the right way to {e prove} it --
    both halves are inductions -- and the wrong way to {e run} it: the
    nine columns have to live in memory, the fold is a second pass over
    them, and the whole thing costs more than the twenty-five
    multiplications it is made of.

    This module is the bridge.  Each of the five entries of
    [fold19 (part a b nl)] is given as one explicit five-term sum, in
    exactly the association and exactly the shape the implementation
    evaluates: [19] multiplied into the {e right} operand, where it costs
    four extra multiplications in total rather than four shifts per
    column, and the products summed left to right.  The implementation can
    then hold the five columns in five local variables and never mention
    an array at all.

    Everything here is unfolding.  [psucc] takes one step of the [repeati]
    that defines [part]; each [p0] to [p8] applies it five times; each
    [col0] to [col4] then rewrites [19 * (x * y)] into [x * (19 * y)] and
    distributes.  There is no new mathematics, which is the point: the
    fast [fmul] computes the same nine columns as the slow one, folded the
    same way. *)
module Spec.Curve25519.Columns

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

include Spec.Curve25519.Field

#push-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(** {2 Unfolding [part]}

    [part a b (i + 1)] adds row [i] to [part a b i], and row [i] touches
    column [k] exactly when [a_i] meets a limb of [b]. *)
let psucc (a b: Seq.seq nat) (i: nat { i < nl }) (k: nat { k < nw })
  : Lemma (vat (part a b (i + 1)) k ==
           vat (part a b i) k +
           (if i <= k && k - i < nl then vat a i * vat b (k - i) else 0))
  = part_step a b i;
    part_len a b i;
    part_len a b (i + 1)

(** [part a b 0] is the zero accumulator. *)
let pzero (a b: Seq.seq nat) (k: nat { k < nw })
  : Lemma (vat (part a b 0) k == 0) = ()

let p0 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 0 == vat a 0 * vat b 0)
  = assert_norm (nl == 5);
    pzero a b 0;
    psucc a b 0 0; psucc a b 1 0; psucc a b 2 0; psucc a b 3 0; psucc a b 4 0;
    ()

let p1 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 1 == vat a 0 * vat b 1 + vat a 1 * vat b 0)
  = assert_norm (nl == 5);
    pzero a b 1;
    psucc a b 0 1; psucc a b 1 1; psucc a b 2 1; psucc a b 3 1; psucc a b 4 1;
    ()

let p2 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 2 == vat a 0 * vat b 2 + vat a 1 * vat b 1 + vat a 2 * vat b 0)
  = assert_norm (nl == 5);
    pzero a b 2;
    psucc a b 0 2; psucc a b 1 2; psucc a b 2 2; psucc a b 3 2; psucc a b 4 2;
    ()

let p3 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 3 == vat a 0 * vat b 3 + vat a 1 * vat b 2 + vat a 2 * vat b 1 + vat a 3 * vat b 0)
  = assert_norm (nl == 5);
    pzero a b 3;
    psucc a b 0 3; psucc a b 1 3; psucc a b 2 3; psucc a b 3 3; psucc a b 4 3;
    ()

let p4 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 4 == vat a 0 * vat b 4 + vat a 1 * vat b 3 + vat a 2 * vat b 2 + vat a 3 * vat b 1 + vat a 4 * vat b 0)
  = assert_norm (nl == 5);
    pzero a b 4;
    psucc a b 0 4; psucc a b 1 4; psucc a b 2 4; psucc a b 3 4; psucc a b 4 4;
    ()

let p5 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 5 == vat a 1 * vat b 4 + vat a 2 * vat b 3 + vat a 3 * vat b 2 + vat a 4 * vat b 1)
  = assert_norm (nl == 5);
    pzero a b 5;
    psucc a b 0 5; psucc a b 1 5; psucc a b 2 5; psucc a b 3 5; psucc a b 4 5;
    ()

let p6 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 6 == vat a 2 * vat b 4 + vat a 3 * vat b 3 + vat a 4 * vat b 2)
  = assert_norm (nl == 5);
    pzero a b 6;
    psucc a b 0 6; psucc a b 1 6; psucc a b 2 6; psucc a b 3 6; psucc a b 4 6;
    ()

let p7 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 7 == vat a 3 * vat b 4 + vat a 4 * vat b 3)
  = assert_norm (nl == 5);
    pzero a b 7;
    psucc a b 0 7; psucc a b 1 7; psucc a b 2 7; psucc a b 3 7; psucc a b 4 7;
    ()

let p8 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 8 == vat a 4 * vat b 4)
  = assert_norm (nl == 5);
    pzero a b 8;
    psucc a b 0 8; psucc a b 1 8; psucc a b 2 8; psucc a b 3 8; psucc a b 4 8;
    ()

(** {2 Moving the nineteen}

    The specification folds with [19 * (a_i * b_j)]; the implementation
    scales [b] once and multiplies [a_i] by [19 * b_j].  Both are
    [(19 * a_i) * b_j] reassociated, which needs saying out loud because
    nonlinear arithmetic is off. *)
let m19 (x y: nat) : Lemma (19 * (x * y) == x * (19 * y))
  = Math.paren_mul_right 19 x y;
    Math.swap_mul 19 x;
    Math.paren_mul_right x 19 y

(** {2 The five columns}

    [vat] reads a limb off the end as zero, so column four has no folded
    part: there is no column nine. *)
let col0 (a b: Seq.seq nat)
  : Lemma (vat (fold19 (part a b nl)) 0 ==
           vat a 0 * vat b 0 +
           vat a 1 * (19 * vat b 4) +
           vat a 2 * (19 * vat b 3) +
           vat a 3 * (19 * vat b 2) +
           vat a 4 * (19 * vat b 1))
  = assert_norm (nl == 5);
    part_len a b nl;
    p0 a b;
    p5 a b;
    Math.distributivity_add_right 19 (vat a 1 * vat b 4 + vat a 2 * vat b 3 + vat a 3 * vat b 2) (vat a 4 * vat b 1);
    Math.distributivity_add_right 19 (vat a 1 * vat b 4 + vat a 2 * vat b 3) (vat a 3 * vat b 2);
    Math.distributivity_add_right 19 (vat a 1 * vat b 4) (vat a 2 * vat b 3);
    m19 (vat a 1) (vat b 4);
    m19 (vat a 2) (vat b 3);
    m19 (vat a 3) (vat b 2);
    m19 (vat a 4) (vat b 1);
    ()

let col1 (a b: Seq.seq nat)
  : Lemma (vat (fold19 (part a b nl)) 1 ==
           vat a 0 * vat b 1 +
           vat a 1 * vat b 0 +
           vat a 2 * (19 * vat b 4) +
           vat a 3 * (19 * vat b 3) +
           vat a 4 * (19 * vat b 2))
  = assert_norm (nl == 5);
    part_len a b nl;
    p1 a b;
    p6 a b;
    Math.distributivity_add_right 19 (vat a 2 * vat b 4 + vat a 3 * vat b 3) (vat a 4 * vat b 2);
    Math.distributivity_add_right 19 (vat a 2 * vat b 4) (vat a 3 * vat b 3);
    m19 (vat a 2) (vat b 4);
    m19 (vat a 3) (vat b 3);
    m19 (vat a 4) (vat b 2);
    ()

let col2 (a b: Seq.seq nat)
  : Lemma (vat (fold19 (part a b nl)) 2 ==
           vat a 0 * vat b 2 +
           vat a 1 * vat b 1 +
           vat a 2 * vat b 0 +
           vat a 3 * (19 * vat b 4) +
           vat a 4 * (19 * vat b 3))
  = assert_norm (nl == 5);
    part_len a b nl;
    p2 a b;
    p7 a b;
    Math.distributivity_add_right 19 (vat a 3 * vat b 4) (vat a 4 * vat b 3);
    m19 (vat a 3) (vat b 4);
    m19 (vat a 4) (vat b 3);
    ()

let col3 (a b: Seq.seq nat)
  : Lemma (vat (fold19 (part a b nl)) 3 ==
           vat a 0 * vat b 3 +
           vat a 1 * vat b 2 +
           vat a 2 * vat b 1 +
           vat a 3 * vat b 0 +
           vat a 4 * (19 * vat b 4))
  = assert_norm (nl == 5);
    part_len a b nl;
    p3 a b;
    p8 a b;
    m19 (vat a 4) (vat b 4);
    ()

let col4 (a b: Seq.seq nat)
  : Lemma (vat (fold19 (part a b nl)) 4 ==
           vat a 0 * vat b 4 +
           vat a 1 * vat b 3 +
           vat a 2 * vat b 2 +
           vat a 3 * vat b 1 +
           vat a 4 * vat b 0)
  = assert_norm (nl == 5);
    part_len a b nl;
    p4 a b;
    ()

#pop-options

(** {2 The carry chain, written out}

    [fmul_spec] finishes with [carry_fix (carry_pass f)]: four chain steps
    up the limbs, the wrap of the top limb back into limb zero against
    [19], and one more step to absorb what the wrap deposited there.
    Unfolded, that is exactly the straight line the implementation runs,
    with every intermediate a value rather than an array slot -- and with
    the carries [k0] to [k4] small enough to be carried in a word, which
    is the whole reason for doing it this way. *)

#push-options "--fuel 8 --ifuel 8 --z3rlimit 300"

let chain (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures (let k0 = vat s 0 / base in
                    let v1 = vat s 1 + k0 in let k1 = v1 / base in
                    let v2 = vat s 2 + k1 in let k2 = v2 / base in
                    let v3 = vat s 3 + k2 in let k3 = v3 / base in
                    let v4 = vat s 4 + k3 in let k4 = v4 / base in
                    let w0 = vat s 0 % base + 19 * k4 in
                    let r = carry_fix (carry_pass s) in
                    Seq.length r == nl /\
                    Seq.index r 0 == w0 % base /\
                    Seq.index r 1 == v1 % base + w0 / base /\
                    Seq.index r 2 == v2 % base /\
                    Seq.index r 3 == v3 % base /\
                    Seq.index r 4 == v4 % base))
  = assert_norm (nl == 5);
    carry_run_len s (nl - 1);
    carry_pass_len s;
    carry_fix_ok (carry_pass s)

#pop-options

(** Five limbs agreeing one by one is the same sequence.  Stated as a
    lemma so that the implementation never has to make the extensionality
    step inside its own proof context, where the surrounding equations
    make the quantifier expensive. *)
let five_eq (x y: Seq.seq nat)
  : Lemma (requires Seq.length x == nl /\ Seq.length y == nl /\
                    Seq.index x 0 == Seq.index y 0 /\
                    Seq.index x 1 == Seq.index y 1 /\
                    Seq.index x 2 == Seq.index y 2 /\
                    Seq.index x 3 == Seq.index y 3 /\
                    Seq.index x 4 == Seq.index y 4)
          (ensures x == y)
  = assert_norm (nl == 5);
    Seq.lemma_eq_intro x y
