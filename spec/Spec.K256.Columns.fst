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

(** The nine columns of secp256k1's schoolbook product, and what happens to
    them, written out.

    [Spec.K256.Field52] describes [fmul] as a nine-column product
    [part a b nl], a four-step carry of the top four columns into [hi], a
    fold of the result against [cf], and two carry passes.  That is the
    right way to {e prove} it -- every one of those steps is an induction
    over [repeati] -- and the wrong way to {e run} it, because it makes
    nine 128-bit columns and two five-limb intermediates live in memory
    when all of them fit in registers.

    This module is the bridge, exactly as [Spec.Curve25519.Columns] is for
    the radix-51 field.  It contains no new mathematics: [psucc] takes one
    step of the [repeati] behind [part] and [p0] to [p8] apply it five
    times; [run4] and [wpass] unfold the carry chain; [fcols] composes
    them into the five folded columns as five explicit expressions in the
    nine products.  The implementation can then hold everything in local
    variables and never mention an array.

    Where the radix-51 bridge has to move a [19] across a product, this one
    does not -- the fold multiplies a carried digit, not a limb of an
    operand -- so the products come out of [p0] to [p8] in exactly the
    association the implementation evaluates. *)
module Spec.K256.Columns

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

include Spec.K256.Field52

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
  : Lemma (vat (part a b nl) 2 ==
           vat a 0 * vat b 2 + vat a 1 * vat b 1 + vat a 2 * vat b 0)
  = assert_norm (nl == 5);
    pzero a b 2;
    psucc a b 0 2; psucc a b 1 2; psucc a b 2 2; psucc a b 3 2; psucc a b 4 2;
    ()

let p3 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 3 ==
           vat a 0 * vat b 3 + vat a 1 * vat b 2 + vat a 2 * vat b 1 + vat a 3 * vat b 0)
  = assert_norm (nl == 5);
    pzero a b 3;
    psucc a b 0 3; psucc a b 1 3; psucc a b 2 3; psucc a b 3 3; psucc a b 4 3;
    ()

let p4 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 4 ==
           vat a 0 * vat b 4 + vat a 1 * vat b 3 + vat a 2 * vat b 2 +
           vat a 3 * vat b 1 + vat a 4 * vat b 0)
  = assert_norm (nl == 5);
    pzero a b 4;
    psucc a b 0 4; psucc a b 1 4; psucc a b 2 4; psucc a b 3 4; psucc a b 4 4;
    ()

let p5 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 5 ==
           vat a 1 * vat b 4 + vat a 2 * vat b 3 + vat a 3 * vat b 2 + vat a 4 * vat b 1)
  = assert_norm (nl == 5);
    pzero a b 5;
    psucc a b 0 5; psucc a b 1 5; psucc a b 2 5; psucc a b 3 5; psucc a b 4 5;
    ()

let p6 (a b: Seq.seq nat)
  : Lemma (vat (part a b nl) 6 ==
           vat a 2 * vat b 4 + vat a 3 * vat b 3 + vat a 4 * vat b 2)
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

#pop-options

(** {2 The carry chain, written out}

    Four steps up a five-limb number.  The last limb is left alone -- this
    is the run that [hi] uses, where the top limb started at zero and the
    whole point is that what lands on it is a carry and nothing else. *)

#push-options "--fuel 8 --ifuel 8 --z3rlimit 300"

let run4 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures (let k0 = vat s 0 / base in
                    let v1 = vat s 1 + k0 in let k1 = v1 / base in
                    let v2 = vat s 2 + k1 in let k2 = v2 / base in
                    let v3 = vat s 3 + k2 in let k3 = v3 / base in
                    let r = carry_run s (nl - 1) in
                    Seq.length r == nl /\
                    Seq.index r 0 == vat s 0 % base /\
                    Seq.index r 1 == v1 % base /\
                    Seq.index r 2 == v2 % base /\
                    Seq.index r 3 == v3 % base /\
                    Seq.index r 4 == vat s 4 + k3))
  = assert_norm (nl == 5);
    carry_run_len s (nl - 1)

(** And the same four steps followed by the wrap: the top limb keeps its
    low digit and its overflow comes back into limb zero against [cf].
    Both of [fmul]'s passes are this. *)
let wpass (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl)
          (ensures (let k0 = vat s 0 / base in
                    let v1 = vat s 1 + k0 in let k1 = v1 / base in
                    let v2 = vat s 2 + k1 in let k2 = v2 / base in
                    let v3 = vat s 3 + k2 in let k3 = v3 / base in
                    let v4 = vat s 4 + k3 in let k4 = v4 / base in
                    let r = carry_pass s in
                    Seq.length r == nl /\
                    Seq.index r 0 == vat s 0 % base + cf * k4 /\
                    Seq.index r 1 == v1 % base /\
                    Seq.index r 2 == v2 % base /\
                    Seq.index r 3 == v3 % base /\
                    Seq.index r 4 == v4 % base))
  = assert_norm (nl == 5);
    run4 s;
    carry_run_len s (nl - 1);
    carry_pass_len s

#pop-options

(** {2 The five folded columns}

    [prep] carries columns five to eight into four proper digits and a
    fifth limb that holds only what reached it, and [fold] adds [cf] times
    each of those to the column five places down.  Unfolded, that is five
    expressions in the nine products and one four-step chain -- which is
    what the implementation runs, top to bottom, out of registers. *)

(** Named, because [fold] is a keyword in Pulse and the implementation
    cannot write it. *)
let folded (c: Seq.seq nat) : Seq.seq nat = fold (prep c)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 300"

let fcols (c: Seq.seq nat)
  : Lemma (requires Seq.length c == nw)
          (ensures (let k5 = vat c 5 / base in
                    let v6 = vat c 6 + k5 in let k6 = v6 / base in
                    let v7 = vat c 7 + k6 in let k7 = v7 / base in
                    let v8 = vat c 8 + k7 in let k8 = v8 / base in
                    let f = folded c in
                    Seq.length f == nl /\
                    Seq.index f 0 == vat c 0 + cf * (vat c 5 % base) /\
                    Seq.index f 1 == vat c 1 + cf * (v6 % base) /\
                    Seq.index f 2 == vat c 2 + cf * (v7 % base) /\
                    Seq.index f 3 == vat c 3 + cf * (v8 % base) /\
                    Seq.index f 4 == vat c 4 + cf * k8))
  = assert_norm (nl == 5);
    assert_norm (nw == 9);
    let u = Seq.slice c 0 nl in
    let w = w5 c in
    w5_ok c;
    assert (forall (i: nat). i < nl - 1 ==> vat w i == vat c (nl + i));
    run4 w;
    let h = hi c in
    prep_len c;
    let aux1 (i: nat { i < nl }) : Lemma (vat (prep c) i == vat c i) =
      Seq.lemma_index_app1 u h i in
    FStar.Classical.forall_intro aux1;
    let aux2 (i: nat { i < nl }) : Lemma (vat (prep c) (nl + i) == Seq.index h i) =
      Seq.lemma_index_app2 u h (nl + i) in
    FStar.Classical.forall_intro aux2;
    ()

#pop-options

(** Five limbs agreeing one by one is the same sequence.  Stated as a
    lemma so that the implementation never has to make the extensionality
    step inside its own proof context. *)
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

(** And nine, for the columns themselves. *)
let nine_eq (x y: Seq.seq nat)
  : Lemma (requires Seq.length x == nw /\ Seq.length y == nw /\
                    (forall (i: nat). i < nw ==> Seq.index x i == Seq.index y i))
          (ensures x == y)
  = Seq.lemma_eq_intro x y
