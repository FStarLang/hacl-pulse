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

(** Repacking between the five fifty-one-bit limbs of Curve25519's field
    and the eight thirty-two-bit limbs of [Spec.Bignum256].

    A fifty-one-bit limb is not a whole number of bytes, so the byte layer
    of the field goes through the thirty-two-bit representation, whose own
    byte layer is a shuffle and is already proved.  What is left is the bit
    repacking, and that is what this module states: each limb of either
    representation is a window of the number the other one denotes.

    There is one lemma per limb -- five one way, eight the other -- so that
    no single query carries more than one window, and the two quantified
    statements [load_ok] and [store_ok] want are assembled from them by a
    case split.  The whole thing lives in its own module for the same
    reason: put next to the rest of the field, every one of these queries
    drags in the ambient context of a fifteen-hundred-line implementation
    and takes minutes instead of seconds. *)
module Spec.Curve25519.Repack

open Spec.Curve25519.Field

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module B32 = Spec.Bignum256
module W = Spec.Bignum51.Window
module W32 = Spec.Bignum256.Window

(** The five fifty-one-bit limbs, as windows of the thirty-two-bit ones.
    The offsets are [(0,0)], [(1,19)], [(3,6)], [(4,25)] and [(6,12)]; the
    two whose offset plus fifty-one exceeds sixty-four straddle three
    thirty-two-bit limbs, the rest only two.  One lemma each, so that no
    single query carries more than one window. *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

let lw0 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == 8 /\ B32.bnd h B32.base)
          (ensures W32.win (B32.eval h) (rad * 0) rad ==
                   (B32.vat h 0 / pow2 0 + pow2 32 * B32.vat h 1) % pow2 51)
  = assert_norm (rad * 0 == B32.rad * 0 + 0 /\ rad == 51 /\ B32.rad - 0 == 32);
    W32.eval_win2 h 0 0 51

let lw1 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == 8 /\ B32.bnd h B32.base)
          (ensures W32.win (B32.eval h) (rad * 1) rad ==
                   (B32.vat h 1 / pow2 19 + pow2 13 * B32.vat h 2 +
                    pow2 45 * B32.vat h 3) % pow2 51)
  = assert_norm (rad * 1 == B32.rad * 1 + 19 /\ rad == 51 /\
                 B32.rad - 19 == 13 /\ 2 * B32.rad - 19 == 45);
    W32.eval_win h 1 19 51

let lw2 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == 8 /\ B32.bnd h B32.base)
          (ensures W32.win (B32.eval h) (rad * 2) rad ==
                   (B32.vat h 3 / pow2 6 + pow2 26 * B32.vat h 4) % pow2 51)
  = assert_norm (rad * 2 == B32.rad * 3 + 6 /\ rad == 51 /\ B32.rad - 6 == 26);
    W32.eval_win2 h 3 6 51

let lw3 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == 8 /\ B32.bnd h B32.base)
          (ensures W32.win (B32.eval h) (rad * 3) rad ==
                   (B32.vat h 4 / pow2 25 + pow2 7 * B32.vat h 5 +
                    pow2 39 * B32.vat h 6) % pow2 51)
  = assert_norm (rad * 3 == B32.rad * 4 + 25 /\ rad == 51 /\
                 B32.rad - 25 == 7 /\ 2 * B32.rad - 25 == 39);
    W32.eval_win h 4 25 51

let lw4 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == 8 /\ B32.bnd h B32.base)
          (ensures W32.win (B32.eval h) (rad * 4) rad ==
                   (B32.vat h 6 / pow2 12 + pow2 20 * B32.vat h 7) % pow2 51)
  = assert_norm (rad * 4 == B32.rad * 6 + 12 /\ rad == 51 /\ B32.rad - 12 == 20);
    W32.eval_win2 h 6 12 51

(** The five limb indices, as a case split kept out of the context below. *)
let below5 (k: nat { k < nl })
  : Lemma (k == 0 \/ k == 1 \/ k == 2 \/ k == 3 \/ k == 4)
  = assert_norm (nl == 5)

let load_windows (h s: Seq.seq nat)
  : Lemma (requires Seq.length h == 8 /\ B32.bnd h B32.base /\ Seq.length s == nl /\
             Seq.index s 0 == (B32.vat h 0 / pow2 0 + pow2 32 * B32.vat h 1) % pow2 51 /\
             Seq.index s 1 == (B32.vat h 1 / pow2 19 + pow2 13 * B32.vat h 2 +
                               pow2 45 * B32.vat h 3) % pow2 51 /\
             Seq.index s 2 == (B32.vat h 3 / pow2 6 + pow2 26 * B32.vat h 4) % pow2 51 /\
             Seq.index s 3 == (B32.vat h 4 / pow2 25 + pow2 7 * B32.vat h 5 +
                               pow2 39 * B32.vat h 6) % pow2 51 /\
             Seq.index s 4 == (B32.vat h 6 / pow2 12 + pow2 20 * B32.vat h 7) % pow2 51)
          (ensures (forall (k: nat). k < nl ==>
                      Seq.index s k == W32.win (B32.eval h) (rad * k) rad))
  = let aux (k: nat { k < nl })
      : Lemma (Seq.index s k == W32.win (B32.eval h) (rad * k) rad)
      = assert_norm (nl == 5);
        if k = 0 then lw0 h
        else if k = 1 then lw1 h
        else if k = 2 then lw2 h
        else if k = 3 then lw3 h
        else begin below5 k; lw4 h end in
    Classical.forall_intro aux

(** And the eight thirty-two-bit limbs as windows of the five.  Offsets
    [(0,0)], [(0,32)], [(1,13)], [(1,45)], [(2,26)], [(3,7)], [(3,39)],
    [(4,20)]; thirty-two bits never reach a third limb. *)

let sw0 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B32.rad * 0) B32.rad ==
                   (vat s 0 / pow2 0 + pow2 51 * vat s 1) % pow2 32)
  = assert_norm (B32.rad * 0 == rad * 0 + 0);
    assert_norm (B32.rad == 32);
    assert_norm (rad - 0 == 51);
    W.eval_win2 s 0 0 32

let sw1 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B32.rad * 1) B32.rad ==
                   (vat s 0 / pow2 32 + pow2 19 * vat s 1) % pow2 32)
  = assert_norm (B32.rad * 1 == rad * 0 + 32);
    assert_norm (B32.rad == 32);
    assert_norm (rad - 32 == 19);
    W.eval_win2 s 0 32 32

let sw2 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B32.rad * 2) B32.rad ==
                   (vat s 1 / pow2 13 + pow2 38 * vat s 2) % pow2 32)
  = assert_norm (B32.rad * 2 == rad * 1 + 13);
    assert_norm (B32.rad == 32);
    assert_norm (rad - 13 == 38);
    W.eval_win2 s 1 13 32

let sw3 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B32.rad * 3) B32.rad ==
                   (vat s 1 / pow2 45 + pow2 6 * vat s 2) % pow2 32)
  = assert_norm (B32.rad * 3 == rad * 1 + 45);
    assert_norm (B32.rad == 32);
    assert_norm (rad - 45 == 6);
    W.eval_win2 s 1 45 32

let sw4 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B32.rad * 4) B32.rad ==
                   (vat s 2 / pow2 26 + pow2 25 * vat s 3) % pow2 32)
  = assert_norm (B32.rad * 4 == rad * 2 + 26);
    assert_norm (B32.rad == 32);
    assert_norm (rad - 26 == 25);
    W.eval_win2 s 2 26 32

let sw5 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B32.rad * 5) B32.rad ==
                   (vat s 3 / pow2 7 + pow2 44 * vat s 4) % pow2 32)
  = assert_norm (B32.rad * 5 == rad * 3 + 7);
    assert_norm (B32.rad == 32);
    assert_norm (rad - 7 == 44);
    W.eval_win2 s 3 7 32

let sw6 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B32.rad * 6) B32.rad ==
                   (vat s 3 / pow2 39 + pow2 12 * vat s 4) % pow2 32)
  = assert_norm (B32.rad * 6 == rad * 3 + 39);
    assert_norm (B32.rad == 32);
    assert_norm (rad - 39 == 12);
    W.eval_win2 s 3 39 32

let sw7 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B32.rad * 7) B32.rad ==
                   (vat s 4 / pow2 20 + pow2 31 * vat s 5) % pow2 32)
  = assert_norm (B32.rad * 7 == rad * 4 + 20);
    assert_norm (B32.rad == 32);
    assert_norm (rad - 20 == 31);
    W.eval_win2 s 4 20 32

(** The eight limb indices, as a case split kept out of the context below. *)
let below8 (j: nat { j < 8 })
  : Lemma (j == 0 \/ j == 1 \/ j == 2 \/ j == 3 \/ j == 4 \/ j == 5 \/ j == 6 \/ j == 7)
  = ()

let store_windows (s u: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base /\ Seq.length u == 8 /\
             Seq.index u 0 == (vat s 0 / pow2 0 + pow2 51 * vat s 1) % pow2 32 /\
             Seq.index u 1 == (vat s 0 / pow2 32 + pow2 19 * vat s 1) % pow2 32 /\
             Seq.index u 2 == (vat s 1 / pow2 13 + pow2 38 * vat s 2) % pow2 32 /\
             Seq.index u 3 == (vat s 1 / pow2 45 + pow2 6 * vat s 2) % pow2 32 /\
             Seq.index u 4 == (vat s 2 / pow2 26 + pow2 25 * vat s 3) % pow2 32 /\
             Seq.index u 5 == (vat s 3 / pow2 7 + pow2 44 * vat s 4) % pow2 32 /\
             Seq.index u 6 == (vat s 3 / pow2 39 + pow2 12 * vat s 4) % pow2 32 /\
             Seq.index u 7 == (vat s 4 / pow2 20 + pow2 31 * vat s 5) % pow2 32)
          (ensures (forall (j: nat). j < 8 ==>
                      Seq.index u j == W.win (eval s) (B32.rad * j) B32.rad))
  = let aux (j: nat { j < 8 })
      : Lemma (Seq.index u j == W.win (eval s) (B32.rad * j) B32.rad)
      = if j = 0 then sw0 s
        else if j = 1 then sw1 s
        else if j = 2 then sw2 s
        else if j = 3 then sw3 s
        else if j = 4 then sw4 s
        else if j = 5 then sw5 s
        else if j = 6 then sw6 s
        else begin below8 j; sw7 s end in
    Classical.forall_intro aux

#pop-options


