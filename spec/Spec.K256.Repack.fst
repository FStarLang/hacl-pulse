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

(** Repacking between the five fifty-two-bit limbs of secp256k1's field and
    the four sixty-four-bit limbs of [Spec.Bignum4].

    A fifty-two-bit limb is not a whole number of bytes, so the byte layer
    of the field goes through the sixty-four-bit representation, whose own
    big-endian layer is a byte shuffle and is already proved.  What is left
    is the bit repacking, and that is what this module states: each limb of
    either representation is a window of the number the other one denotes.

    There is one lemma per limb -- five one way, four the other -- so that
    no single query carries more than one window, and the two quantified
    statements [load_ok] and [store_ok] want are assembled from them by a
    case split.  The whole thing lives in its own module for the same
    reason [Spec.Curve25519.Repack] does: put next to the rest of the
    field, every one of these queries drags in the ambient context of a
    thousand-line implementation and takes minutes instead of seconds.

    Two of the nine windows are degenerate and are stated in the form the
    code actually computes.  The bottom fifty-two-bit limb is a mask of the
    bottom sixty-four-bit one, because the next sixty-four-bit limb sits
    entirely above bit fifty-two; and the top fifty-two-bit limb is a plain
    shift of the top sixty-four-bit one, because there is no limb above it
    and a sixty-four-bit number shifted down by sixteen already fits. *)
module Spec.K256.Repack

open Spec.K256.Field52

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module B4 = Spec.Bignum4
module W = Spec.Bignum52.Window
module W4 = Spec.Bignum4.Window

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"

(** {2 Loading}

    The five fifty-two-bit limbs, as windows of the four sixty-four-bit
    ones.  The offsets are [(0,0)], [(0,52)], [(1,40)], [(2,28)] and
    [(3,16)]: fifty-two bits starting at a multiple of fifty-two never
    reach past the limb after the one they start in, so every window
    spans at most two sixty-four-bit limbs. *)

let lw0 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == B4.nl /\ B4.bnd h B4.base)
          (ensures W4.win (B4.eval h) (rad * 0) rad == B4.vat h 0 % pow2 52)
  = assert_norm (rad * 0 == B4.rad * 0 + 0);
    W4.eval_win2 h 0 0 52;
    assert_norm (B4.rad - 0 == 64);
    assert_norm (pow2 0 == 1);
    assert_norm (rad == 52);
    Math.pow2_plus 12 52;
    Math.paren_mul_right (pow2 12) (pow2 52) (B4.vat h 1);
    Math.swap_mul (pow2 52) (B4.vat h 1);
    Math.paren_mul_right (pow2 12) (B4.vat h 1) (pow2 52);
    assert (W4.win (B4.eval h) (rad * 0) rad ==
            (B4.vat h 0 + (pow2 12 * B4.vat h 1) * pow2 52) % pow2 52);
    Math.lemma_mod_plus (B4.vat h 0) (pow2 12 * B4.vat h 1) (pow2 52)

let lw1 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == B4.nl /\ B4.bnd h B4.base)
          (ensures W4.win (B4.eval h) (rad * 1) rad ==
                   (B4.vat h 0 / pow2 52 + pow2 12 * B4.vat h 1) % pow2 52)
  = assert_norm (rad * 1 == B4.rad * 0 + 52);
    assert_norm (B4.rad - 52 == 12);
    W4.eval_win2 h 0 52 52

let lw2 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == B4.nl /\ B4.bnd h B4.base)
          (ensures W4.win (B4.eval h) (rad * 2) rad ==
                   (B4.vat h 1 / pow2 40 + pow2 24 * B4.vat h 2) % pow2 52)
  = assert_norm (rad * 2 == B4.rad * 1 + 40);
    assert_norm (B4.rad - 40 == 24);
    W4.eval_win2 h 1 40 52

let lw3 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == B4.nl /\ B4.bnd h B4.base)
          (ensures W4.win (B4.eval h) (rad * 3) rad ==
                   (B4.vat h 2 / pow2 28 + pow2 36 * B4.vat h 3) % pow2 52)
  = assert_norm (rad * 3 == B4.rad * 2 + 28);
    assert_norm (B4.rad - 28 == 36);
    W4.eval_win2 h 2 28 52

let lw4 (h: Seq.seq nat)
  : Lemma (requires Seq.length h == B4.nl /\ B4.bnd h B4.base)
          (ensures W4.win (B4.eval h) (rad * 4) rad == B4.vat h 3 / pow2 16)
  = assert_norm (rad * 4 == B4.rad * 3 + 16);
    assert_norm (B4.rad - 16 == 48);
    W4.eval_win2 h 3 16 52;
    assert (B4.vat h 4 == 0);
    assert_norm (B4.base == pow2 64);
    Math.lemma_div_lt_nat (B4.vat h 3) 64 16;
    Math.pow2_le_compat 52 48;
    Math.small_mod (B4.vat h 3 / pow2 16) (pow2 52)

(** The five limb indices, as a case split kept out of the context below. *)
let below5 (k: nat { k < nl })
  : Lemma (k == 0 \/ k == 1 \/ k == 2 \/ k == 3 \/ k == 4)
  = assert_norm (nl == 5)

let load_windows (h s: Seq.seq nat)
  : Lemma (requires Seq.length h == B4.nl /\ B4.bnd h B4.base /\ Seq.length s == nl /\
             Seq.index s 0 == B4.vat h 0 % pow2 52 /\
             Seq.index s 1 == (B4.vat h 0 / pow2 52 + pow2 12 * B4.vat h 1) % pow2 52 /\
             Seq.index s 2 == (B4.vat h 1 / pow2 40 + pow2 24 * B4.vat h 2) % pow2 52 /\
             Seq.index s 3 == (B4.vat h 2 / pow2 28 + pow2 36 * B4.vat h 3) % pow2 52 /\
             Seq.index s 4 == B4.vat h 3 / pow2 16)
          (ensures (forall (k: nat). k < nl ==>
                      Seq.index s k == W4.win (B4.eval h) (rad * k) rad))
  = let aux (k: nat { k < nl })
      : Lemma (Seq.index s k == W4.win (B4.eval h) (rad * k) rad)
      = assert_norm (nl == 5);
        if k = 0 then lw0 h
        else if k = 1 then lw1 h
        else if k = 2 then lw2 h
        else if k = 3 then lw3 h
        else begin
          below5 k;
          lw4 h
        end in
    Classical.forall_intro aux

(** {2 Storing}

    And the four sixty-four-bit limbs as windows of the five fifty-two-bit
    ones.  Offsets [(0,0)], [(1,12)], [(2,24)], [(3,36)]; sixty-four bits
    starting at most thirty-six into a fifty-two-bit limb reach at most
    bit one hundred, so these too span only two limbs. *)

let sw0 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B4.rad * 0) B4.rad ==
                   (vat s 0 / pow2 0 + pow2 52 * vat s 1) % pow2 64)
  = assert_norm (B4.rad * 0 == rad * 0 + 0);
    assert_norm (B4.rad == 64);
    assert_norm (rad - 0 == 52);
    W.eval_win2 s 0 0 64

let sw1 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B4.rad * 1) B4.rad ==
                   (vat s 1 / pow2 12 + pow2 40 * vat s 2) % pow2 64)
  = assert_norm (B4.rad * 1 == rad * 1 + 12);
    assert_norm (B4.rad == 64);
    assert_norm (rad - 12 == 40);
    W.eval_win2 s 1 12 64

let sw2 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B4.rad * 2) B4.rad ==
                   (vat s 2 / pow2 24 + pow2 28 * vat s 3) % pow2 64)
  = assert_norm (B4.rad * 2 == rad * 2 + 24);
    assert_norm (B4.rad == 64);
    assert_norm (rad - 24 == 28);
    W.eval_win2 s 2 24 64

let sw3 (s: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base)
          (ensures W.win (eval s) (B4.rad * 3) B4.rad ==
                   (vat s 3 / pow2 36 + pow2 16 * vat s 4) % pow2 64)
  = assert_norm (B4.rad * 3 == rad * 3 + 36);
    assert_norm (B4.rad == 64);
    assert_norm (rad - 36 == 16);
    W.eval_win2 s 3 36 64

(** The four limb indices, as a case split kept out of the context below. *)
let below4 (j: nat { j < B4.nl })
  : Lemma (j == 0 \/ j == 1 \/ j == 2 \/ j == 3)
  = assert_norm (B4.nl == 4)

let store_windows (s u: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base /\ Seq.length u == B4.nl /\
             Seq.index u 0 == (vat s 0 / pow2 0 + pow2 52 * vat s 1) % pow2 64 /\
             Seq.index u 1 == (vat s 1 / pow2 12 + pow2 40 * vat s 2) % pow2 64 /\
             Seq.index u 2 == (vat s 2 / pow2 24 + pow2 28 * vat s 3) % pow2 64 /\
             Seq.index u 3 == (vat s 3 / pow2 36 + pow2 16 * vat s 4) % pow2 64)
          (ensures (forall (j: nat). j < B4.nl ==>
                      Seq.index u j == W.win (eval s) (B4.rad * j) B4.rad))
  = let aux (j: nat { j < B4.nl })
      : Lemma (Seq.index u j == W.win (eval s) (B4.rad * j) B4.rad)
      = assert_norm (B4.nl == 4);
        if j = 0 then sw0 s
        else if j = 1 then sw1 s
        else if j = 2 then sw2 s
        else begin below4 j; sw3 s end in
    Classical.forall_intro aux

(** {2 The two ends}

    Loading: the five fifty-two-bit limbs are the successive windows of the
    sixty-four-bit number the bytes decode to.  Unlike Curve25519 the radix
    does not divide the width -- five times fifty-two is two hundred and
    sixty, four above what a load can produce -- so the bound wanted by
    [eval_windows] is slack rather than tight. *)

let load_ok (v: nat) (s: Seq.seq nat)
  : Lemma (requires v < pow2 256 /\ Seq.length s == nl /\
                    (forall (k: nat). k < nl ==> Seq.index s k == W4.win v (rad * k) rad))
          (ensures eval s == v /\ bnd s base)
  = assert_norm (rad * 5 == 260);
    Math.pow2_le_compat 260 256;
    W.eval_windows v s

(** Storing: the four sixty-four-bit limbs are the successive windows of
    the fifty-two-bit number, and [Spec.Bignum4] turns those into bytes. *)

let store_ok (v: nat) (u: Seq.seq nat)
  : Lemma (requires v < pow2 256 /\ Seq.length u == B4.nl /\
                    (forall (j: nat). j < B4.nl ==> Seq.index u j == W.win v (B4.rad * j) B4.rad))
          (ensures B4.eval u == v /\ B4.bnd u B4.base)
  = assert_norm (B4.rad * B4.nl == 256);
  W4.eval_windows v u

(** {2 The two ends, assembled}

    The implementation calls only these.  Everything above is folded into
    one lemma each so that the Pulse function is left with a single ghost
    call: the field module's ambient context is large enough that a proof
    spread over four steps there costs minutes. *)

let load_all (h s: Seq.seq nat)
  : Lemma (requires Seq.length h == B4.nl /\ B4.bnd h B4.base /\ Seq.length s == nl /\
             Seq.index s 0 == B4.vat h 0 % pow2 52 /\
             Seq.index s 1 == (B4.vat h 0 / pow2 52 + pow2 12 * B4.vat h 1) % pow2 52 /\
             Seq.index s 2 == (B4.vat h 1 / pow2 40 + pow2 24 * B4.vat h 2) % pow2 52 /\
             Seq.index s 3 == (B4.vat h 2 / pow2 28 + pow2 36 * B4.vat h 3) % pow2 52 /\
             Seq.index s 4 == B4.vat h 3 / pow2 16)
          (ensures eval s == B4.eval h /\ bnd s base)
  = B4.eval_bnd h;
    assert_norm (B4.rad * B4.nl == 256);
    load_windows h s;
    load_ok (B4.eval h) s

let store_all (s u: Seq.seq nat)
  : Lemma (requires Seq.length s == nl /\ bnd s base /\ eval s < pow2 256 /\
             Seq.length u == B4.nl /\
             Seq.index u 0 == (vat s 0 / pow2 0 + pow2 52 * vat s 1) % pow2 64 /\
             Seq.index u 1 == (vat s 1 / pow2 12 + pow2 40 * vat s 2) % pow2 64 /\
             Seq.index u 2 == (vat s 2 / pow2 24 + pow2 28 * vat s 3) % pow2 64 /\
             Seq.index u 3 == (vat s 3 / pow2 36 + pow2 16 * vat s 4) % pow2 64)
          (ensures B4.eval u == eval s /\ B4.bnd u B4.base)
  = store_windows s u;
    store_ok (eval s) u

#pop-options
