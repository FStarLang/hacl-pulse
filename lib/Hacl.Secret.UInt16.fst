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

module Hacl.Secret.UInt16

friend Hacl.Secret.UInt8

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas

let t = U16.t

let v x = U16.v x

let v_extensional x y = U16.v_inj x y

let classify x = x

let zero = 0us
let one = 1us
let ones = 0xffffus

let add_mod x y = U16.add_mod x y
let sub_mod x y = U16.sub_mod x y
let mul_mod x y = U16.mul_mod x y

let logand x y = U16.logand x y
let logor  x y = U16.logor  x y
let logxor x y = U16.logxor x y
let lognot x   = U16.lognot x

let shift_left x s =
  UInt.shift_left_value_lemma #16 (v x) (U32.v s);
  U16.shift_left x s

let shift_right x s =
  UInt.shift_right_value_lemma #16 (v x) (U32.v s);
  U16.shift_right x s

(* [2^n - 1] computed in 32 bits, so that [n = 16] -- which Frodo's
   [logq = 16] parameter sets need -- is not a special case. *)
let mask_low n =
  Math.pow2_le_compat 16 (U32.v n);
  UInt.shift_left_value_lemma #32 1 (U32.v n);
  Math.small_modulo_lemma_1 (pow2 (U32.v n)) (pow2 32);
  let m = U32.sub (U32.shift_left 1ul n) 1ul in
  Math.small_modulo_lemma_1 (pow2 (U32.v n) - 1) (pow2 16);
  Cast.uint32_to_uint16 m

(* [UInt.logand_mask] does not cover the two ends: at [n = 0] the mask is
   zero and at [n = 16] it is all ones, and both have their own lemma. *)
let logand_mask_low x n =
  if U32.v n = 0 then
    UInt.logand_lemma_1 #16 (v x)
  else if U32.v n = 16 then begin
    UInt.logand_lemma_2 #16 (v x);
    Math.small_modulo_lemma_1 (v x) (pow2 16)
  end else
    UInt.logand_mask #16 (v x) (U32.v n)

(* All three masks widen to 32 bits, where neither a difference nor a
   decrement can wrap, and read off a single bit.  Cheaper to prove than the
   native-width bit tricks, and the compiler emits the same thing. *)

let eq_mask x y =
  let d = U16.logxor x y in
  UInt.logxor_self #16 (v x);
  UInt.logxor_neq_nonzero #16 (v x) (v y);
  let d32 = Cast.uint16_to_uint32 d in
  let m = U32.shift_right (U32.sub_mod d32 1ul) 31ul in
  UInt.shift_right_value_lemma #32 (U32.v (U32.sub_mod d32 1ul)) 31;
  U16.sub_mod 0us (Cast.uint32_to_uint16 m)

private
let borrow (x y: t) : m: U16.t { U16.v m == (if v x < v y then 1 else 0) } =
  let d = U32.sub_mod (Cast.uint16_to_uint32 x) (Cast.uint16_to_uint32 y) in
  UInt.shift_right_value_lemma #32 (U32.v d) 31;
  Cast.uint32_to_uint16 (U32.shift_right d 31ul)

let gte_mask x y = U16.sub_mod (borrow x y) 1us

let lt_mask x y = U16.sub_mod 0us (borrow x y)

let select mask x y =
  UInt.lognot_lemma_1 #16;
  UInt.lognot_self #16 (UInt.zero 16);
  UInt.logand_lemma_1 #16 (v x);
  UInt.logand_lemma_2 #16 (v x);
  UInt.logand_lemma_1 #16 (v y);
  UInt.logand_lemma_2 #16 (v y);
  UInt.logand_commutative #16 (v mask) (v x);
  UInt.logand_commutative #16 (UInt.lognot #16 (v mask)) (v y);
  let l = U16.logand mask x in
  let r = U16.logand (U16.lognot mask) y in
  UInt.logor_lemma_1 #16 (v l);
  UInt.logor_lemma_1 #16 (v r);
  UInt.logor_commutative #16 (v l) (v r);
  U16.logor l r

let lo x =
  Math.lemma_mod_lt (v x) (pow2 8);
  Cast.uint16_to_uint8 x

let hi x =
  UInt.shift_right_value_lemma #16 (v x) 8;
  Math.lemma_div_lt (v x) 16 8;
  Cast.uint16_to_uint8 (U16.shift_right x 8ul)

let of_bytes_le l h =
  let h16 = Cast.uint8_to_uint16 h in
  UInt.shift_left_value_lemma #16 (U8.v h) 8;
  Math.small_modulo_lemma_1 (U8.v h * pow2 8) (pow2 16);
  let hs = U16.shift_left h16 8ul in
  let l16 = Cast.uint8_to_uint16 l in
  UInt.logor_disjoint #16 (U16.v hs) (U16.v l16) 8;
  U16.logor hs l16

let of_bytes_le_lo_hi x =
  Math.euclidean_division_definition (v x) (pow2 8)
