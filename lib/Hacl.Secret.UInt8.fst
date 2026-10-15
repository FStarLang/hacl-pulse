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

module Hacl.Secret.UInt8

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas

let t = U8.t

let v x = U8.v x

let v_extensional x y = U8.v_inj x y

let classify x = x

let zero = 0uy
let ones = 255uy

let add_mod x y = U8.add_mod x y
let sub_mod x y = U8.sub_mod x y
let mul_mod x y = U8.mul_mod x y

let logand x y = U8.logand x y
let logor  x y = U8.logor  x y
let logxor x y = U8.logxor x y
let lognot x   = U8.lognot x

let shift_left x s =
  UInt.shift_left_value_lemma #8 (v x) (U32.v s);
  U8.shift_left x s

let shift_right x s =
  UInt.shift_right_value_lemma #8 (v x) (U32.v s);
  U8.shift_right x s

(* A rotation is a shift each way, or-ed together.  The two halves occupy
   disjoint bits, so the or is an addition -- which is what makes the
   arithmetic postcondition provable without descending to bit vectors. *)
private
let rotate (x: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 8 })
  : r: t { v r == v x / pow2 (U32.v s) + (v x % pow2 (U32.v s)) * pow2 (8 - U32.v s) }
  = let s' = U32.sub 8ul s in
    let hi = shift_left x s' in
    let lo = shift_right x s in
    Math.pow2_multiplication_modulo_lemma_2 (v x) 8 (U32.v s');
    Math.multiple_modulo_lemma (v x % pow2 (U32.v s)) (pow2 (U32.v s'));
    Math.lemma_div_lt (v x) 8 (U32.v s);
    UInt.logor_disjoint #8 (v hi) (v lo) (U32.v s');
    U8.logor hi lo

let rotate_right x s = rotate x s

let rotate_left x s = rotate x (U32.sub 8ul s)

(* The masks below all follow the same recipe: widen to 64 bits, where the
   difference of two 8-bit numbers cannot wrap, and read off the sign bit.
   HACL* instead used a sequence of bit tricks at the native width, which is
   two instructions shorter and an order of magnitude harder to prove; at this
   width the widening is free, since the compiler has to materialise a 32-bit
   register for the arithmetic anyway. *)

(* The sign bit of [d - 1], for an 8-bit [d] widened to 64 bits. *)
private
let is_zero_bit_lemma (d: U8.t)
  : Lemma (U8.v (Cast.uint64_to_uint8
                  (U64.shift_right (U64.sub_mod (Cast.uint8_to_uint64 d) 1UL) 63ul))
           == (if U8.v d = 0 then 1 else 0))
  = let e = U64.sub_mod (Cast.uint8_to_uint64 d) 1UL in
    let m = U64.shift_right e 63ul in
    UInt.shift_right_value_lemma #64 (U64.v e) 63;
    if U8.v d = 0 then begin
      assert_norm ((0 - 1) % pow2 64 == pow2 64 - 1);
      assert_norm ((pow2 64 - 1) / pow2 63 == 1)
    end else begin
      Math.small_mod (U8.v d - 1) (pow2 64);
      Math.small_div (U8.v d - 1) (pow2 63)
    end;
    Math.small_mod (U64.v m) (pow2 8)

let eq_mask x y =
  let d = U8.logxor x y in
  UInt.logxor_self #8 (v x);
  UInt.logxor_neq_nonzero #8 (v x) (v y);
  (* [d] is zero exactly when [x] and [y] agree. *)
  let d64 = Cast.uint8_to_uint64 d in
  let m = U64.shift_right (U64.sub_mod d64 1UL) 63ul in
  is_zero_bit_lemma d;
  U8.sub_mod 0uy (Cast.uint64_to_uint8 m)

(* [borrow x y] is 1 when [x < y] and 0 otherwise. *)
private
let borrow (x y: t) : m: U8.t { U8.v m == (if v x < v y then 1 else 0) } =
  let d = U64.sub_mod (Cast.uint8_to_uint64 x) (Cast.uint8_to_uint64 y) in
  UInt.shift_right_value_lemma #64 (U64.v d) 63;
  Cast.uint64_to_uint8 (U64.shift_right d 63ul)

let gte_mask x y = U8.sub_mod (borrow x y) 1uy

let lt_mask x y = U8.sub_mod 0uy (borrow x y)

let select mask x y =
  UInt.lognot_lemma_1 #8;
  UInt.lognot_self #8 (UInt.zero 8);
  UInt.logand_lemma_1 #8 (v x);
  UInt.logand_lemma_2 #8 (v x);
  UInt.logand_lemma_1 #8 (v y);
  UInt.logand_lemma_2 #8 (v y);
  UInt.logand_commutative #8 (v mask) (v x);
  UInt.logand_commutative #8 (UInt.lognot #8 (v mask)) (v y);
  let l = U8.logand mask x in
  let r = U8.logand (U8.lognot mask) y in
  UInt.logor_lemma_1 #8 (v l);
  UInt.logor_lemma_1 #8 (v r);
  UInt.logor_commutative #8 (v l) (v r);
  U8.logor l r
