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

module Hacl.Secret.UInt32

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Cast = FStar.Int.Cast
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas

let t = U32.t

let v x = U32.v x

let v_extensional x y = U32.v_inj x y

let classify x = x

let zero = 0ul
let ones = 0xfffffffful

let add_mod x y = U32.add_mod x y
let sub_mod x y = U32.sub_mod x y
let mul_mod x y = U32.mul_mod x y

let logand x y = U32.logand x y
let logor  x y = U32.logor  x y
let logxor x y = U32.logxor x y
let lognot x   = U32.lognot x

let shift_left x s =
  UInt.shift_left_value_lemma #32 (v x) (U32.v s);
  U32.shift_left x s

let shift_right x s =
  UInt.shift_right_value_lemma #32 (v x) (U32.v s);
  U32.shift_right x s

(* A rotation is a shift each way, or-ed together.  The two halves occupy
   disjoint bits, so the or is an addition -- which is what makes the
   arithmetic postcondition provable without descending to bit vectors. *)
private
let rotate (x: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 32 })
  : r: t { v r == v x / pow2 (U32.v s) + (v x % pow2 (U32.v s)) * pow2 (32 - U32.v s) }
  = let s' = U32.sub 32ul s in
    let hi = shift_left x s' in
    let lo = shift_right x s in
    (* [hi] keeps only the low [s] bits of [x], moved up to the top. *)
    Math.pow2_multiplication_modulo_lemma_2 (v x) 32 (U32.v s');
    Math.multiple_modulo_lemma (v x % pow2 (U32.v s)) (pow2 (U32.v s'));
    (* [lo] fits below the bits [hi] occupies, so the or is a sum. *)
    Math.lemma_div_lt (v x) 32 (U32.v s);
    UInt.logor_disjoint #32 (v hi) (v lo) (U32.v s');
    U32.logor hi lo

let rotate_right x s = rotate x s

let rotate_left x s =
  rotate x (U32.sub 32ul s)

(* The masks below widen to 64 bits, where the difference of two 32-bit
   numbers cannot wrap, and read off the sign bit.  HACL* instead used a
   sequence of bit tricks at the native width; this is a couple of
   instructions longer and an order of magnitude easier to prove. *)

let eq_mask x y =
  let d = U32.logxor x y in
  UInt.logxor_self #32 (v x);
  UInt.logxor_neq_nonzero #32 (v x) (v y);
  (* [d] is zero exactly when [x] and [y] agree. *)
  let d64 = Cast.uint32_to_uint64 d in
  let m = U64.shift_right (U64.sub_mod d64 1UL) 63ul in
  UInt.shift_right_value_lemma #64 (U64.v (U64.sub_mod d64 1UL)) 63;
  U32.sub_mod 0ul (Cast.uint64_to_uint32 m)

(* [borrow x y] is 1 when [x < y] and 0 otherwise. *)
private
let borrow (x y: t) : m: U32.t { U32.v m == (if v x < v y then 1 else 0) } =
  let d = U64.sub_mod (Cast.uint32_to_uint64 x) (Cast.uint32_to_uint64 y) in
  UInt.shift_right_value_lemma #64 (U64.v d) 63;
  Cast.uint64_to_uint32 (U64.shift_right d 63ul)

let gte_mask x y = U32.sub_mod (borrow x y) 1ul

let lt_mask x y = U32.sub_mod 0ul (borrow x y)

let select mask x y =
  UInt.lognot_lemma_1 #32;
  UInt.lognot_self #32 (UInt.zero 32);
  UInt.logand_lemma_1 #32 (v x);
  UInt.logand_lemma_2 #32 (v x);
  UInt.logand_lemma_1 #32 (v y);
  UInt.logand_lemma_2 #32 (v y);
  UInt.logand_commutative #32 (v mask) (v x);
  UInt.logand_commutative #32 (UInt.lognot #32 (v mask)) (v y);
  let l = U32.logand mask x in
  let r = U32.logand (U32.lognot mask) y in
  UInt.logor_lemma_1 #32 (v l);
  UInt.logor_lemma_1 #32 (v r);
  UInt.logor_commutative #32 (v l) (v r);
  U32.logor l r
