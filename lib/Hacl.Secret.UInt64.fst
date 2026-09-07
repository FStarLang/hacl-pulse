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

module Hacl.Secret.UInt64

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module UInt = FStar.UInt
module Math = FStar.Math.Lemmas

let t = U64.t

let v x = U64.v x

let v_extensional x y = U64.v_inj x y

let classify x = x

let zero = 0UL
let ones = 0xffffffffffffffffUL

let add_mod x y = U64.add_mod x y
let sub_mod x y = U64.sub_mod x y
let mul_mod x y = U64.mul_mod x y

let logand x y = U64.logand x y
let logor  x y = U64.logor  x y
let logxor x y = U64.logxor x y
let lognot x   = U64.lognot x

let shift_left x s =
  UInt.shift_left_value_lemma #64 (v x) (U32.v s);
  U64.shift_left x s

let shift_right x s =
  UInt.shift_right_value_lemma #64 (v x) (U32.v s);
  U64.shift_right x s

(* A rotation is a shift each way, or-ed together.  The two halves occupy
   disjoint bits, so the or is an addition -- which is what makes the
   arithmetic postcondition provable without descending to bit vectors. *)
private
let rotate (x: t) (s: U32.t { 0 < U32.v s /\ U32.v s < 64 })
  : r: t { v r == v x / pow2 (U32.v s) + (v x % pow2 (U32.v s)) * pow2 (64 - U32.v s) }
  = let s' = U32.sub 64ul s in
    let hi = shift_left x s' in
    let lo = shift_right x s in
    (* [hi] keeps only the low [s] bits of [x], moved up to the top. *)
    Math.pow2_multiplication_modulo_lemma_2 (v x) 64 (U32.v s');
    Math.multiple_modulo_lemma (v x % pow2 (U32.v s)) (pow2 (U32.v s'));
    (* [lo] fits below the bits [hi] occupies, so the or is a sum. *)
    Math.lemma_div_lt (v x) 64 (U32.v s);
    UInt.logor_disjoint #64 (v hi) (v lo) (U32.v s');
    U64.logor hi lo

let rotate_right x s = rotate x s

let rotate_left x s = rotate x (U32.sub 64ul s)

(* At 8 and 32 bits the comparison masks widen to 64, where a difference
   cannot wrap, and read off the sign bit.  Here there is no wider machine
   type to widen to -- [FStar.UInt128] is emulated, and far too slow for a
   primitive -- so the same idea is applied to the two 32-bit halves and the
   results are combined.  Everything below is ordinary arithmetic on values
   that are provably 0 or 1; the point of writing it this way, rather than as
   the shorter sequence of bit tricks HACL* used, is that SMT can check it. *)

(* [lt_bit a b] is 1 when [a < b], for arguments that fit in 32 bits: their
   difference then cannot wrap past the sign bit. *)
private
let lt_bit (a b: U64.t { U64.v a < pow2 32 /\ U64.v b < pow2 32 })
  : r: U64.t { U64.v r == (if U64.v a < U64.v b then 1 else 0) }
  = let d = U64.sub_mod a b in
    UInt.shift_right_value_lemma #64 (U64.v d) 63;
    U64.shift_right d 63ul

private
let hi32 (x: U64.t) : r: U64.t { U64.v r == U64.v x / pow2 32 } =
  UInt.shift_right_value_lemma #64 (U64.v x) 32;
  U64.shift_right x 32ul

private
let lo32 (x: U64.t) : r: U64.t { U64.v r == U64.v x % pow2 32 } =
  let h = hi32 x in
  UInt.shift_left_value_lemma #64 (U64.v h) 32;
  Math.euclidean_division_definition (U64.v x) (pow2 32);
  U64.sub_mod x (U64.shift_left h 32ul)

(* Splitting a 64-bit comparison into two 32-bit ones is only lexicographic
   order on the halves; Z3 needs the multiplication spelled out. *)
private
let lemma_lt_split (xh xl yh yl: nat)
  : Lemma (requires xl < pow2 32 /\ yl < pow2 32)
          (ensures (xh * pow2 32 + xl < yh * pow2 32 + yl)
                   <==> (xh < yh \/ (xh == yh /\ xl < yl)))
  = if xh < yh then Math.lemma_mult_le_right (pow2 32) (xh + 1) yh
    else if yh < xh then Math.lemma_mult_le_right (pow2 32) (yh + 1) xh

(* [borrow x y] is 1 when [x < y]: compare the high halves, and fall back on
   the low halves when they agree. *)
#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"
private
let borrow (x y: t) : r: U64.t { U64.v r == (if v x < v y then 1 else 0) } =
  let xh = hi32 x in
  let yh = hi32 y in
  let xl = lo32 x in
  let yl = lo32 y in
  let lh = lt_bit xh yh in
  let gh = lt_bit yh xh in
  let ll = lt_bit xl yl in
  (* [eh] is 1 exactly when the high halves agree; [lh] and [gh] cannot both
     be 1, so neither subtraction wraps. *)
  let eh = U64.sub_mod (U64.sub_mod 1UL lh) gh in
  assert (U64.v eh == (if U64.v xh = U64.v yh then 1 else 0));
  let r = U64.add_mod lh (U64.mul_mod eh ll) in
  assert (U64.v r == (if U64.v xh < U64.v yh
                      || (U64.v xh = U64.v yh && U64.v xl < U64.v yl)
                      then 1 else 0));
  Math.euclidean_division_definition (v x) (pow2 32);
  Math.euclidean_division_definition (v y) (pow2 32);
  lemma_lt_split (U64.v xh) (U64.v xl) (U64.v yh) (U64.v yl);
  r
#pop-options

#push-options "--z3rlimit 200 --fuel 0 --ifuel 1"
let eq_mask x y =
  let d = U64.logxor x y in
  UInt.logxor_self #64 (v x);
  UInt.logxor_neq_nonzero #64 (v x) (v y);
  (* [d] is zero exactly when [x] and [y] agree, and is zero exactly when both
     its halves are. *)
  let dh = hi32 d in
  let dl = lo32 d in
  Math.euclidean_division_definition (U64.v d) (pow2 32);
  let z = U64.mul_mod (lt_bit dh 1UL) (lt_bit dl 1UL) in
  assert (U64.v z == (if U64.v d = 0 then 1 else 0));
  U64.sub_mod 0UL z
#pop-options

#push-options "--z3rlimit 100 --fuel 0 --ifuel 0"
let gte_mask x y = U64.sub_mod (borrow x y) 1UL

let lt_mask x y = U64.sub_mod 0UL (borrow x y)
#pop-options

#push-options "--z3rlimit 100 --fuel 0 --ifuel 1"
let select mask x y =
  UInt.lognot_lemma_1 #64;
  UInt.lognot_self #64 (UInt.zero 64);
  UInt.logand_lemma_1 #64 (v x);
  UInt.logand_lemma_2 #64 (v x);
  UInt.logand_lemma_1 #64 (v y);
  UInt.logand_lemma_2 #64 (v y);
  UInt.logand_commutative #64 (v mask) (v x);
  UInt.logand_commutative #64 (UInt.lognot #64 (v mask)) (v y);
  let l = U64.logand mask x in
  let r = U64.logand (U64.lognot mask) y in
  UInt.logor_lemma_1 #64 (v l);
  UInt.logor_lemma_1 #64 (v r);
  UInt.logor_commutative #64 (v l) (v r);
  U64.logor l r
#pop-options
