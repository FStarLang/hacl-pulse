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

module Hacl.Secret.UInt128

(* [mul_wide] is the one operation here that spans two widths, and it cannot
   be written through [Hacl.Secret.Cast]: widening both arguments and
   multiplying is not available, because [FStar.UInt128] deliberately has no
   128 x 128 multiply.  So this module has to see that a secret [uint64] is
   a [FStar.UInt64.t].  That makes it the third member of the friend set,
   after [Hacl.Secret.Cast] and [Hacl.Secret.Declassify]; the set is still
   small enough to read, and still shows up in the build log. *)
friend Hacl.Secret.UInt64

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128
module Math = FStar.Math.Lemmas

let t = U128.t

let v x = U128.v x

let v_extensional x y = U128.v_inj x y

let zero = U128.uint_to_t 0

(* Written as a shift rather than as a literal: [pow2 64] is not a C
   constant, and the shift is folded at compile time anyway. *)
let pow2_64 =
  Math.pow2_lt_compat 128 64;
  Math.small_modulo_lemma_1 (pow2 64) (pow2 128);
  U128.shift_left (U128.uint_to_t 1) 64ul

let add_mod x y = U128.add_mod x y
let sub_mod x y = U128.sub_mod x y

let mul_wide x y = U128.mul_wide x y

let logand x y = U128.logand x y
let logor  x y = U128.logor  x y
let logxor x y = U128.logxor x y
let lognot x   = U128.lognot x

let shift_left x s = U128.shift_left x s
let shift_right x s = U128.shift_right x s
