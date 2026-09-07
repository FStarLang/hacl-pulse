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

(** The instances of [Hacl.Secret.Word.word].

    Kept apart from the per-width modules so that those stay independent of
    each other and of the class.  There is deliberately no 8-bit instance:
    byte-wise code is not width-parametric, and admitting one would force every
    generic shift to carry a side condition. *)
module Hacl.Secret.Word.Instances

open Hacl.Secret.Word

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Cast = Hacl.Secret.Cast

instance word_u32 : word S32.t = {
  bits = 32;
  nbytes = 4sz;
  v = S32.v;
  v_extensional = (fun x y -> S32.v_extensional x y);
  of_v = (fun n -> S32.classify (U32.uint_to_t n));
  zero = S32.zero;
  add_mod = S32.add_mod;
  logand = S32.logand;
  logor = S32.logor;
  logxor = S32.logxor;
  lognot = S32.lognot;
  shift_left = S32.shift_left;
  shift_right = S32.shift_right;
  rotate_right = S32.rotate_right;
  of_byte = Cast.u8_to_u32;
  to_byte = Cast.u32_to_u8;
}

instance word_u64 : word S64.t = {
  bits = 64;
  nbytes = 8sz;
  v = S64.v;
  v_extensional = (fun x y -> S64.v_extensional x y);
  of_v = (fun n -> S64.classify (U64.uint_to_t n));
  zero = S64.zero;
  add_mod = S64.add_mod;
  logand = S64.logand;
  logor = S64.logor;
  logxor = S64.logxor;
  lognot = S64.lognot;
  shift_left = S64.shift_left;
  shift_right = S64.shift_right;
  rotate_right = S64.rotate_right;
  of_byte = Cast.u8_to_u64;
  to_byte = Cast.u64_to_u8;
}
