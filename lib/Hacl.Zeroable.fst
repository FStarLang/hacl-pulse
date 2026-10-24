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

module Hacl.Zeroable

module U128 = FStar.UInt128
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module S128 = Hacl.Secret.UInt128

[@@erasable]
noeq type zeroable (t: Type0) = { zv: t }

let zero_value d = d.zv

let zeroable_u8   = { zv = 0uy }
let zeroable_u16  = { zv = 0us }
let zeroable_u32  = { zv = 0ul }
let zeroable_u64  = { zv = 0uL }
let zeroable_u128 = { zv = U128.uint_to_t 0 }
let zeroable_sz   = { zv = 0sz }

let zeroable_s8   = { zv = S8.zero }
let zeroable_s16  = { zv = S16.zero }
let zeroable_s32  = { zv = S32.zero }
let zeroable_s64  = { zv = S64.zero }
let zeroable_s128 = { zv = S128.zero }

let zeroable_refine #b #d p _ = { zv = d.zv }
