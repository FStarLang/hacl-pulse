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

module Hacl.Secret.Declassify

friend Hacl.Secret.UInt8
friend Hacl.Secret.UInt32
friend Hacl.Secret.UInt64

let u8 x = x
let u32 x = x
let u64 x = x

let bool_of_mask mask = FStar.UInt8.eq mask 255uy
