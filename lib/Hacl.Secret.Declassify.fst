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

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module SA = Hacl.Secret.Array

friend Hacl.Secret.UInt8
friend Hacl.Secret.UInt32
friend Hacl.Secret.UInt64
friend Hacl.Secret.Array

let u8 x = x
let u32 x = x
let u64 x = x

let bool_of_mask mask = FStar.UInt8.eq mask 255uy

let u8_seq s = s
let u8_seq_index s i = ()
let u8_seq_slice s i j = ()
let u8_seq_append s1 s2 = ()
let u8_seq_classify_seq s = ()
let classify_seq_u8_seq s = ()

ghost fn of_secret (a: A.array U8.t) (#p: perm) (#s: erased (Seq.seq S8.t))
  requires A.pts_to (SA.secret a) #p s
  ensures A.pts_to a #p (u8_seq s)
{
  rewrite A.pts_to (SA.secret a) #p s as A.pts_to a #p (u8_seq s)
}
