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

module Hacl.Secret.Array

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8

friend Hacl.Secret.UInt8

let secret a = a

let secret_length a = ()

let secret_injective a b = ()

ghost fn to_secret (a: A.array U8.t) (#p: perm) (#s: erased (Seq.seq U8.t))
  requires A.pts_to a #p s
  ensures A.pts_to (secret a) #p (S8.classify_seq s)
{
  rewrite A.pts_to a #p s as A.pts_to (secret a) #p (S8.classify_seq s)
}
