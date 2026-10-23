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

(** Public byte buffers viewed as secret ones.

    A client whose data lives in [A.array U8.t] can hand it to the library,
    whose API takes [A.array S8.t], without copying: [secret a] is the same
    pointer, and [to_secret] retypes the permission.  Neither costs anything
    at run time.  The way back, which does weaken the constant-time
    discipline, is [Hacl.Secret.Declassify.of_secret]. *)
module Hacl.Secret.Array

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8

(** The same pointer, viewed as secret bytes. *)
inline_for_extraction
val secret (a: A.array U8.t) : A.array S8.t

val secret_length (a: A.array U8.t)
  : Lemma (A.length (secret a) == A.length a) [SMTPat (A.length (secret a))]

val secret_injective (a b: A.array U8.t)
  : Lemma (requires secret a == secret b) (ensures a == b)

ghost fn to_secret (a: A.array U8.t) (#p: perm) (#s: erased (Seq.seq U8.t))
  requires A.pts_to a #p s
  ensures A.pts_to (secret a) #p (S8.classify_seq s)
