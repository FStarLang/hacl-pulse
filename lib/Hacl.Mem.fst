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

module Hacl.Mem

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Zeroable

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT

let must_wipe #t a = emp

ghost fn track (#t: Type0) (a: A.array t)
  ensures must_wipe a
{
  fold (must_wipe a)
}

[@@custard_extern "Hacl_Mem_wipe"; custard_c_header "Hacl_Mem.h"]
assume val memzero (#t: Type0) {| zeroable t |} (a: A.array t) (n: SZ.t) (#s: erased (Seq.seq t))
  : stt unit (requires A.pts_to a s ** pure (SZ.v n == A.length a))
             (ensures fun _ -> exists* s'. A.pts_to a s')

fn wipe (#t: Type0) {| zeroable t |} (a: A.array t) (n: SZ.t) (#s: erased (Seq.seq t))
  requires A.pts_to a s ** must_wipe a ** pure (SZ.v n == A.length a)
  ensures exists* s'. A.pts_to a s'
{
  unfold (must_wipe a);
  memzero a n
}

ghost fn nowipe (#t: Type0) (a: A.array t)
  requires must_wipe a
{
  unfold (must_wipe a)
}

(* FStarLang/hacl-pulse#9: wiping must not let a proof read back a value
   of a type that all-zero bytes do not represent. *)
type one = x: FStar.UInt8.t { FStar.UInt8.v x == 1 }

[@@expect_failure]
fn wipe_refined (a: A.array one) (#s: erased (Seq.seq one))
  requires A.pts_to a s ** must_wipe a ** pure (A.length a == 1)
  ensures exists* s'. A.pts_to a s'
{
  wipe a 1sz
}

[@@expect_failure]
let zeroable_one : zeroable one =
  zeroable_refine (fun x -> FStar.UInt8.v x == 1) ()

(** [a] is the array view of a whole [Vec], i.e. of a [malloc] result. *)
let must_free #t a =
  pure (exists (v: V.vec t). V.vec_to_array v == a /\ V.is_full_vec v)

fn alloc (#t: Type0) (x: t) (n: SZ.t)
  returns a: A.array t
  ensures A.pts_to a (Seq.create (SZ.v n) x) ** must_free a **
          pure (A.length a == SZ.v n)
{
  let h = V.alloc x n;
  V.to_array_pts_to h;
  fold (must_free (V.vec_to_array h));
  V.vec_to_array h
}

[@@custard_extern "Hacl_Mem_free"; custard_c_header "Hacl_Mem.h"]
assume val wipe_and_free (#t: Type0) (a: A.array t) (n: SZ.t) (#s: erased (Seq.seq t))
  : stt unit (requires A.pts_to a s ** must_free a ** pure (SZ.v n == A.length a))
             (ensures fun _ -> emp)

fn free (#t: Type0) (a: A.array t) (n: SZ.t) (#s: erased (Seq.seq t))
  requires A.pts_to a s ** must_free a ** pure (SZ.v n == A.length a)
{
  wipe_and_free a n
}
