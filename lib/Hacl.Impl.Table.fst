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

(** A compile-time table, as a slice.

    Every algorithm here has tables that are part of its definition: SHA-2's
    round constants and initial states, Keccak's iota constants and rho
    offsets, BLAKE2's initialization vector.  They belong in the program image,

      static const uint64_t Hacl_Hash_SHA3_rc_arr[24] = { 1ULL, ... };

    which is what [Pulse.Lib.GlobalArray] gives.  What is left over is the
    bookkeeping: the permission is fractional and it is never given back.

    That is not a leak.  The object has static storage duration, so there is
    nothing to return it to, and it is exactly why the emitted array can be
    [const].  But Pulse will not discard a permission silently, so every use
    of a table ends with a {!drop_table}. *)
module Hacl.Impl.Table

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module Seq = FStar.Seq

(** [n] is passed so that a caller that wants the length as a machine value --
    a loop bound, usually -- has one; the precondition checks it against the
    table's actual length. *)
inline_for_extraction
fn table (#t: Type0) (a: G.static_array t) (n: SZ.t)
requires pure (Seq.length (G.static_array_elems a) == SZ.v n)
returns arr: A.array t
ensures exists* (p: perm). A.pts_to arr #p (G.static_array_elems a)
{
  let arr = G.array_of_static_array a;
  with p v. assert (A.pts_to arr #p v);
  A.pts_to_len arr;
  arr
}

(** Let a table go.

    A caller of {!table} ends up holding a read permission it can neither use
    nor give back.  This is where it goes; it compiles to nothing. *)
ghost fn drop_table (#t: Type0) (s: A.array t) (#p: perm) (#v: Seq.seq t)
requires A.pts_to s #p v
ensures emp
{
  drop_ (A.pts_to s #p v)
}
