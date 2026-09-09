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

    which is what [Pulse.Lib.GlobalArray] gives.  The rest of this library
    works on slices, so the one thing missing is the conversion, and it is the
    same three lines every time.

    The permission is fractional and it is never given back.  That is not a
    leak: the object has static storage duration, so there is nothing to
    return it to, and it is exactly why the emitted array can be [const].  A
    caller therefore does *not* pair this with [S.to_array], which is the one
    visible difference from a stack table. *)
module Hacl.Impl.Table

#lang-pulse

open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module A = Pulse.Lib.Array
module G = Pulse.Lib.GlobalArray
module SZ = FStar.SizeT
module Seq = FStar.Seq

(** [n] is passed rather than derived because [S.from_array] wants the length
    as a [size_t] and the only length in scope is a [nat] under [Seq.length].
    Callers write the literal, and the precondition checks it. *)
inline_for_extraction
fn table (#t: Type0) (a: G.static_array t) (n: SZ.t)
requires pure (Seq.length (G.static_array_elems a) == SZ.v n)
returns s: S.slice t
ensures exists* (p: perm). S.pts_to s #p (G.static_array_elems a)
{
  let arr = G.array_of_static_array a;
  with p v. assert (A.pts_to arr #p v);
  A.pts_to_len arr;
  let s = S.from_array arr #p n;
  drop_ (S.is_from_array arr s);
  s
}

(** Let a table go.

    A caller of {!table} ends up holding a read permission it can neither use
    nor give back, and Pulse will not discard it silently, so every use of a
    table ends with one of these.  It is the counterpart of the [S.to_array]
    that a stack table needs -- one line either way, and this one compiles to
    nothing. *)
ghost fn drop_table (#t: Type0) (s: S.slice t) (#p: perm) (#v: Seq.seq t)
requires S.pts_to s #p v
ensures emp
{
  drop_ (S.pts_to s #p v)
}
