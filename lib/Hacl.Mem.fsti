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

(** Scratch memory that is wiped when it is released.

    Every array of secrets this library allocates goes through this module,
    and the build checks that (see [mk/memlint.pl]).  There are two kinds.

    {b Stack.}  A local array is declared as usual and then registered:

    {[
      let mut buf = [| z; n |];
      Mem.track buf;
      ...
      Mem.wipe buf n;
    ]}

    [track] produces the ghost obligation [must_wipe buf], and only [wipe]
    consumes it.  Pulse rejects a function that ends with an unconsumed
    resource, so a forgotten [wipe] is a type error ("Leftover resources:
    must_wipe buf"), not a leak.  Sizes are always compile-time constants or
    bounded by one; the caller never chooses the size of our stack frame.
    Wipe a buffer right after its last use rather than at the end of the
    function: the proof context then stays small, and the window in which
    the secret sits in memory is shorter.

    {b Heap.}  Anything large (Frodo matrices, big bignum tables) is
    allocated with [alloc], which returns the array together with
    [must_free a], and is released with [free], which wipes before calling
    [free(3)].  [must_free] can only be produced by [alloc], so [free] can
    only be applied to something [alloc] returned.  Allocation failure
    aborts the program.

    The wiping itself is in [c/Hacl_Mem.h]; it is trusted, and its
    postcondition (the contents are now unknown) is weaker than what it
    does.  It cannot be a verified loop: gcc and clang delete stores to an
    array that is about to die, and keeping them takes an optimization
    barrier, which would be trusted all the same.

    "Unknown" still means a sequence of [t]s, so [wipe] needs all-zero
    bytes to be a [t]: see [Hacl.Zeroable].  [A.pts_to_uninit] would avoid
    that, but [let mut x = [| v; n |]] must end its scope in [A.pts_to]
    (FStarLang/FStar#4777).  [free] needs neither: nothing is read back. *)
module Hacl.Mem

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Zeroable

module A = Pulse.Lib.Array
module SZ = FStar.SizeT

(** {2 Stack} *)

val must_wipe (#t: Type0) (a: A.array t) : slprop

ghost fn track (#t: Type0) (a: A.array t)
  ensures must_wipe a

fn wipe (#t: Type0) {| zeroable t |} (a: A.array t) (n: SZ.t) (#s: erased (Seq.seq t))
  requires A.pts_to a s ** must_wipe a ** pure (SZ.v n == A.length a)
  ensures exists* s'. A.pts_to a s'

(** Release the obligation without wiping.  This is for the handful of
    temporaries inside the hottest leaves (field multiplication, the Keccak
    state) that the C compiler keeps in registers: wiping them would take
    their address and force every intermediate value through memory, at up
    to twice the running time.  Whatever such a buffer leaves behind is in
    register spill slots, which no wipe of ours reaches anyway.  The build
    allows [nowipe] only in the functions listed in [mk/memlint.pl]. *)
ghost fn nowipe (#t: Type0) (a: A.array t)
  requires must_wipe a

(** {2 Heap} *)

val must_free (#t: Type0) (a: A.array t) : slprop

fn alloc (#t: Type0) (x: t) (n: SZ.t)
  returns a: A.array t
  ensures A.pts_to a (Seq.create (SZ.v n) x) ** must_free a **
          pure (A.length a == SZ.v n)

fn free (#t: Type0) (a: A.array t) (n: SZ.t) (#s: erased (Seq.seq t))
  requires A.pts_to a s ** must_free a ** pure (SZ.v n == A.length a)
