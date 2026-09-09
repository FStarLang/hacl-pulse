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

(** The operations a secret machine word supports, as a type class.

    HACL* wrote width-parametric code against [Lib.IntTypes.int_t t l], a type
    indexed by a width and a secrecy level, and then relied on a custom tactic
    to specialize the call graph.  hacl-pulse instead uses an ordinary F* type
    class and lets Custard monomorphize it: a dictionary binder is specialized
    by construction, so a hash written once against [word] becomes, in the
    generated C, one function per instance, calling that instance's operations
    directly with nothing left to indirect through.

    Only the operations that width-parametric code actually shares live here.
    A construction that needs something specific to one width -- a 64x64
    widening multiply, say -- should name that width rather than grow this
    class. *)
module Hacl.Secret.Word

module U32 = FStar.UInt32
module UInt = FStar.UInt
module S8 = Hacl.Secret.UInt8

class word (t: Type0) = {
  (** The width, in bits.  A field rather than a class index, so that
      [word Hacl.Secret.UInt32.t] is a complete statement of what a value is.
      Every width is a whole number of bytes, so serialization can talk about
      them; at least four, which is the narrowest word any of the algorithms
      uses and enough that a length always fits in the two words a hash
      reserves for it; and at most sixteen, because no machine word is wider
      than that.  Byte-wise code is not width-parametric and should name
      [Hacl.Secret.UInt8] directly. *)
  bits: n: pos { n % 8 == 0 /\ 32 <= n /\ n <= 128 };

  (** The width in bytes as a machine value, so that generic loops can index
      the bytes of a word without converting [bits] at runtime. *)
  nbytes: n: FStar.SizeT.t { FStar.SizeT.v n * 8 == bits };

  v: t -> GTot (x: nat { x < pow2 bits });

  v_extensional: (x: t) -> (y: t) -> Lemma (requires v x == v y) (ensures x == y);

  (** [v] is onto, in the ghost world.  Together with [v_extensional] this says
      a word *is* its value, which is what lets specifications be written as
      arithmetic on [nat] and implementations as machine operations, with the
      two related by a single equation.  It is [GTot], so it never reaches the
      generated code. *)
  of_v: (n: nat { n < pow2 bits }) -> GTot (r: t { v r == n });

  zero: r: t { v r == 0 };

  add_mod: (x: t) -> (y: t) -> (r: t { v r == (v x + v y) % pow2 bits });

  logand: (x: t) -> (y: t) -> (r: t { v r == UInt.logand #bits (v x) (v y) });
  logor:  (x: t) -> (y: t) -> (r: t { v r == UInt.logor  #bits (v x) (v y) });
  logxor: (x: t) -> (y: t) -> (r: t { v r == UInt.logxor #bits (v x) (v y) });
  lognot: (x: t) -> (r: t { v r == UInt.lognot #bits (v x) });

  (** Shift distances are public.  A variable-distance shift is not constant
      time on every microarchitecture, and in practice every distance in this
      library is a constant from a standards document. *)
  shift_left:  (x: t) -> (s: U32.t { U32.v s < bits }) -> (r: t { v r == (v x * pow2 (U32.v s)) % pow2 bits });
  shift_right: (x: t) -> (s: U32.t { U32.v s < bits }) -> (r: t { v r == v x / pow2 (U32.v s) });

  rotate_right: (x: t) -> (s: U32.t { 0 < U32.v s /\ U32.v s < bits }) ->
    (r: t { v r == v x / pow2 (U32.v s) + (v x % pow2 (U32.v s)) * pow2 (bits - U32.v s) });

  (** A public byte count, split into the low [bits] and the next [bits].
      Every length in this library is a [size_t]; BLAKE2's block counter is two
      words wide, which at 32 bits means splitting one.  There is no way to
      write that generically -- it is exactly a width-specific truncation -- so
      it is a method rather than a function over the others.

      The [% pow2 64] is not noise: [FStar.SizeT.fits] is abstract, so nothing
      says a [size_t] is only sixty-four bits, and the only conversion the
      standard library offers truncates to that width.  A caller that needs the
      split to be exact says so, by carrying [SZ.v x < pow2 64] -- which on
      every platform anyone compiles for is a tautology, and which the type
      system will not let us assume. *)
  of_sizet_lo: (x: FStar.SizeT.t) -> (r: t { v r == (FStar.SizeT.v x % pow2 64) % pow2 bits });
  of_sizet_hi: (x: FStar.SizeT.t) ->
    (r: t { v r == ((FStar.SizeT.v x % pow2 64) / pow2 bits) % pow2 bits });

  (** Widening and truncating conversions to bytes, which is all that generic
      big-endian (de)serialization needs. *)
  of_byte: (b: S8.t) -> (r: t { v r == S8.v b });
  to_byte: (x: t) -> (r: S8.t { S8.v r == v x % pow2 8 });
}

(** The width in bytes. *)
unfold
let bytes (#t: Type0) {| word t |} : n: pos { n * 8 == bits #t } = bits #t / 8
