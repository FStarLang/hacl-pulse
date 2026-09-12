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

(** The field GF(2^128) as GCM uses it, and GHASH.

    {2 Which GF(2^128)}

    There are two conventions for laying a 128-bit field element out in
    memory, and GCM uses the awkward one.  NIST SP 800-38D reads a block as a
    polynomial {i most significant coefficient first}: bit 0 of the string --
    the top bit of byte 0 -- is the coefficient of x^0, and bit 127 -- the
    bottom bit of byte 15 -- is the coefficient of x^127.  Multiplying by x
    therefore shifts the string {i right}, and the reduction constant
    [0xe1 00 .. 00] is the polynomial x^128 + x^7 + x^2 + x + 1 written in the
    same reversed order.  This is why every fast GHASH implementation begins
    by reflecting its inputs, and why a carry-less multiply instruction needs
    a fixup afterwards.

    {2 Why this is a block and not a number}

    An element is specified here as sixteen bytes, not as a number below
    2^128.  A number would make [gadd] a 128-bit xor, and F* has no cheap
    128-bit xor to compute with -- [FStar.UInt128] is a record of two 64-bit
    halves whose bitwise operations are as opaque as [FStar.UInt]'s.  More
    importantly, the implementation holds an element as sixteen bytes, so a
    byte-indexed specification is one the implementation can be proved equal
    to without a change of representation in between.  The bit-level
    operations that the multiplication needs -- testing bit [i] and shifting
    the whole string right by one -- are the only places where the byte layout
    shows through, and they are three lines each. *)
module Spec.GF128

open Spec.Byte

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas

let blocklen = 16

type block = Seq.lseq elem blocklen

let zero : block = Seq.create blocklen 0

let gadd (a b: block) : block =
  Seq.init blocklen (fun i -> Seq.index a i ^^ Seq.index b i)

(** Bit [i] of the 128-bit string: [i = 0] is the top bit of byte 0. *)
let bit (a: block) (i: nat { i < 128 }) : bool =
  (Seq.index a (i / 8) / pow2 (7 - i % 8)) % 2 = 1

(** One step of the shift: byte [i] of the result takes the bottom bit of
    byte [i - 1] as its top bit and drops its own bottom bit. *)
let shift_byte (a: block) (i: nat { i < blocklen }) : elem =
  let carry : elem = if i = 0 then 0 else (Seq.index a (i - 1) % 2) * 128 in
  let rest : elem = Seq.index a i / 2 in
  carry + rest

let shift_right_1 (a: block) : block =
  Seq.init blocklen (fun i -> shift_byte a i)

(** [R] of SP 800-38D 6.3: the polynomial x^128 + x^7 + x^2 + x + 1, less its
    leading term, in the reversed bit order. *)
let r_block : block =
  Seq.init blocklen (fun i -> (if i = 0 then 0xe1 else 0) <: elem)

(** The multiplication of SP 800-38D algorithm 1, verbatim.  [v] runs through
    [y], [x*y], [x^2*y], ... -- each step is a shift and, when the bit that
    falls off the end is set, a reduction -- and [z] accumulates the ones that
    [x] selects.

    The loop is constant-time as written: both branches are on bits of secret
    data, and the implementation turns each into a mask.  There is no table
    and no precomputation, which is the whole reason a portable GHASH can be
    written at all without opening the cache-timing door that the usual
    four-bit table method opens. *)
let rec gmul_loop (x: block) (z v: block) (i: nat { i <= 128 })
  : Tot block (decreases (128 - i)) =
  if i = 128 then z
  else
    let z' = if bit x i then gadd z v else z in
    let v' = if Seq.index v (blocklen - 1) % 2 = 0
             then shift_right_1 v
             else gadd (shift_right_1 v) r_block in
    gmul_loop x z' v' (i + 1)

let gmul (x y: block) : block = gmul_loop x zero y 0

(** {2 GHASH}

    GHASH is Horner's rule in this field: the blocks of the input are the
    coefficients of a polynomial evaluated at [h].  The input must already be
    a whole number of blocks; GCM pads it, and the padding is part of what is
    authenticated, so the padding belongs to [Spec.GCM] and not here. *)

let nblocks (data: Seq.seq elem) : nat = Seq.length data / blocklen

let blk (data: Seq.seq elem) (i: nat { (i + 1) * blocklen <= Seq.length data })
  : block =
  Math.lemma_mult_le_right blocklen (i + 1) (Seq.length data);
  Seq.slice data (i * blocklen) (i * blocklen + blocklen)

let rec ghash_acc (h: block) (data: Seq.seq elem { Seq.length data % blocklen == 0 })
                  (i: nat { i <= nblocks data })
  : Tot block (decreases i) =
  if i = 0 then zero
  else begin
    Math.lemma_mult_le_right blocklen i (nblocks data);
    Math.multiple_division_lemma (nblocks data) blocklen;
    gmul (gadd (ghash_acc h data (i - 1)) (blk data (i - 1))) h
  end

let ghash (h: block) (data: Seq.seq elem { Seq.length data % blocklen == 0 })
  : block = ghash_acc h data (nblocks data)
