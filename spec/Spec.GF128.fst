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

(** {2 GHASH as a fold}

    An implementation cannot materialise the concatenation GCM hashes: the
    padded associated data, the padded ciphertext and the length block live in
    three different places, and the padding lives nowhere at all.  So GHASH is
    restated here as a fold over an explicit accumulator, [ghash_upd], with
    the one law an implementation needs -- hashing a concatenation is hashing
    one part and then the other.  The driver then calls it once per piece and
    never builds the concatenation. *)

let rec ghash_from (h: block) (acc: block)
                   (data: Seq.seq elem { Seq.length data % blocklen == 0 })
                   (i: nat { i <= nblocks data })
  : Tot block (decreases i) =
  if i = 0 then acc
  else begin
    Math.lemma_mult_le_right blocklen i (nblocks data);
    Math.multiple_division_lemma (nblocks data) blocklen;
    gmul (gadd (ghash_from h acc data (i - 1)) (blk data (i - 1))) h
  end

(** Fold the whole of [data] into [acc]. *)
let ghash_upd (h: block) (acc: block)
              (data: Seq.seq elem { Seq.length data % blocklen == 0 })
  : block = ghash_from h acc data (nblocks data)

let rec ghash_from_zero (h: block)
                        (data: Seq.seq elem { Seq.length data % blocklen == 0 })
                        (i: nat { i <= nblocks data })
  : Lemma (ensures ghash_from h zero data i == ghash_acc h data i) (decreases i)
  = if i = 0 then () else ghash_from_zero h data (i - 1)

let ghash_is_upd (h: block) (data: Seq.seq elem { Seq.length data % blocklen == 0 })
  : Lemma (ghash h data == ghash_upd h zero data)
  = ghash_from_zero h data (nblocks data)

(** One step of the fold, which is what a loop body does. *)
let ghash_from_step (h acc: block)
                    (data: Seq.seq elem { Seq.length data % blocklen == 0 })
                    (k: nat { k + 1 <= nblocks data })
  : Lemma ((k + 1) * blocklen <= Seq.length data /\
           ghash_from h acc data (k + 1) ==
             gmul (gadd (ghash_from h acc data k) (blk data k)) h)
  = Math.lemma_mult_le_right blocklen (k + 1) (nblocks data);
    Math.multiple_division_lemma (nblocks data) blocklen

(** {3 The concatenation law} *)

let nblocks_append (d1 d2: Seq.seq elem)
  : Lemma (requires Seq.length d1 % blocklen == 0 /\ Seq.length d2 % blocklen == 0)
          (ensures Seq.length (Seq.append d1 d2) % blocklen == 0 /\
                   nblocks (Seq.append d1 d2) == nblocks d1 + nblocks d2)
  = Seq.lemma_len_append d1 d2;
    Math.modulo_distributivity (Seq.length d1) (Seq.length d2) blocklen;
    Math.lemma_div_exact (Seq.length d1) blocklen;
    Math.lemma_div_exact (Seq.length d2) blocklen;
    Math.division_addition_lemma (Seq.length d2) blocklen (nblocks d1)

let blk_append_left (d1 d2: Seq.seq elem)
                    (k: nat { (k + 1) * blocklen <= Seq.length d1 })
  : Lemma ((k + 1) * blocklen <= Seq.length (Seq.append d1 d2) /\
           blk (Seq.append d1 d2) k == blk d1 k)
  = Seq.lemma_len_append d1 d2;
    Math.lemma_mult_le_right blocklen (k + 1) (Seq.length d1);
    Seq.lemma_eq_intro (blk (Seq.append d1 d2) k) (blk d1 k)

let blk_append_right (d1 d2: Seq.seq elem)
                     (k: nat { (k + 1) * blocklen <= Seq.length d2 })
  : Lemma (requires Seq.length d1 % blocklen == 0)
          (ensures (nblocks d1 + k + 1) * blocklen <= Seq.length (Seq.append d1 d2) /\
                   blk (Seq.append d1 d2) (nblocks d1 + k) == blk d2 k)
  = Seq.lemma_len_append d1 d2;
    Math.lemma_div_exact (Seq.length d1) blocklen;
    Math.distributivity_add_left (nblocks d1) (k + 1) blocklen;
    Math.distributivity_add_left (nblocks d1) k blocklen;
    Seq.lemma_eq_intro (blk (Seq.append d1 d2) (nblocks d1 + k)) (blk d2 k)

let rec ghash_from_prefix (h acc: block) (d1 d2: Seq.seq elem)
                          (i: nat { i <= nblocks d1 })
  : Lemma (requires Seq.length d1 % blocklen == 0 /\ Seq.length d2 % blocklen == 0)
          (ensures Seq.length (Seq.append d1 d2) % blocklen == 0 /\
                   i <= nblocks (Seq.append d1 d2) /\
                   ghash_from h acc (Seq.append d1 d2) i == ghash_from h acc d1 i)
          (decreases i)
  = nblocks_append d1 d2;
    if i = 0 then ()
    else begin
      ghash_from_prefix h acc d1 d2 (i - 1);
      Math.lemma_mult_le_right blocklen i (nblocks d1);
      Math.multiple_division_lemma (nblocks d1) blocklen;
      blk_append_left d1 d2 (i - 1)
    end

let rec ghash_from_append (h acc: block) (d1 d2: Seq.seq elem)
                          (j: nat { j <= nblocks d2 })
  : Lemma (requires Seq.length d1 % blocklen == 0 /\ Seq.length d2 % blocklen == 0)
          (ensures Seq.length (Seq.append d1 d2) % blocklen == 0 /\
                   nblocks d1 + j <= nblocks (Seq.append d1 d2) /\
                   ghash_from h acc (Seq.append d1 d2) (nblocks d1 + j) ==
                     ghash_from h (ghash_upd h acc d1) d2 j)
          (decreases j)
  = nblocks_append d1 d2;
    if j = 0 then ghash_from_prefix h acc d1 d2 (nblocks d1)
    else begin
      ghash_from_append h acc d1 d2 (j - 1);
      Math.lemma_mult_le_right blocklen j (nblocks d2);
      Math.multiple_division_lemma (nblocks d2) blocklen;
      Math.lemma_mult_le_right blocklen (nblocks d1 + j) (nblocks (Seq.append d1 d2));
      Math.multiple_division_lemma (nblocks (Seq.append d1 d2)) blocklen;
      blk_append_right d1 d2 (j - 1);
      ghash_from_step h acc (Seq.append d1 d2) (nblocks d1 + j - 1);
      ghash_from_step h (ghash_upd h acc d1) d2 (j - 1)
    end

(** Hashing [d1 ++ d2] is hashing [d1] and then hashing [d2]. *)
let ghash_upd_append (h acc: block) (d1 d2: Seq.seq elem)
  : Lemma (requires Seq.length d1 % blocklen == 0 /\ Seq.length d2 % blocklen == 0)
          (ensures Seq.length (Seq.append d1 d2) % blocklen == 0 /\
                   ghash_upd h acc (Seq.append d1 d2) ==
                     ghash_upd h (ghash_upd h acc d1) d2)
  = nblocks_append d1 d2;
    ghash_from_append h acc d1 d2 (nblocks d2)
