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

(** The counter of counter mode.

    [inc32] is the standard incrementing function of NIST SP 800-38A: the
    last four bytes of the block, read as a big-endian thirty-two bit
    number, plus one, wrapping.  It is written here as a carry chain over
    the four bytes with the carry itself a mask, so that a counter which
    happens to be secret leaks nothing through a branch.  The alternative --
    loading the four bytes into a thirty-two bit word -- would need a
    secret-integer cast for no gain.

    It lives in its own module, below [Hacl.AES.NI], because the vectorised
    counter-mode step needs to advance the counter itself: it produces four
    consecutive counter blocks in registers before running any of them
    through the cipher. *)
module Hacl.AES.Counter

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module SHANI = Spec.SHANI
module CL = Spec.CLMUL
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The pure side of [inc32]} *)

(** Four bytes, most significant first, are recovered from the number they
    make: the standard digit extraction, spelled out because the numbers are
    the only place division appears in this file. *)
let byte_at_digits (a b c d: elem)
  : Lemma (let x = a * 16777216 + b * 65536 + c * 256 + d in
           x < 4294967296 /\
           byte_at x 0 == d /\ byte_at x 8 == c /\
           byte_at x 16 == b /\ byte_at x 24 == a)
  = assert_norm (pow2 0 == 1);
    assert_norm (pow2 8 == 256);
    assert_norm (pow2 16 == 65536);
    assert_norm (pow2 24 == 16777216);
    let x = a * 16777216 + b * 65536 + c * 256 + d in
    let y = a * 65536 + b * 256 + c in
    let z = a * 256 + b in
    assert (x == d + y * 256);
    Math.lemma_div_plus d y 256; Math.small_div d 256;
    Math.lemma_mod_plus d y 256; Math.small_mod d 256;
    assert (y == c + z * 256);
    Math.lemma_div_plus c z 256; Math.small_div c 256;
    Math.lemma_mod_plus c z 256; Math.small_mod c 256;
    Math.lemma_div_plus b a 256; Math.small_div b 256;
    Math.lemma_mod_plus b a 256; Math.small_mod b 256;
    Math.division_multiplication_lemma x 256 256;
    Math.division_multiplication_lemma x 65536 256;
    Math.small_mod a 256

#push-options "--z3rlimit 400"

(** The carry chain is the increment.  [c15] is the carry out of the last
    byte, [c14] out of the last two, and so on: each is the previous carry
    kept only where the byte was already all ones. *)
let inc32_bytes (b: block) (r12 r13 r14 r15: elem)
  : Lemma (requires
      (let x12 = Seq.index b 12 in let x13 = Seq.index b 13 in
       let x14 = Seq.index b 14 in let x15 = Seq.index b 15 in
       let c15 = (if x15 = 255 then 1 else 0) in
       let c14 = (if x14 = 255 then c15 else 0) in
       let c13 = (if x13 = 255 then c14 else 0) in
       r15 == (x15 + 1) % 256 /\ r14 == (x14 + c15) % 256 /\
       r13 == (x13 + c14) % 256 /\ r12 == (x12 + c13) % 256))
    (ensures
      (forall (j: nat). j < 12 ==> Seq.index (inc32 b) j == Seq.index b j) /\
      Seq.index (inc32 b) 12 == r12 /\ Seq.index (inc32 b) 13 == r13 /\
      Seq.index (inc32 b) 14 == r14 /\ Seq.index (inc32 b) 15 == r15)
  = assert_norm (pow2 32 == 4294967296);
    let x12 = Seq.index b 12 in let x13 = Seq.index b 13 in
    let x14 = Seq.index b 14 in let x15 = Seq.index b 15 in
    byte_at_digits x12 x13 x14 x15;
    let n = be32 b in
    assert (n == x12 * 16777216 + x13 * 65536 + x14 * 256 + x15);
    if x15 < 255 then begin
      byte_at_digits x12 x13 x14 (x15 + 1);
      Math.small_mod (n + 1) 4294967296
    end else if x14 < 255 then begin
      byte_at_digits x12 x13 (x14 + 1) 0;
      Math.small_mod (n + 1) 4294967296
    end else if x13 < 255 then begin
      byte_at_digits x12 (x13 + 1) 0 0;
      Math.small_mod (n + 1) 4294967296
    end else if x12 < 255 then begin
      byte_at_digits (x12 + 1) 0 0 0;
      Math.small_mod (n + 1) 4294967296
    end else begin
      byte_at_digits 0 0 0 0;
      Math.lemma_mod_plus 0 1 4294967296
    end

#pop-options

(** {2 The increment} *)

(** [--z3refresh]: by the time the carry chain is reached the solver has
    seen every digit-extraction lemma above, all of them divisions by powers
    of two on concrete moduli, and the state they leave behind makes this
    one function cost tens of minutes rather than a minute.  Starting it
    from a clean solver is also faster than the module was before. *)
#push-options "--z3refresh"
fn inc32_impl (ctr: A.array S8.t) (#v0: erased (Seq.seq S8.t))
requires A.pts_to ctr v0 ** pure (Seq.length v0 == blocklen)
ensures exists* (v1: Seq.seq S8.t). A.pts_to ctr v1 ** pure (
  Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\
  vals v1 == inc32 (vals v0))
{
  A.pts_to_len ctr;
  (* The constants are classified here rather than taken from
     [Hacl.Secret.UInt8], because this function is reached from the AES-NI
     path and a global reached from a function with a target attribute is
     not something Custard will emit. *)
  let one = S8.classify 1uy;
  let ff = S8.classify 255uy;
  let zz = S8.classify 0uy;
  let x12 = A.(ctr.(12sz));
  let x13 = A.(ctr.(13sz));
  let x14 = A.(ctr.(14sz));
  let x15 = A.(ctr.(15sz));
  let r15 = S8.add_mod x15 one;
  let c15 = S8.select (S8.eq_mask x15 ff) one zz;
  let r14 = S8.add_mod x14 c15;
  let c14 = S8.select (S8.eq_mask x14 ff) c15 zz;
  let r13 = S8.add_mod x13 c14;
  let c13 = S8.select (S8.eq_mask x13 ff) c14 zz;
  let r12 = S8.add_mod x12 c13;
  A.((ctr.(12sz) <- r12));
  A.((ctr.(13sz) <- r13));
  A.((ctr.(14sz) <- r14));
  A.((ctr.(15sz) <- r15));
  with v1. assert A.pts_to ctr v1;
  assert_norm (pow2 8 == 256);
  inc32_bytes (vals v0) (S8.v r12) (S8.v r13) (S8.v r14) (S8.v r15);
  Seq.lemma_eq_intro (vals v1) (inc32 (vals v0));
  A.pts_to_len ctr;
}
#pop-options


(** {2 The increment as a lane}

    The carry chain above is thirty-five instructions and it runs on the
    array, so the vectorised driver that wants four consecutive counters
    pays it four times with a narrow store and a wide reload in between --
    a store-forwarding failure on every one.  There is a much cheaper route,
    and it needs no new instruction: reversing the sixteen bytes moves the
    counter's four bytes to the bottom of the register and turns their
    big-endian reading into a little-endian one, which is exactly lane zero;
    a packed thirty-two bit add of one increments that lane, modulo 2^32 and
    without carrying into its neighbours, which is precisely what [inc32]
    asks for; and reversing again puts it back.  Three instructions instead
    of thirty-five, and nothing leaves a register.

    [lane_of] is a lane written out as the number its four bytes make, so
    that the statement below is arithmetic on naturals and mentions neither
    secret integers nor [le_nat]. *)

let lane_of (b: block) (i: nat { i < 4 }) : nat =
  Seq.index b (4 * i) + 256 * Seq.index b (4 * i + 1) +
  65536 * Seq.index b (4 * i + 2) + 16777216 * Seq.index b (4 * i + 3)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let lane_of_bound (b: block) (i: nat { i < 4 })
  : Lemma (lane_of b i < pow2 32)
  = assert_norm (pow2 32 == 4294967296)
#pop-options

#push-options "--fuel 6 --ifuel 1 --z3rlimit 100"
(** The bridge to [Spec.SHANI.lane], which is where the [add32] axiom states
    itself.  Unfolding [le_nat] on a four-byte slice is all there is to it. *)
let lane_of_reg (v: Seq.lseq S8.t 16) (i: nat { i < 4 })
  : Lemma (S32.v (SHANI.lane v i) == lane_of (vals v) i)
  = SHANI.lane_val v i;
    let s = Seq.slice v (4 * i) (4 * i + 4) in
    assert (Seq.index s 0 == Seq.index v (4 * i));
    assert (Seq.index (Seq.slice s 1 4) 0 == Seq.index v (4 * i + 1));
    assert (Seq.index (Seq.slice (Seq.slice s 1 4) 1 3) 0 == Seq.index v (4 * i + 2));
    assert (Seq.index (Seq.slice (Seq.slice (Seq.slice s 1 4) 1 3) 1 2) 0 ==
            Seq.index v (4 * i + 3));
    vals_index v (4 * i); vals_index v (4 * i + 1);
    vals_index v (4 * i + 2); vals_index v (4 * i + 3)
#pop-options

(** Each byte of a register is recovered from its lane by a shift and a
    mask.  Stated on [lane_of] it is four small divisions. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"
let byte_of_lane (b: block) (j: nat { j < 16 })
  : Lemma (Seq.index b j == (lane_of b (j / 4) / pow2 (8 * (j % 4))) % 256)
  = let i = j / 4 in
    let k = j % 4 in
    Math.lemma_div_mod j 4;
    assert_norm (pow2 0 == 1); assert_norm (pow2 8 == 256);
    assert_norm (pow2 16 == 65536); assert_norm (pow2 24 == 16777216);
    let b0 = Seq.index b (4 * i) in let b1 = Seq.index b (4 * i + 1) in
    let b2 = Seq.index b (4 * i + 2) in let b3 = Seq.index b (4 * i + 3) in
    let x = lane_of b i in
    if k = 0 then begin
      Math.lemma_div_plus b0 (b1 + 256 * b2 + 65536 * b3) 256;
      Math.small_div b0 256;
      Math.lemma_mod_plus b0 (b1 + 256 * b2 + 65536 * b3) 256;
      Math.small_mod b0 256
    end else if k = 1 then begin
      assert (x == b0 + 256 * (b1 + 256 * b2 + 65536 * b3));
      Math.lemma_div_plus b0 (b1 + 256 * b2 + 65536 * b3) 256;
      Math.small_div b0 256;
      Math.lemma_mod_plus b1 (b2 + 256 * b3) 256;
      Math.small_mod b1 256
    end else if k = 2 then begin
      assert (x == b0 + 256 * b1 + 65536 * (b2 + 256 * b3));
      Math.lemma_div_plus (b0 + 256 * b1) (b2 + 256 * b3) 65536;
      Math.small_div (b0 + 256 * b1) 65536;
      Math.lemma_mod_plus b2 b3 256;
      Math.small_mod b2 256
    end else begin
      assert (x == b0 + 256 * b1 + 65536 * b2 + 16777216 * b3);
      Math.lemma_div_plus (b0 + 256 * b1 + 65536 * b2) b3 16777216;
      Math.small_div (b0 + 256 * b1 + 65536 * b2) 16777216;
      Math.small_mod b3 256
    end
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Lane zero of the reversed block is the big-endian counter.  Byte [k] of
    the reversal is byte [15 - k] of the block, so the four bytes of lane
    zero are bytes 15, 14, 13 and 12, least significant first -- which is
    [be32] read the other way up. *)
let lane_zero_be32 (c: block)
  : Lemma (lane_of (CL.bswap c) 0 == be32 c)
  = assert_norm (256 * 256 * 256 * 256 == pow2 32)

(** And the three remaining lanes cover exactly the twelve bytes [inc32]
    leaves alone. *)
let lane_rest (c: block) (i: nat { 1 <= i /\ i < 4 }) (k: nat { k < 4 })
  : Lemma (Seq.index (CL.bswap c) (4 * i + k) == Seq.index c (15 - 4 * i - k) /\
           15 - 4 * i - k < 12)
  = ()

(** The twelve bytes above the counter.  Byte [j] of the reversal is byte
    [15 - j] of [r], which for [j < 12] sits in one of the three lanes the
    add did not touch, and the same byte of the reversal of [c]. *)
let inc32_lanes_low (c r: block) (j: nat { j < 12 })
  : Lemma (requires
      lane_of r 1 == lane_of (CL.bswap c) 1 /\
      lane_of r 2 == lane_of (CL.bswap c) 2 /\
      lane_of r 3 == lane_of (CL.bswap c) 3)
    (ensures Seq.index (CL.bswap r) j == Seq.index c j)
  = let i = (15 - j) / 4 in
    let k = (15 - j) % 4 in
    Math.lemma_div_mod (15 - j) 4;
    byte_of_lane r (15 - j);
    byte_of_lane (CL.bswap c) (15 - j);
    lane_rest c i k

(** And the four below it, which are the new counter most significant
    first: byte [j] of the reversal is byte [15 - j] of lane zero. *)
let inc32_lanes_high (c r: block) (j: nat { 12 <= j /\ j < 16 })
  : Lemma (requires lane_of r 0 == (be32 c + 1) % pow2 32)
    (ensures Seq.index (CL.bswap r) j == byte_at ((be32 c + 1) % pow2 32)
                                                 (8 * (15 - j)))
  = byte_of_lane r (15 - j)

(** The whole step.  [r] is the register the packed add leaves behind: its
    lane zero is the counter plus one and its other three lanes are the
    other twelve bytes untouched.  Reversing it is [inc32].  The sixteen
    instances are written out rather than quantified, because a block is
    sixteen bytes and concrete indices are what the two lemmas above want. *)
let inc32_lanes (c r: block)
  : Lemma (requires
      lane_of r 0 == (lane_of (CL.bswap c) 0 + 1) % pow2 32 /\
      lane_of r 1 == lane_of (CL.bswap c) 1 /\
      lane_of r 2 == lane_of (CL.bswap c) 2 /\
      lane_of r 3 == lane_of (CL.bswap c) 3)
    (ensures CL.bswap r == inc32 c)
  = lane_zero_be32 c;
    inc32_lanes_low c r 0; inc32_lanes_low c r 1; inc32_lanes_low c r 2;
    inc32_lanes_low c r 3; inc32_lanes_low c r 4; inc32_lanes_low c r 5;
    inc32_lanes_low c r 6; inc32_lanes_low c r 7; inc32_lanes_low c r 8;
    inc32_lanes_low c r 9; inc32_lanes_low c r 10; inc32_lanes_low c r 11;
    inc32_lanes_high c r 12; inc32_lanes_high c r 13;
    inc32_lanes_high c r 14; inc32_lanes_high c r 15;
    Seq.lemma_eq_intro (CL.bswap r) (inc32 c)

#pop-options

(** {2 Four at a time}

    [Spec.AES.counter_block] is a recursion, and the vectorised driver needs
    the first five values of it spelled out: it advances the counter four
    times per step. *)

#push-options "--fuel 5 --ifuel 1"
let counter_unfold (b: block)
  : Lemma (counter_block b 0 == b /\
           counter_block b 1 == inc32 b /\
           counter_block b 2 == inc32 (inc32 b) /\
           counter_block b 3 == inc32 (inc32 (inc32 b)) /\
           counter_block b 4 == inc32 (inc32 (inc32 (inc32 b))))
  = ()
#pop-options

#pop-options
