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

(** GF(2^128) as GCM uses it: the multiplication of SP 800-38D algorithm 1,
    written out.

    There is no table.  The usual GHASH implementation precomputes sixteen or
    two hundred and fifty-six multiples of the hash key and indexes them by
    four bits of the ciphertext at a time -- a lookup at a secret index,
    which is the same cache-timing door that a table-driven S-box opens.  The
    loop here runs all one hundred and twenty-eight steps, both branches of
    each turned into a mask: about a hundred instructions per bit, so a
    megabyte a second or so.  Carry-less multiply instructions are the real
    answer on hardware that has them, and are the intended upgrade path.

    The shift is written descending, so that the byte that supplies a
    carry is read before it is overwritten and no scratch is needed. *)
module Hacl.AES.GF128

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.GF128
open Hacl.AES.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module UInt = FStar.UInt
module Copy = Hacl.Impl.Copy
module Poly = Spec.GF128.Poly
module Math = FStar.Math.Lemmas
module Mem = Hacl.Mem

(** This module is arithmetic-heavy, and the default SMT encoding boxes
    every integer operation, which hides the structure of the products from
    Z3's arithmetic solver.  Encoding linear arithmetic natively and leaving
    only the nonlinear operators wrapped is measurably faster here. *)
#set-options "--smtencoding.nl_arith_repr wrapped --smtencoding.l_arith_repr native --smtencoding.elim_box true"

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The pure side} *)

let gadd_eq (v0 vb v: Seq.seq S8.t) (off: nat) (n: nat)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\
             off + blocklen <= Seq.length vb /\ blocklen <= n /\
             (forall (j: nat). j < blocklen ==>
                Seq.index (vals v) j ==
                  (if j < n
                   then Seq.index (vals v0) j ^^ Seq.index (vals vb) (off + j)
                   else Seq.index (vals v0) j)))
          (ensures vals v == gadd (vals v0)
                              (Seq.slice (vals vb) off (off + blocklen)))
  = Seq.lemma_eq_intro (vals v)
      (gadd (vals v0) (Seq.slice (vals vb) off (off + blocklen)))

let shift_eq (v0 v: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\ n == 0 /\
             (forall (j: nat). j < blocklen ==>
                Seq.index (vals v) j ==
                  (if n <= j then shift_byte (vals v0) j
                   else Seq.index (vals v0) j)))
          (ensures vals v == shift_right_1 (vals v0))
  = Seq.lemma_eq_intro (vals v) (shift_right_1 (vals v0))

(** The reduction touches byte zero only: [r_block] is [0xe1] followed by
    fifteen zeroes, and a byte xored with zero is itself. *)
let reduce_eq (v0 v: Seq.seq S8.t) (odd: bool)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\
             Seq.index (vals v) 0 ==
               Seq.index (vals v0) 0 ^^ (if odd then 0xe1 else 0) /\
             (forall (j: nat). 0 < j /\ j < blocklen ==>
                Seq.index (vals v) j == Seq.index (vals v0) j))
          (ensures vals v == (if odd then gadd (vals v0) r_block else vals v0))
  = FStar.Classical.forall_intro xor_zero;
    if odd then Seq.lemma_eq_intro (vals v) (gadd (vals v0) r_block)
    else Seq.lemma_eq_intro (vals v) (vals v0)

(** The conditional addition of [z + v] the multiplication makes at each
    bit: a byte xored with zero is itself, which is the whole content of the
    branch that is not taken. *)
let select_add_eq (v0 vb v: Seq.seq S8.t) (taken: bool) (n: nat)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length vb == blocklen /\
             Seq.length v == blocklen /\ blocklen <= n /\
             (forall (j: nat). j < blocklen ==>
                Seq.index (vals v) j ==
                  (if j < n
                   then Seq.index (vals v0) j ^^
                        (if taken then Seq.index (vals vb) j else 0)
                   else Seq.index (vals v0) j)))
          (ensures vals v == (if taken then gadd (vals v0) (vals vb) else vals v0))
  = FStar.Classical.forall_intro xor_zero;
    if taken then Seq.lemma_eq_intro (vals v) (gadd (vals v0) (vals vb))
    else Seq.lemma_eq_intro (vals v) (vals v0)

(** A byte and a carry bit into the top of it occupy disjoint bits, so the
    [or] the implementation writes is the sum the specification writes. *)
let or_carry (c r: elem)
  : Lemma (requires (c == 0 \/ c == 128) /\ r < 128)
          (ensures UInt.logor #8 c r == c + r)
  = assert_norm (pow2 7 == 128);
    UInt.logor_disjoint #8 c r 7

let and_one (a: elem) : Lemma (UInt.logand #8 a 1 == a % 2) =
  assert_norm (pow2 1 == 2);
  UInt.logand_mask #8 a 1

#push-options "--fuel 2 --ifuel 1"

let gmul_loop_done (x z v: block) : Lemma (gmul_loop x z v 128 == z) = ()

let gmul_loop_step (x z v: block) (i: nat)
  : Lemma (requires i < 128)
          (ensures gmul_loop x z v i ==
            gmul_loop x
              (if bit x i then gadd z v else z)
              (if Seq.index v (blocklen - 1) % 2 = 0
               then shift_right_1 v
               else gadd (shift_right_1 v) r_block)
              (i + 1))
  = ()

let gmul_start (x y: block) : Lemma (gmul_loop x zero y 0 == gmul x y) = ()

#pop-options

let zero_block (v: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length v == blocklen /\ blocklen <= n /\
             (forall (j: nat). j < blocklen ==>
                Seq.index (vals v) j == (if j < n then 0 else Seq.index (vals v) j)))
          (ensures vals v == zero)
  = Seq.lemma_eq_intro (vals v) zero

(** {2 Addition} *)

(** [a := a + b[off..off+16)]. *)

fn gadd_at_impl (a: A.array S8.t) (b: A.array S8.t) (off: SZ.t)
                (#v0 #vb: erased (Seq.seq S8.t)) (#pb: perm)
requires A.pts_to a v0 ** A.pts_to b #pb vb ** pure (
  Seq.length v0 == blocklen /\ SZ.v off + blocklen <= Seq.length vb)
ensures exists* (v1: Seq.seq S8.t). A.pts_to a v1 ** A.pts_to b #pb vb ** pure (
  Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\
  SZ.v off + blocklen <= Seq.length vb /\
  vals v1 == gadd (vals v0) (Seq.slice (vals vb) (SZ.v off) (SZ.v off + blocklen)))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= blocklen /\ Seq.length v == blocklen /\
          Seq.length v0 == blocklen /\
          SZ.v off + blocklen <= Seq.length vb /\
          (forall (j: nat). j < blocklen ==>
             Seq.index (vals v) j ==
               (if j < SZ.v vi
                then Seq.index (vals v0) j ^^ Seq.index (vals vb) (SZ.v off + j)
                else Seq.index (vals v0) j)))
  decreases (blocklen - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(SZ.add off vi));
    let r = bxor x y;
    with v. assert A.pts_to a v;
    vals_upd v (SZ.v vi) r;
    A.((a.(vi) <- r));
    i := SZ.add vi 1sz;
  };
  let vn = !i;
  with v. assert A.pts_to a v;
  gadd_eq v0 vb v (SZ.v off) (SZ.v vn);
  A.pts_to_len a;
}

(** {2 The step on [v]}

    One right shift of the whole block, then the reduction by [R] when the
    bit that fell off the end was set.  The loop runs from the top byte down
    so that byte [k - 1], which supplies the carry into byte [k], is still
    untouched when it is read. *)

#push-options "--z3rlimit 400"
fn shift_reduce_impl (v: A.array S8.t) (#v0: erased (Seq.seq S8.t))
requires A.pts_to v v0 ** pure (Seq.length v0 == blocklen)
ensures exists* (v1: Seq.seq S8.t). A.pts_to v v1 ** pure (
  Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\
  vals v1 == (if Seq.index (vals v0) (blocklen - 1) % 2 = 0
              then shift_right_1 (vals v0)
              else gadd (shift_right_1 (vals v0)) r_block))
{
  A.pts_to_len v;
  let one = S8.classify 1uy;
  let last = A.(v.(15sz));
  let lsb = S8.logand last one;
  and_one (S8.v last);
  let rmask = S8.eq_mask lsb one;

  let mut i = 16sz;
  while (let vi = !i; SZ.gt vi 0sz)
  invariant exists* (vi: SZ.t) (vv: Seq.seq S8.t).
    pts_to i vi ** A.pts_to v vv **
    pure (SZ.v vi <= blocklen /\ Seq.length vv == blocklen /\
          Seq.length v0 == blocklen /\
          (forall (j: nat). j < blocklen ==>
             Seq.index (vals vv) j ==
               (if SZ.v vi <= j then shift_byte (vals v0) j
                else Seq.index (vals v0) j)))
  decreases (SZ.v (!i))
  {
    let vi = !i;
    let k = SZ.sub vi 1sz;
    let cur = A.(v.(k));
    let rest = S8.shift_right cur 1ul;
    with vv. assert A.pts_to v vv;
    if (k = 0sz) {
      or_carry 0 (S8.v rest);
      vals_upd vv 0 rest;
      A.((v.(0sz) <- rest));
      i := k;
    } else {
      let prev = A.(v.(SZ.sub k 1sz));
      and_one (S8.v prev);
      let carry = S8.shift_left (S8.logand prev one) 7ul;
      assert_norm (pow2 7 == 128);
      assert_norm (pow2 8 == 256);
      or_carry (S8.v carry) (S8.v rest);
      let r = S8.logor carry rest;
      vals_upd vv (SZ.v k) r;
      A.((v.(k) <- r));
      i := k;
    }
  };
  let vn = !i;
  with vs. assert A.pts_to v vs;
  shift_eq v0 vs (SZ.v vn);

  assert (pure (S8.v lsb == Seq.index (vals v0) (blocklen - 1) % 2));
  let b0 = A.(v.(0sz));
  let e1 = S8.classify 0xe1uy;
  let red = S8.select rmask e1 S8.zero;
  assert (pure (S8.v red ==
    (if Seq.index (vals v0) (blocklen - 1) % 2 = 1 then 0xe1 else 0)));
  let nb0 = bxor b0 red;
  vals_upd vs 0 nb0;
  A.((v.(0sz) <- nb0));
  with v1. assert A.pts_to v v1;
  reduce_eq vs v1 (Seq.index (vals v0) (blocklen - 1) % 2 = 1);
  A.pts_to_len v;
}

(** {2 The inverse step: dividing by [x]}

    Multiplication by [x] is invertible, and the inverse is the mirror image
    of [shift_reduce_impl]: shift the whole block the other way, and when the
    bit that fell off the {i bottom} was set, add [R / x], which is
    [x^127 + x^6 + x + 1] -- [0xc2] in byte zero and [1] in byte fifteen.

    It is called exactly once, when a GCM key is expanded.  GHASH's
    multiplier omits the one-bit shift that would line the carry-less
    product up with GHASH's bit order, and so computes [x] times the field
    product; holding the hash key divided by [x] cancels that factor in every
    multiplication the cipher will ever do.  See
    [Hacl.AES.GF128.NI.raw_product] and [Spec.GF128.Poly.xtimes_xdiv].

    The loop runs from byte zero upwards, so byte [k + 1], which supplies the
    carry into byte [k], is still untouched when it is read.  The last byte
    has no successor to take a carry from, so it is handled after the loop
    rather than by a test inside it: the test is the only branch in an
    otherwise straight-line body, and the loop is short enough that paying
    for it sixteen times is a measurable part of a GCM key expansion. *)

let shl_eq (v0 v: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\
             n == blocklen /\
             (forall (j: nat). j < blocklen ==>
                Seq.index (vals v) j ==
                  (if j < n
                   then Poly.shl_byte (vals v0) j
                   else Seq.index (vals v0) j)))
          (ensures vals v == Poly.shift_left_1 (vals v0))
  = Seq.lemma_eq_intro (vals v) (Poly.shift_left_1 (vals v0))

(** [R / x] touches bytes zero and fifteen only, and a byte xored with zero
    is itself. *)
let rdiv_eq (v0 v: Seq.seq S8.t) (odd: bool)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\
             Seq.index (vals v) 0 ==
               Seq.index (vals v0) 0 ^^ (if odd then 0xc2 else 0) /\
             Seq.index (vals v) (blocklen - 1) ==
               Seq.index (vals v0) (blocklen - 1) ^^ (if odd then 1 else 0) /\
             (forall (j: nat). 0 < j /\ j < blocklen - 1 ==>
                Seq.index (vals v) j == Seq.index (vals v0) j))
          (ensures vals v == (if odd then gadd (vals v0) Poly.rdiv_block
                              else vals v0))
  = FStar.Classical.forall_intro xor_zero;
    if odd then Seq.lemma_eq_intro (vals v) (gadd (vals v0) Poly.rdiv_block)
    else Seq.lemma_eq_intro (vals v) (vals v0)

(** A carry bit into the bottom of an even byte is disjoint from it. *)
let or_low (c r: elem)
  : Lemma (requires (c == 0 \/ c == 1) /\ r % 2 == 0)
          (ensures UInt.logor #8 r c == r + c)
  = assert_norm (pow2 1 == 2);
    UInt.logor_disjoint #8 r c 1

#push-options "--z3rlimit 1500"
fn xdiv_impl (v: A.array S8.t) (#v0: erased (Seq.seq S8.t))
requires A.pts_to v v0 ** pure (Seq.length v0 == blocklen)
ensures exists* (v1: Seq.seq S8.t). A.pts_to v v1 ** pure (
  Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\
  vals v1 == Poly.xdiv (vals v0))
{
  A.pts_to_len v;
  let one = S8.classify 1uy;
  let first = A.(v.(0sz));
  let msb = S8.shift_right first 7ul;
  assert_norm (pow2 7 == 128);
  Math.lemma_div_lt (S8.v first) 8 7;
  Math.small_mod (S8.v first / 128) 2;
  let rmask = S8.eq_mask msb one;

  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 15sz)
  invariant exists* (vi: SZ.t) (vv: Seq.seq S8.t).
    pts_to i vi ** A.pts_to v vv **
    pure (SZ.v vi <= blocklen - 1 /\ Seq.length vv == blocklen /\
          Seq.length v0 == blocklen /\
          (forall (j: nat). j < blocklen ==>
             Seq.index (vals vv) j ==
               (if j < SZ.v vi then Poly.shl_byte (vals v0) j
                else Seq.index (vals v0) j)))
  decreases (blocklen - 1 - SZ.v (!i))
  {
    let vi = !i;
    let cur = A.(v.(vi));
    let rest = S8.shift_left cur 1ul;
    with vv. assert A.pts_to v vv;
    let nxt = A.(v.(SZ.add vi 1sz));
    let carry = S8.shift_right nxt 7ul;
    Math.lemma_div_lt (S8.v nxt) 8 7;
    or_low (S8.v carry) (S8.v rest);
    let r = S8.logor rest carry;
    vals_upd vv (SZ.v vi) r;
    A.((v.(vi) <- r));
    i := SZ.add vi 1sz;
  };
  let last = A.(v.(15sz));
  let lrest = S8.shift_left last 1ul;
  with vw. assert A.pts_to v vw;
  or_low 0 (S8.v lrest);
  vals_upd vw 15 lrest;
  A.((v.(15sz) <- lrest));
  with vs. assert A.pts_to v vs;
  shl_eq v0 vs blocklen;

  let b0 = A.(v.(0sz));
  let c2 = S8.classify 0xc2uy;
  let red0 = S8.select rmask c2 S8.zero;
  let nb0 = bxor b0 red0;
  vals_upd vs 0 nb0;
  A.((v.(0sz) <- nb0));
  with vt. assert A.pts_to v vt;
  let b15 = A.(v.(15sz));
  let red15 = S8.select rmask one S8.zero;
  let nb15 = bxor b15 red15;
  vals_upd vt 15 nb15;
  A.((v.(15sz) <- nb15));
  with v1. assert A.pts_to v v1;
  assert (pure (bit (vals v0) 0 == (Seq.index (vals v0) 0 / 128 = 1)));
  rdiv_eq vs v1 (bit (vals v0) 0);
  A.pts_to_len v;
}
#pop-options

(** [z := z + v] when the mask is all ones, and nothing when it is all
    zeroes -- the conditional accumulation of algorithm 1, branch-free. *)

#pop-options

fn select_add (z: A.array S8.t) (v: A.array S8.t) (mask: S8.t)
              (#v0 #vb: erased (Seq.seq S8.t))
requires A.pts_to z v0 ** A.pts_to v vb ** pure (
  Seq.length v0 == blocklen /\ Seq.length vb == blocklen /\
  (S8.v mask == 0 \/ S8.v mask == 255))
ensures exists* (v1: Seq.seq S8.t). A.pts_to z v1 ** A.pts_to v vb ** pure (
  Seq.length v0 == blocklen /\ Seq.length vb == blocklen /\
  Seq.length v1 == blocklen /\
  vals v1 == (if S8.v mask = 0 then vals v0 else gadd (vals v0) (vals vb)))
{
  A.pts_to_len z;
  A.pts_to_len v;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (vz: Seq.seq S8.t).
    pts_to i vi ** A.pts_to z vz ** A.pts_to v vb **
    pure (SZ.v vi <= blocklen /\ Seq.length vz == blocklen /\
          Seq.length v0 == blocklen /\ Seq.length vb == blocklen /\
          (S8.v mask == 0 \/ S8.v mask == 255) /\
          (forall (j: nat). j < blocklen ==>
             Seq.index (vals vz) j ==
               (if j < SZ.v vi
                then Seq.index (vals v0) j ^^
                     (if S8.v mask = 0 then 0 else Seq.index (vals vb) j)
                else Seq.index (vals v0) j)))
  decreases (blocklen - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(z.(vi));
    let y = A.(v.(vi));
    let r = bxor x (S8.select mask y S8.zero);
    with vz. assert A.pts_to z vz;
    vals_upd vz (SZ.v vi) r;
    A.((z.(vi) <- r));
    i := SZ.add vi 1sz;
  };
  let vn = !i;
  with vz. assert A.pts_to z vz;
  select_add_eq v0 vb vz (S8.v mask <> 0) (SZ.v vn);
  A.pts_to_len z;
}

(** {2 Multiplication}

    [a := a * h].  The accumulator and the running multiple of [h] are
    scratch; the bits of [a] are read before anything is written to it. *)

fn gmul_portable (a: A.array S8.t) (h: A.array S8.t)
             (#va #vh: erased (Seq.seq S8.t))
requires A.pts_to a va ** A.pts_to h vh ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen)
ensures exists* (va': Seq.seq S8.t). A.pts_to a va' ** A.pts_to h vh ** pure (
  Seq.length va == blocklen /\ Seq.length vh == blocklen /\
  Seq.length va' == blocklen /\
  vals va' == gmul (vals va) (vals vh))
{
  A.pts_to_len a;
  A.pts_to_len h;
  let z8 = S8.zero;
  let one = S8.classify 1uy;
  let mut za = [| z8; 16sz |];
  Mem.track za; A.pts_to_len za; let mut vaa = [| z8; 16sz |];
  Mem.track vaa; A.pts_to_len vaa; A.pts_to_len za;
  A.pts_to_len vaa;
  Copy.copy_exact vaa h 16sz;
  with vz0. assert A.pts_to za vz0;
  zero_block vz0 blocklen;
  gmul_start (vals va) (vals vh);

  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 128sz)
  invariant exists* (vi: SZ.t) (vz: Seq.seq S8.t) (vw: Seq.seq S8.t).
    pts_to i vi ** A.pts_to a va ** A.pts_to h vh **
    A.pts_to za vz ** A.pts_to vaa vw **
    pure (SZ.v vi <= 128 /\ Seq.length vz == blocklen /\
          Seq.length vw == blocklen /\ Seq.length va == blocklen /\
          Seq.length vh == blocklen /\
          gmul_loop (vals va) (vals vz) (vals vw) (SZ.v vi) ==
            gmul (vals va) (vals vh))
  decreases (128 - SZ.v (!i))
  {
    let vi = !i;
    with vz. assert A.pts_to za vz;
    with vw. assert A.pts_to vaa vw;
    gmul_loop_step (vals va) (vals vz) (vals vw) (SZ.v vi);

    let bidx = SZ.div vi 8sz;
    let sh = SZ.sub 7sz (SZ.rem vi 8sz);
    let xb = A.(a.(bidx));
    let bitv = S8.logand (S8.shift_right xb (SZ.sizet_to_uint32 sh)) one;
    and_one (S8.v xb / pow2 (SZ.v sh));
    let bmask = S8.eq_mask bitv one;

    select_add za vaa bmask;
    shift_reduce_impl vaa;
    i := SZ.add vi 1sz;
  };
  let vn = !i;
  with vz. assert A.pts_to za vz;
  with vw. assert A.pts_to vaa vw;
  gmul_loop_done (vals va) (vals vz) (vals vw);
  Copy.copy_exact a za 16sz;
  Mem.wipe vaa 16sz;
  Mem.wipe za 16sz;
  ()
}

#pop-options
