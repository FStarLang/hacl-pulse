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

(** The four state transformations of FIPS 197, in place on a sixteen-byte
    slice.

    The state is the flat sixteen bytes, not a matrix: FIPS 197 fills its
    four-by-four array column by column, so byte [4c + r] is row [r] of column
    [c], and only ShiftRows cares.  It is written here as what it is -- three
    rotations of the last three rows -- with every index a literal.

    SubBytes and AddRoundKey are loops, because their bodies are independent
    and the invariant is the obvious prefix one.  ShiftRows and MixColumns are
    straight line: each output byte depends on several input bytes, so the
    reads all happen before the writes and no scratch buffer is needed. *)
module Hacl.AES

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Core

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The pure side}

    Pulse does not unfold specification definitions inside a verification
    condition, so every statement that needs [sub_bytes] or [mix_columns] to
    be looked at is proved here, at the level of numbers, and the Pulse
    function below only has to supply the sixteen equations. *)

let sub_bytes_eq (v0 v: Seq.seq S8.t) (n: nat)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\
                    blocklen <= n /\
                    (forall (j: nat). j < blocklen ==>
                       Seq.index (vals v) j ==
                         (if j < n then sbox (Seq.index (vals v0) j)
                          else Seq.index (vals v0) j)))
          (ensures vals v == sub_bytes (vals v0))
  = Seq.lemma_eq_intro (vals v) (sub_bytes (vals v0))

let add_round_key_eq (v0 vw v: Seq.seq S8.t) (off: nat) (n: nat)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\
                    off + blocklen <= Seq.length vw /\ blocklen <= n /\
                    (forall (j: nat). j < blocklen ==>
                       Seq.index (vals v) j ==
                         (if j < n
                          then Seq.index (vals v0) j ^^ Seq.index (vals vw) (off + j)
                          else Seq.index (vals v0) j)))
          (ensures vals v == add_round_key (vals v0)
                               (Seq.slice (vals vw) off (off + blocklen)))
  = Seq.lemma_eq_intro (vals v)
      (add_round_key (vals v0) (Seq.slice (vals vw) off (off + blocklen)))

(** The sixteen bytes of the permutation, written out: row zero is fixed, row
    one is a four-cycle, row two two transpositions, row three the inverse
    four-cycle. *)
let shift_rows_eq (v0 v: Seq.seq S8.t)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\
             Seq.index v 0 == Seq.index v0 0 /\ Seq.index v 4 == Seq.index v0 4 /\
             Seq.index v 8 == Seq.index v0 8 /\ Seq.index v 12 == Seq.index v0 12 /\
             Seq.index v 1 == Seq.index v0 5 /\ Seq.index v 5 == Seq.index v0 9 /\
             Seq.index v 9 == Seq.index v0 13 /\ Seq.index v 13 == Seq.index v0 1 /\
             Seq.index v 2 == Seq.index v0 10 /\ Seq.index v 6 == Seq.index v0 14 /\
             Seq.index v 10 == Seq.index v0 2 /\ Seq.index v 14 == Seq.index v0 6 /\
             Seq.index v 3 == Seq.index v0 15 /\ Seq.index v 7 == Seq.index v0 3 /\
             Seq.index v 11 == Seq.index v0 7 /\ Seq.index v 15 == Seq.index v0 11)
          (ensures vals v == shift_rows (vals v0))
  = Seq.lemma_eq_intro (vals v) (shift_rows (vals v0))

(** One output byte at a time: the MixColumns matrix is [(2 3 1 1)] rotated
    right by the row index, so row [r] of column [c] combines the four bytes
    of that column with the coefficients in that order.  Splitting the sixteen
    into sixteen lemmas is what makes them discharge: as one statement the
    solver has sixteen large hypotheses to match at once. *)
let mix_at_0 (b: block) (x: elem)
  : Lemma (requires x == fmul 2 (Seq.index b 0) ^^ (fmul 3 (Seq.index b 1) ^^ (fmul 1 (Seq.index b 2) ^^ fmul 1 (Seq.index b 3))))
          (ensures Seq.index (mix_columns b) 0 == x) = ()

let mix_at_1 (b: block) (x: elem)
  : Lemma (requires x == fmul 1 (Seq.index b 0) ^^ (fmul 2 (Seq.index b 1) ^^ (fmul 3 (Seq.index b 2) ^^ fmul 1 (Seq.index b 3))))
          (ensures Seq.index (mix_columns b) 1 == x) = ()

let mix_at_2 (b: block) (x: elem)
  : Lemma (requires x == fmul 1 (Seq.index b 0) ^^ (fmul 1 (Seq.index b 1) ^^ (fmul 2 (Seq.index b 2) ^^ fmul 3 (Seq.index b 3))))
          (ensures Seq.index (mix_columns b) 2 == x) = ()

let mix_at_3 (b: block) (x: elem)
  : Lemma (requires x == fmul 3 (Seq.index b 0) ^^ (fmul 1 (Seq.index b 1) ^^ (fmul 1 (Seq.index b 2) ^^ fmul 2 (Seq.index b 3))))
          (ensures Seq.index (mix_columns b) 3 == x) = ()

let mix_at_4 (b: block) (x: elem)
  : Lemma (requires x == fmul 2 (Seq.index b 4) ^^ (fmul 3 (Seq.index b 5) ^^ (fmul 1 (Seq.index b 6) ^^ fmul 1 (Seq.index b 7))))
          (ensures Seq.index (mix_columns b) 4 == x) = ()

let mix_at_5 (b: block) (x: elem)
  : Lemma (requires x == fmul 1 (Seq.index b 4) ^^ (fmul 2 (Seq.index b 5) ^^ (fmul 3 (Seq.index b 6) ^^ fmul 1 (Seq.index b 7))))
          (ensures Seq.index (mix_columns b) 5 == x) = ()

let mix_at_6 (b: block) (x: elem)
  : Lemma (requires x == fmul 1 (Seq.index b 4) ^^ (fmul 1 (Seq.index b 5) ^^ (fmul 2 (Seq.index b 6) ^^ fmul 3 (Seq.index b 7))))
          (ensures Seq.index (mix_columns b) 6 == x) = ()

let mix_at_7 (b: block) (x: elem)
  : Lemma (requires x == fmul 3 (Seq.index b 4) ^^ (fmul 1 (Seq.index b 5) ^^ (fmul 1 (Seq.index b 6) ^^ fmul 2 (Seq.index b 7))))
          (ensures Seq.index (mix_columns b) 7 == x) = ()

let mix_at_8 (b: block) (x: elem)
  : Lemma (requires x == fmul 2 (Seq.index b 8) ^^ (fmul 3 (Seq.index b 9) ^^ (fmul 1 (Seq.index b 10) ^^ fmul 1 (Seq.index b 11))))
          (ensures Seq.index (mix_columns b) 8 == x) = ()

let mix_at_9 (b: block) (x: elem)
  : Lemma (requires x == fmul 1 (Seq.index b 8) ^^ (fmul 2 (Seq.index b 9) ^^ (fmul 3 (Seq.index b 10) ^^ fmul 1 (Seq.index b 11))))
          (ensures Seq.index (mix_columns b) 9 == x) = ()

let mix_at_10 (b: block) (x: elem)
  : Lemma (requires x == fmul 1 (Seq.index b 8) ^^ (fmul 1 (Seq.index b 9) ^^ (fmul 2 (Seq.index b 10) ^^ fmul 3 (Seq.index b 11))))
          (ensures Seq.index (mix_columns b) 10 == x) = ()

let mix_at_11 (b: block) (x: elem)
  : Lemma (requires x == fmul 3 (Seq.index b 8) ^^ (fmul 1 (Seq.index b 9) ^^ (fmul 1 (Seq.index b 10) ^^ fmul 2 (Seq.index b 11))))
          (ensures Seq.index (mix_columns b) 11 == x) = ()

let mix_at_12 (b: block) (x: elem)
  : Lemma (requires x == fmul 2 (Seq.index b 12) ^^ (fmul 3 (Seq.index b 13) ^^ (fmul 1 (Seq.index b 14) ^^ fmul 1 (Seq.index b 15))))
          (ensures Seq.index (mix_columns b) 12 == x) = ()

let mix_at_13 (b: block) (x: elem)
  : Lemma (requires x == fmul 1 (Seq.index b 12) ^^ (fmul 2 (Seq.index b 13) ^^ (fmul 3 (Seq.index b 14) ^^ fmul 1 (Seq.index b 15))))
          (ensures Seq.index (mix_columns b) 13 == x) = ()

let mix_at_14 (b: block) (x: elem)
  : Lemma (requires x == fmul 1 (Seq.index b 12) ^^ (fmul 1 (Seq.index b 13) ^^ (fmul 2 (Seq.index b 14) ^^ fmul 3 (Seq.index b 15))))
          (ensures Seq.index (mix_columns b) 14 == x) = ()

let mix_at_15 (b: block) (x: elem)
  : Lemma (requires x == fmul 3 (Seq.index b 12) ^^ (fmul 1 (Seq.index b 13) ^^ (fmul 1 (Seq.index b 14) ^^ fmul 2 (Seq.index b 15))))
          (ensures Seq.index (mix_columns b) 15 == x) = ()

let mix_columns_join (v0 v: Seq.seq S8.t)
  : Lemma (requires Seq.length v0 == blocklen /\ Seq.length v == blocklen /\
             Seq.index (vals v) 0 == Seq.index (mix_columns (vals v0)) 0 /\
             Seq.index (vals v) 1 == Seq.index (mix_columns (vals v0)) 1 /\
             Seq.index (vals v) 2 == Seq.index (mix_columns (vals v0)) 2 /\
             Seq.index (vals v) 3 == Seq.index (mix_columns (vals v0)) 3 /\
             Seq.index (vals v) 4 == Seq.index (mix_columns (vals v0)) 4 /\
             Seq.index (vals v) 5 == Seq.index (mix_columns (vals v0)) 5 /\
             Seq.index (vals v) 6 == Seq.index (mix_columns (vals v0)) 6 /\
             Seq.index (vals v) 7 == Seq.index (mix_columns (vals v0)) 7 /\
             Seq.index (vals v) 8 == Seq.index (mix_columns (vals v0)) 8 /\
             Seq.index (vals v) 9 == Seq.index (mix_columns (vals v0)) 9 /\
             Seq.index (vals v) 10 == Seq.index (mix_columns (vals v0)) 10 /\
             Seq.index (vals v) 11 == Seq.index (mix_columns (vals v0)) 11 /\
             Seq.index (vals v) 12 == Seq.index (mix_columns (vals v0)) 12 /\
             Seq.index (vals v) 13 == Seq.index (mix_columns (vals v0)) 13 /\
             Seq.index (vals v) 14 == Seq.index (mix_columns (vals v0)) 14 /\
             Seq.index (vals v) 15 == Seq.index (mix_columns (vals v0)) 15)
          (ensures vals v == mix_columns (vals v0))
  = Seq.lemma_eq_intro (vals v) (mix_columns (vals v0))

(** {2 SubBytes} *)

fn sub_bytes_impl (st: A.array S8.t) (#v0: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == blocklen)
ensures exists* (v1: Seq.seq S8.t). A.pts_to st v1 **
  pure (Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\ vals v1 == sub_bytes (vals v0))
{
  A.pts_to_len st;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to st v **
    pure (SZ.v vi <= blocklen /\ Seq.length v == blocklen /\
          Seq.length v0 == blocklen /\
          (forall (j: nat). j < blocklen ==>
            Seq.index (vals v) j ==
              (if j < SZ.v vi then sbox (Seq.index (vals v0) j)
               else Seq.index (vals v0) j)))
  decreases (blocklen - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(st.(vi));
    let y = sbox_impl x;
    with v. assert A.pts_to st v;
    vals_upd v (SZ.v vi) y;
    A.((st.(vi) <- y));
    i := SZ.add vi 1sz;
  };
  let vn = !i;
  with v. assert A.pts_to st v;
  sub_bytes_eq v0 v (SZ.v vn);
  (* A Pulse function may not end with a pure statement: the last one is
     dropped.  This read of the length is the cheapest thing that is not. *)
  A.pts_to_len st;
}

(** {2 AddRoundKey}

    The round key is a sixteen-byte window of the expanded key rather than a
    slice of its own, so that the caller does not have to carve one out at
    every round. *)

fn add_round_key_impl (st: A.array S8.t) (w: A.array S8.t) (off: SZ.t)
                      (#v0 #vw: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** A.pts_to w vw **
         pure (Seq.length v0 == blocklen /\
               SZ.v off + blocklen <= Seq.length vw)
ensures exists* (v1: Seq.seq S8.t). A.pts_to st v1 ** A.pts_to w vw **
  pure (Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\
        SZ.v off + blocklen <= Seq.length vw /\
        vals v1 == add_round_key (vals v0)
                     (Seq.slice (vals vw) (SZ.v off) (SZ.v off + blocklen)))
{
  A.pts_to_len st;
  A.pts_to_len w;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi 16sz)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to st v ** A.pts_to w vw **
    pure (SZ.v vi <= blocklen /\ Seq.length v == blocklen /\
          Seq.length v0 == blocklen /\
          SZ.v off + blocklen <= Seq.length vw /\
          (forall (j: nat). j < blocklen ==>
            Seq.index (vals v) j ==
              (if j < SZ.v vi
               then Seq.index (vals v0) j ^^ Seq.index (vals vw) (SZ.v off + j)
               else Seq.index (vals v0) j)))
  decreases (blocklen - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(st.(vi));
    let b = A.(w.(SZ.add off vi));
    let y = bxor a b;
    with v. assert A.pts_to st v;
    vals_upd v (SZ.v vi) y;
    A.((st.(vi) <- y));
    i := SZ.add vi 1sz;
  };
  let vn = !i;
  with v. assert A.pts_to st v;
  add_round_key_eq v0 vw v (SZ.v off) (SZ.v vn);
  (* A Pulse function may not end with a pure statement: the last one is
     dropped.  This read of the length is the cheapest thing that is not. *)
  A.pts_to_len st;
}

(** {2 ShiftRows}

    Row [r] moves left by [r] columns.  Row zero does not move; row one is a
    four-cycle, row two two transpositions, row three the inverse
    four-cycle. *)

fn shift_rows_impl (st: A.array S8.t) (#v0: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == blocklen)
ensures exists* (v1: Seq.seq S8.t). A.pts_to st v1 **
  pure (Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\ vals v1 == shift_rows (vals v0))
{
  A.pts_to_len st;
  let x1  = A.(st.(1sz));  let x5  = A.(st.(5sz));
  let x9  = A.(st.(9sz));  let x13 = A.(st.(13sz));
  let x2  = A.(st.(2sz));  let x6  = A.(st.(6sz));
  let x10 = A.(st.(10sz)); let x14 = A.(st.(14sz));
  let x3  = A.(st.(3sz));  let x7  = A.(st.(7sz));
  let x11 = A.(st.(11sz)); let x15 = A.(st.(15sz));
  A.((st.(1sz)  <- x5));  A.((st.(5sz)  <- x9));
  A.((st.(9sz)  <- x13)); A.((st.(13sz) <- x1));
  A.((st.(2sz)  <- x10)); A.((st.(6sz)  <- x14));
  A.((st.(10sz) <- x2));  A.((st.(14sz) <- x6));
  A.((st.(3sz)  <- x15)); A.((st.(7sz)  <- x3));
  A.((st.(11sz) <- x7));  A.((st.(15sz) <- x11));
  with v. assert A.pts_to st v;
  shift_rows_eq v0 v;
  (* A Pulse function may not end with a pure statement: the last one is
     dropped.  This read of the length is the cheapest thing that is not. *)
  A.pts_to_len st;
}

(** {2 MixColumns}

    Each output byte is a combination of the four bytes of its column, so all
    sixteen inputs are read first.  The coefficients are [1], [2] and [3],
    passed to the general multiplication rather than specialized to [xtime]:
    the saving would be a quarter of the round's field multiplications, and
    against the fifteen that every S-box costs it is not worth an exponent
    lemma. *)

(** One column, given its four bytes already read out of the state.  Splitting
    MixColumns this way keeps each verification condition down to four nested
    [Seq.upd]s; sixteen in a row made the solver time out on nothing more than
    the length of the result. *)

fn mix_column_impl (st: A.array S8.t) (o: SZ.t) (a0 a1 a2 a3: S8.t)
  (#v0: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == blocklen /\ SZ.v o + 4 <= blocklen)
ensures exists* (v1: Seq.seq S8.t). A.pts_to st v1 ** pure (
  Seq.length v0 == blocklen /\ SZ.v o + 4 <= blocklen /\ Seq.length v1 == blocklen /\
  (forall (j: nat). j < blocklen /\ (j < SZ.v o \/ SZ.v o + 4 <= j) ==>
     Seq.index v1 j == Seq.index v0 j) /\
  S8.v (Seq.index v1 (SZ.v o + 0)) == fmul 2 (S8.v a0) ^^ (fmul 3 (S8.v a1) ^^ (fmul 1 (S8.v a2) ^^ fmul 1 (S8.v a3))) /\
  S8.v (Seq.index v1 (SZ.v o + 1)) == fmul 1 (S8.v a0) ^^ (fmul 2 (S8.v a1) ^^ (fmul 3 (S8.v a2) ^^ fmul 1 (S8.v a3))) /\
  S8.v (Seq.index v1 (SZ.v o + 2)) == fmul 1 (S8.v a0) ^^ (fmul 1 (S8.v a1) ^^ (fmul 2 (S8.v a2) ^^ fmul 3 (S8.v a3))) /\
  S8.v (Seq.index v1 (SZ.v o + 3)) == fmul 3 (S8.v a0) ^^ (fmul 1 (S8.v a1) ^^ (fmul 1 (S8.v a2) ^^ fmul 2 (S8.v a3))))
{
  A.pts_to_len st;
  let c1 = S8.classify 1uy;
  let c2 = S8.classify 2uy;
  let c3 = S8.classify 3uy;
  A.((st.(SZ.add o 0sz) <- bxor (fmul_impl c2 a0) (bxor (fmul_impl c3 a1) (bxor (fmul_impl c1 a2) (fmul_impl c1 a3)))));
  A.((st.(SZ.add o 1sz) <- bxor (fmul_impl c1 a0) (bxor (fmul_impl c2 a1) (bxor (fmul_impl c3 a2) (fmul_impl c1 a3)))));
  A.((st.(SZ.add o 2sz) <- bxor (fmul_impl c1 a0) (bxor (fmul_impl c1 a1) (bxor (fmul_impl c2 a2) (fmul_impl c3 a3)))));
  A.((st.(SZ.add o 3sz) <- bxor (fmul_impl c3 a0) (bxor (fmul_impl c1 a1) (bxor (fmul_impl c1 a2) (fmul_impl c2 a3)))));
  A.pts_to_len st;
}

fn mix_columns_impl (st: A.array S8.t) (#v0: erased (Seq.seq S8.t))
requires A.pts_to st v0 ** pure (Seq.length v0 == blocklen)
ensures exists* (v1: Seq.seq S8.t). A.pts_to st v1 **
  pure (Seq.length v0 == blocklen /\ Seq.length v1 == blocklen /\ vals v1 == mix_columns (vals v0))
{
  A.pts_to_len st;
  let a0  = A.(st.(0sz));  let a1  = A.(st.(1sz));
  let a2  = A.(st.(2sz));  let a3  = A.(st.(3sz));
  let a4  = A.(st.(4sz));  let a5  = A.(st.(5sz));
  let a6  = A.(st.(6sz));  let a7  = A.(st.(7sz));
  let a8  = A.(st.(8sz));  let a9  = A.(st.(9sz));
  let a10 = A.(st.(10sz)); let a11 = A.(st.(11sz));
  let a12 = A.(st.(12sz)); let a13 = A.(st.(13sz));
  let a14 = A.(st.(14sz)); let a15 = A.(st.(15sz));
  mix_column_impl st 0sz  a0  a1  a2  a3;
  mix_column_impl st 4sz  a4  a5  a6  a7;
  mix_column_impl st 8sz  a8  a9  a10 a11;
  mix_column_impl st 12sz a12 a13 a14 a15;
  with v. assert A.pts_to st v;
  mix_at_0 (vals v0) (Seq.index (vals v) 0);
  mix_at_1 (vals v0) (Seq.index (vals v) 1);
  mix_at_2 (vals v0) (Seq.index (vals v) 2);
  mix_at_3 (vals v0) (Seq.index (vals v) 3);
  mix_at_4 (vals v0) (Seq.index (vals v) 4);
  mix_at_5 (vals v0) (Seq.index (vals v) 5);
  mix_at_6 (vals v0) (Seq.index (vals v) 6);
  mix_at_7 (vals v0) (Seq.index (vals v) 7);
  mix_at_8 (vals v0) (Seq.index (vals v) 8);
  mix_at_9 (vals v0) (Seq.index (vals v) 9);
  mix_at_10 (vals v0) (Seq.index (vals v) 10);
  mix_at_11 (vals v0) (Seq.index (vals v) 11);
  mix_at_12 (vals v0) (Seq.index (vals v) 12);
  mix_at_13 (vals v0) (Seq.index (vals v) 13);
  mix_at_14 (vals v0) (Seq.index (vals v) 14);
  mix_at_15 (vals v0) (Seq.index (vals v) 15);
  mix_columns_join v0 v;
  (* A Pulse function may not end with a pure statement: the last one is
     dropped.  This read of the length is the cheapest thing that is not. *)
  A.pts_to_len st;
}

#pop-options
