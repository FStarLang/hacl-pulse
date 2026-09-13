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

(** Between a number and its bytes.

    A key on the wire is a string of bytes; a number in this library is an
    array of limbs.  The four functions here convert, in both byte orders,
    and say the only thing worth saying: the number the bytes denote and the
    number the limbs denote are the same number.

    {b Lengths.}  Each function takes a limb count [n] and works on exactly
    [4n] bytes.  HACL* instead takes a byte count and rounds up, padding on
    the left.  That rounding is the caller's business here: a caller with a
    length that is not a multiple of four zeroes a [4n]-byte buffer and
    copies its bytes into the right end, which is both what the padding
    means and what the caller usually has to do anyway to own the buffer.
    Nothing in this library, and nothing in the standards it implements, has
    a key length that is not a multiple of four.

    {b Constant time.}  Byte order is a compile-time choice and the loop
    bounds are public lengths.  No byte or limb is ever branched on. *)
module Hacl.Bignum.Convert

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Bignum
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Hacl.Spec.Bytes
open Hacl.Impl.Bytes
open Hacl.Impl.Limb32
open Hacl.Bignum.Base

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32

#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"

(** An empty window is worth nothing.  Stated rather than unfolded, because
    everything below runs at zero fuel. *)
#push-options "--fuel 1"
let be_nat_empty (s: Seq.seq S8.t)
  : Lemma (requires Seq.length s == 0) (ensures be_nat s == 0) = ()
let le_nat_empty (s: Seq.seq S8.t)
  : Lemma (requires Seq.length s == 0) (ensures le_nat s == 0) = ()
#pop-options

(** {2 The four step lemmas}

    All four loops below are one line of arithmetic each, and all four of
    those lines are easier for the solver alone than inside a loop body that
    carries two arrays and a quantifier.  They are stated here in exactly
    the shape the body needs. *)

(** Reading big-endian: the window just below the cursor is worth its own
    four bytes, weighted by the limbs already read. *)
let from_be_step (vb: Seq.seq S8.t) (n: nat) (i: nat { i < n })
  : Lemma (requires Seq.length vb == 4 * n)
          (ensures be_nat (Seq.slice vb (4 * (n - i - 1)) (4 * n)) ==
                   be_nat (Seq.slice vb (4 * (n - i)) (4 * n)) +
                   wt i * be_nat (Seq.slice vb (4 * (n - i - 1)) (4 * (n - i))))
  = let s = Seq.slice vb (4 * (n - i - 1)) (4 * n) in
    be_nat_split s (4 * i);
    Seq.lemma_eq_intro (Seq.slice s 0 4) (Seq.slice vb (4 * (n - i - 1)) (4 * (n - i)));
    Seq.lemma_eq_intro (Seq.slice s 4 (4 * i + 4)) (Seq.slice vb (4 * (n - i)) (4 * n));
    assert (pow2 (8 * (4 * i)) == wt i)

(** Reading little-endian: the window just above the cursor is worth its own
    four bytes, weighted the same way. *)
let from_le_step (vb: Seq.seq S8.t) (n: nat) (i: nat { i < n })
  : Lemma (requires Seq.length vb == 4 * n)
          (ensures le_nat (Seq.slice vb 0 (4 * i + 4)) ==
                   le_nat (Seq.slice vb 0 (4 * i)) +
                   wt i * le_nat (Seq.slice vb (4 * i) (4 * i + 4)))
  = let s = Seq.slice vb 0 (4 * i + 4) in
    le_nat_split s (4 * i);
    Seq.lemma_eq_intro (Seq.slice s 0 (4 * i)) (Seq.slice vb 0 (4 * i));
    Seq.lemma_eq_intro (Seq.slice s (4 * i) (4 * i + 4)) (Seq.slice vb (4 * i) (4 * i + 4));
    assert (pow2 (8 * (4 * i)) == wt i)

(** Writing: the four bytes a window receives are the big-endian -- or the
    little-endian -- form of the limb, so the window is worth the limb. *)
let write_window_be (v: Seq.seq S8.t) (off: nat) (x: nat)
  : Lemma (requires off + 4 <= Seq.length v /\ x < pow2 32 /\
                    (forall (m: nat). m < 4 ==>
                       S8.v (Seq.index v (off + m)) == (x / pow2 (8 * (3 - m))) % 256))
          (ensures be_nat (Seq.slice v off (off + 4)) == x)
  = assert (pow2 32 == pow2 (8 * 4));
    Seq.lemma_eq_intro (Seq.slice v off (off + 4)) (nat_to_be 4 x);
    be_nat_to_be 4 x

let write_window_le (v: Seq.seq S8.t) (off: nat) (x: nat)
  : Lemma (requires off + 4 <= Seq.length v /\ x < pow2 32 /\
                    (forall (m: nat). m < 4 ==>
                       S8.v (Seq.index v (off + m)) == (x / pow2 (8 * m)) % 256))
          (ensures le_nat (Seq.slice v off (off + 4)) == x)
  = assert (pow2 32 == pow2 (8 * 4));
    Seq.lemma_eq_intro (Seq.slice v off (off + 4)) (nat_to_le 4 x);
    le_nat_to_le 4 x

(** What a write leaves alone it leaves equal. *)
let untouched (u v: Seq.seq S8.t) (lo: nat) (hi: nat { lo <= hi })
  : Lemma (requires hi <= Seq.length u /\ Seq.length v == Seq.length u /\
                    (forall (k: nat). lo <= k /\ k < hi ==> Seq.index v k == Seq.index u k))
          (ensures Seq.slice v lo hi == Seq.slice u lo hi)
  = Seq.lemma_eq_intro (Seq.slice v lo hi) (Seq.slice u lo hi)

(** A [Hacl.Secret.UInt32] read through the word class is the same value.
    The class is how the byte loops are written; [Spec.Bignum] speaks of
    limbs.  This is the one line that says the two agree. *)
let w32 (x: S32.t) : Lemma (v #S32.t x == S32.v x /\ bytes #S32.t == 4) = ()

(** {2 Bytes to limbs} *)

fn from_bytes_be (res: A.array S32.t) (n: SZ.t) (b: A.array S8.t)
                 (#p: perm) (#vres: erased (Seq.seq S32.t)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to res vres ** A.pts_to b #p vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length vb == 4 * SZ.v n /\ SZ.fits (4 * SZ.v n))
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v n /\ num v == be_nat vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  let mut i = 0sz;
  pre_zero vres;
  be_nat_empty (Seq.slice vb (4 * SZ.v n) (4 * SZ.v n));
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S32.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          pre v (SZ.v vi) == be_nat (Seq.slice vb (4 * (SZ.v n - SZ.v vi)) (4 * SZ.v n)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to res v);
    let off = SZ.mul 4sz (SZ.sub (SZ.sub n vi) 1sz);
    let w = load_be #S32.t b off;
    A.((res.(vi) <- w));
    pre_upd v (SZ.v vi) w (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) w) (SZ.v vi);
    from_be_step vb (SZ.v n) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  Seq.lemma_eq_intro (Seq.slice vb 0 (4 * SZ.v n)) vb;
  ()
}

fn from_bytes_le (res: A.array S32.t) (n: SZ.t) (b: A.array S8.t)
                 (#p: perm) (#vres: erased (Seq.seq S32.t)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to res vres ** A.pts_to b #p vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length vb == 4 * SZ.v n /\ SZ.fits (4 * SZ.v n))
ensures exists* (v: Seq.seq S32.t).
  A.pts_to res v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v n /\ num v == le_nat vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  let mut i = 0sz;
  pre_zero vres;
  le_nat_empty (Seq.slice vb 0 0);
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S32.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          pre v (SZ.v vi) == le_nat (Seq.slice vb 0 (4 * SZ.v vi)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to res v);
    let off = SZ.mul 4sz vi;
    let w = load_le #S32.t b off;
    A.((res.(vi) <- w));
    pre_upd v (SZ.v vi) w (SZ.v vi);
    pre_snoc (Seq.upd v (SZ.v vi) w) (SZ.v vi);
    from_le_step vb (SZ.v n) (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  Seq.lemma_eq_intro (Seq.slice vb 0 (4 * SZ.v n)) vb;
  ()
}

(** {2 Limbs to bytes} *)

fn to_bytes_be (b: A.array S8.t) (a: A.array S32.t) (n: SZ.t)
               (#p: perm) (#vb: erased (Seq.seq S8.t)) (#va: erased (Seq.seq S32.t))
requires A.pts_to b vb ** A.pts_to a #p va **
  pure (Seq.length vb == 4 * SZ.v n /\ Seq.length va == SZ.v n /\ SZ.fits (4 * SZ.v n))
ensures exists* (v: Seq.seq S8.t).
  A.pts_to b v ** A.pts_to a #p va **
  pure (Seq.length v == 4 * SZ.v n /\ be_nat v == num va)
{
  A.pts_to_len b;
  A.pts_to_len a;
  let mut i = 0sz;
  pre_zero va;
  be_nat_empty (Seq.slice vb (4 * SZ.v n) (4 * SZ.v n));
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #p va **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == 4 * SZ.v n /\
          be_nat (Seq.slice v (4 * (SZ.v n - SZ.v vi)) (4 * SZ.v n)) == pre va (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v0. assert (A.pts_to b v0);
    let off = SZ.mul 4sz (SZ.sub (SZ.sub n vi) 1sz);
    let x = A.(a.(vi));
    store_be #S32.t b off x;
    with v1. assert (A.pts_to b v1);
    w32 x;
    write_window_be v1 (SZ.v off) (S32.v x);
    untouched v0 v1 (4 * (SZ.v n - SZ.v vi)) (4 * SZ.v n);
    from_be_step v1 (SZ.v n) (SZ.v vi);
    pre_snoc va (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  pre_full va;
  Seq.lemma_eq_intro (Seq.slice v 0 (4 * SZ.v n)) v;
  ()
}

fn to_bytes_le (b: A.array S8.t) (a: A.array S32.t) (n: SZ.t)
               (#p: perm) (#vb: erased (Seq.seq S8.t)) (#va: erased (Seq.seq S32.t))
requires A.pts_to b vb ** A.pts_to a #p va **
  pure (Seq.length vb == 4 * SZ.v n /\ Seq.length va == SZ.v n /\ SZ.fits (4 * SZ.v n))
ensures exists* (v: Seq.seq S8.t).
  A.pts_to b v ** A.pts_to a #p va **
  pure (Seq.length v == 4 * SZ.v n /\ le_nat v == num va)
{
  A.pts_to_len b;
  A.pts_to_len a;
  let mut i = 0sz;
  pre_zero va;
  le_nat_empty (Seq.slice vb 0 0);
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #p va **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == 4 * SZ.v n /\
          le_nat (Seq.slice v 0 (4 * SZ.v vi)) == pre va (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v0. assert (A.pts_to b v0);
    let off = SZ.mul 4sz vi;
    let x = A.(a.(vi));
    store_le #S32.t b off x;
    with v1. assert (A.pts_to b v1);
    w32 x;
    write_window_le v1 (SZ.v off) (S32.v x);
    untouched v0 v1 0 (4 * SZ.v vi);
    from_le_step v1 (SZ.v n) (SZ.v vi);
    pre_snoc va (SZ.v vi);
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  pre_full va;
  Seq.lemma_eq_intro (Seq.slice v 0 (4 * SZ.v n)) v;
  ()
}

#pop-options
