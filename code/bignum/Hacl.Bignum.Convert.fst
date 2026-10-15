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
    [8n] bytes.  HACL* instead takes a byte count and rounds up, padding on
    the left.  That rounding is the caller's business here: a caller with a
    length that is not a multiple of eight zeroes a [8n]-byte buffer and
    copies its bytes into the right end, which is both what the padding
    means and what the caller usually has to do anyway to own the buffer.
    Nothing in this library, and nothing in the standards it implements, has
    a key length that is not a multiple of eight.

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
open Hacl.Impl.Limb64
open Hacl.Bignum.Base

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64

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
  : Lemma (requires Seq.length vb == 8 * n)
          (ensures be_nat (Seq.slice vb (8 * (n - i - 1)) (8 * n)) ==
                   be_nat (Seq.slice vb (8 * (n - i)) (8 * n)) +
                   wt i * be_nat (Seq.slice vb (8 * (n - i - 1)) (8 * (n - i))))
  = let s = Seq.slice vb (8 * (n - i - 1)) (8 * n) in
    be_nat_split s (8 * i);
    Seq.lemma_eq_intro (Seq.slice s 0 8) (Seq.slice vb (8 * (n - i - 1)) (8 * (n - i)));
    Seq.lemma_eq_intro (Seq.slice s 8 (8 * i + 8)) (Seq.slice vb (8 * (n - i)) (8 * n));
    assert (pow2 (8 * (8 * i)) == wt i)

(** Reading little-endian: the window just above the cursor is worth its own
    four bytes, weighted the same way. *)
let from_le_step (vb: Seq.seq S8.t) (n: nat) (i: nat { i < n })
  : Lemma (requires Seq.length vb == 8 * n)
          (ensures le_nat (Seq.slice vb 0 (8 * i + 8)) ==
                   le_nat (Seq.slice vb 0 (8 * i)) +
                   wt i * le_nat (Seq.slice vb (8 * i) (8 * i + 8)))
  = let s = Seq.slice vb 0 (8 * i + 8) in
    le_nat_split s (8 * i);
    Seq.lemma_eq_intro (Seq.slice s 0 (8 * i)) (Seq.slice vb 0 (8 * i));
    Seq.lemma_eq_intro (Seq.slice s (8 * i) (8 * i + 8)) (Seq.slice vb (8 * i) (8 * i + 8));
    assert (pow2 (8 * (8 * i)) == wt i)

(** Writing: the four bytes a window receives are the big-endian -- or the
    little-endian -- form of the limb, so the window is worth the limb. *)
let write_window_be (v: Seq.seq S8.t) (off: nat) (x: nat)
  : Lemma (requires off + 8 <= Seq.length v /\ x < pow2 64 /\
                    (forall (m: nat). m < 8 ==>
                       S8.v (Seq.index v (off + m)) == (x / pow2 (8 * (7 - m))) % 256))
          (ensures be_nat (Seq.slice v off (off + 8)) == x)
  = assert (pow2 64 == pow2 (8 * 8));
    Seq.lemma_eq_intro (Seq.slice v off (off + 8)) (nat_to_be 8 x);
    be_nat_to_be 8 x

let write_window_le (v: Seq.seq S8.t) (off: nat) (x: nat)
  : Lemma (requires off + 8 <= Seq.length v /\ x < pow2 64 /\
                    (forall (m: nat). m < 8 ==>
                       S8.v (Seq.index v (off + m)) == (x / pow2 (8 * m)) % 256))
          (ensures le_nat (Seq.slice v off (off + 8)) == x)
  = assert (pow2 64 == pow2 (8 * 8));
    Seq.lemma_eq_intro (Seq.slice v off (off + 8)) (nat_to_le 8 x);
    le_nat_to_le 8 x

(** What a write leaves alone it leaves equal. *)
let untouched (u v: Seq.seq S8.t) (lo: nat) (hi: nat { lo <= hi })
  : Lemma (requires hi <= Seq.length u /\ Seq.length v == Seq.length u /\
                    (forall (k: nat). lo <= k /\ k < hi ==> Seq.index v k == Seq.index u k))
          (ensures Seq.slice v lo hi == Seq.slice u lo hi)
  = Seq.lemma_eq_intro (Seq.slice v lo hi) (Seq.slice u lo hi)

(** One step of each writing loop, stated whole so the loop body only has
    to supply its facts, not re-derive the invariant. *)
let to_be_step (v0 v1: Seq.seq S8.t) (va: Seq.seq S64.t) (n: nat) (i: nat { i < n })
  : Lemma (requires Seq.length v0 == 8 * n /\ Seq.length v1 == 8 * n /\ Seq.length va == n /\
                    be_nat (Seq.slice v0 (8 * (n - i)) (8 * n)) == pre va i /\
                    Seq.slice v1 (8 * (n - i)) (8 * n) == Seq.slice v0 (8 * (n - i)) (8 * n) /\
                    be_nat (Seq.slice v1 (8 * (n - i - 1)) (8 * (n - i))) == S64.v (Seq.index va i))
          (ensures be_nat (Seq.slice v1 (8 * (n - (i + 1))) (8 * n)) == pre va (i + 1))
  = from_be_step v1 n i;
    pre_snoc va i

let to_le_step (v0 v1: Seq.seq S8.t) (va: Seq.seq S64.t) (n: nat) (i: nat { i < n })
  : Lemma (requires Seq.length v0 == 8 * n /\ Seq.length v1 == 8 * n /\ Seq.length va == n /\
                    le_nat (Seq.slice v0 0 (8 * i)) == pre va i /\
                    Seq.slice v1 0 (8 * i) == Seq.slice v0 0 (8 * i) /\
                    le_nat (Seq.slice v1 (8 * i) (8 * i + 8)) == S64.v (Seq.index va i))
          (ensures le_nat (Seq.slice v1 0 (8 * (i + 1))) == pre va (i + 1))
  = from_le_step v1 n i;
    pre_snoc va i

(** A [Hacl.Secret.UInt64] read through the word class is the same value.
    The class is how the byte loops are written; [Spec.Bignum] speaks of
    limbs.  This is the one line that says the two agree. *)
let w64 (x: S64.t) : Lemma (v #S64.t x == S64.v x /\ bytes #S64.t == 8) = ()

(** {2 Whole loop bodies}

    Each loop body below hands its facts, exactly as the load or store
    returned them, to one of these, and gets back the invariant at [i + 1].
    Keeping this out of the Pulse body keeps the solver's context small. *)
let from_be_body (vb: Seq.seq S8.t) (vr: Seq.seq S64.t) (n: nat) (i: nat { i < n })
                 (off: nat) (w: S64.t)
  : Lemma (requires Seq.length vb == 8 * n /\ Seq.length vr == n /\ off == 8 * (n - i - 1) /\
                    pre vr i == be_nat (Seq.slice vb (8 * (n - i)) (8 * n)) /\
                    off + bytes #S64.t <= Seq.length vb /\
                    v w == be_nat (Seq.slice vb off (off + bytes #S64.t)))
          (ensures pre (Seq.upd vr i w) (i + 1) ==
                   be_nat (Seq.slice vb (8 * (n - (i + 1))) (8 * n)))
  = w64 w;
    pre_upd vr i w i;
    pre_snoc (Seq.upd vr i w) i;
    from_be_step vb n i

let from_le_body (vb: Seq.seq S8.t) (vr: Seq.seq S64.t) (n: nat) (i: nat { i < n })
                 (off: nat) (w: S64.t)
  : Lemma (requires Seq.length vb == 8 * n /\ Seq.length vr == n /\ off == 8 * i /\
                    pre vr i == le_nat (Seq.slice vb 0 (8 * i)) /\
                    off + bytes #S64.t <= Seq.length vb /\
                    v w == le_nat (Seq.slice vb off (off + bytes #S64.t)))
          (ensures pre (Seq.upd vr i w) (i + 1) == le_nat (Seq.slice vb 0 (8 * (i + 1))))
  = w64 w;
    pre_upd vr i w i;
    pre_snoc (Seq.upd vr i w) i;
    from_le_step vb n i

let to_be_body (v0 v1: Seq.seq S8.t) (va: Seq.seq S64.t) (n: nat) (i: nat { i < n })
               (off: nat) (x: S64.t)
  : Lemma (requires Seq.length v0 == 8 * n /\ Seq.length va == n /\ off == 8 * (n - i - 1) /\
                    x == Seq.index va i /\
                    be_nat (Seq.slice v0 (8 * (n - i)) (8 * n)) == pre va i /\
                    Seq.length v1 == Seq.length v0 /\ off + bytes #S64.t <= Seq.length v1 /\
                    (forall (k: nat). k < bytes #S64.t ==>
                       S8.v (Seq.index v1 (off + k)) ==
                       (v x / pow2 (8 * (bytes #S64.t - 1 - k))) % 256) /\
                    (forall (k: nat). k < Seq.length v0 ==> k < off \/ k >= off + bytes #S64.t ==>
                       Seq.index v1 k == Seq.index v0 k))
          (ensures Seq.length v1 == 8 * n /\
                   be_nat (Seq.slice v1 (8 * (n - (i + 1))) (8 * n)) == pre va (i + 1))
  = w64 x;
    write_window_be v1 off (S64.v x);
    untouched v0 v1 (8 * (n - i)) (8 * n);
    to_be_step v0 v1 va n i

let to_le_body (v0 v1: Seq.seq S8.t) (va: Seq.seq S64.t) (n: nat) (i: nat { i < n })
               (off: nat) (x: S64.t)
  : Lemma (requires Seq.length v0 == 8 * n /\ Seq.length va == n /\ off == 8 * i /\
                    x == Seq.index va i /\
                    le_nat (Seq.slice v0 0 (8 * i)) == pre va i /\
                    Seq.length v1 == Seq.length v0 /\ off + bytes #S64.t <= Seq.length v1 /\
                    (forall (k: nat). k < bytes #S64.t ==>
                       S8.v (Seq.index v1 (off + k)) == (v x / pow2 (8 * k)) % 256) /\
                    (forall (k: nat). k < Seq.length v0 ==> k < off \/ k >= off + bytes #S64.t ==>
                       Seq.index v1 k == Seq.index v0 k))
          (ensures Seq.length v1 == 8 * n /\
                   le_nat (Seq.slice v1 0 (8 * (i + 1))) == pre va (i + 1))
  = w64 x;
    write_window_le v1 off (S64.v x);
    untouched v0 v1 0 (8 * i);
    to_le_step v0 v1 va n i

(** {2 Bytes to limbs} *)

fn from_bytes_be (res: A.array S64.t) (n: SZ.t) (b: A.array S8.t)
                 (#p: perm) (#vres: erased (Seq.seq S64.t)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to res vres ** A.pts_to b #p vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length vb == 8 * SZ.v n /\ SZ.fits (8 * SZ.v n))
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v n /\ num v == be_nat vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  let mut i = 0sz;
  pre_zero vres;
  be_nat_empty (Seq.slice vb (8 * SZ.v n) (8 * SZ.v n));
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          pre v (SZ.v vi) == be_nat (Seq.slice vb (8 * (SZ.v n - SZ.v vi)) (8 * SZ.v n)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to res v);
    let off = SZ.mul 8sz (SZ.sub (SZ.sub n vi) 1sz);
    assert (pure (SZ.v off == 8 * (SZ.v n - SZ.v vi - 1)));
    let w = load_be #S64.t b off;
    A.((res.(vi) <- w));
    from_be_body vb v (SZ.v n) (SZ.v vi) (SZ.v off) w;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  Seq.lemma_eq_intro (Seq.slice vb 0 (8 * SZ.v n)) vb;
  ()
}

fn from_bytes_le (res: A.array S64.t) (n: SZ.t) (b: A.array S8.t)
                 (#p: perm) (#vres: erased (Seq.seq S64.t)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to res vres ** A.pts_to b #p vb **
  pure (Seq.length vres == SZ.v n /\ Seq.length vb == 8 * SZ.v n /\ SZ.fits (8 * SZ.v n))
ensures exists* (v: Seq.seq S64.t).
  A.pts_to res v ** A.pts_to b #p vb **
  pure (Seq.length v == SZ.v n /\ num v == le_nat vb)
{
  A.pts_to_len res;
  A.pts_to_len b;
  let mut i = 0sz;
  pre_zero vres;
  le_nat_empty (Seq.slice vb 0 0);
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S64.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == SZ.v n /\
          pre v (SZ.v vi) == le_nat (Seq.slice vb 0 (8 * SZ.v vi)))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v. assert (A.pts_to res v);
    let off = SZ.mul 8sz vi;
    assert (pure (SZ.v off == 8 * SZ.v vi));
    let w = load_le #S64.t b off;
    A.((res.(vi) <- w));
    from_le_body vb v (SZ.v n) (SZ.v vi) (SZ.v off) w;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  pre_full v;
  Seq.lemma_eq_intro (Seq.slice vb 0 (8 * SZ.v n)) vb;
  ()
}

(** {2 Limbs to bytes} *)

fn to_bytes_be (b: A.array S8.t) (a: A.array S64.t) (n: SZ.t)
               (#p: perm) (#vb: erased (Seq.seq S8.t)) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #p va **
  pure (Seq.length vb == 8 * SZ.v n /\ Seq.length va == SZ.v n /\ SZ.fits (8 * SZ.v n))
ensures exists* (v: Seq.seq S8.t).
  A.pts_to b v ** A.pts_to a #p va **
  pure (Seq.length v == 8 * SZ.v n /\ be_nat v == num va)
{
  A.pts_to_len b;
  A.pts_to_len a;
  let mut i = 0sz;
  pre_zero va;
  be_nat_empty (Seq.slice vb (8 * SZ.v n) (8 * SZ.v n));
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #p va **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == 8 * SZ.v n /\
          be_nat (Seq.slice v (8 * (SZ.v n - SZ.v vi)) (8 * SZ.v n)) == pre va (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v0. assert (A.pts_to b v0);
    let off = SZ.mul 8sz (SZ.sub (SZ.sub n vi) 1sz);
    assert (pure (SZ.v off == 8 * (SZ.v n - SZ.v vi - 1)));
    let x = A.(a.(vi));
    store_be #S64.t b off x;
    with v1. assert (A.pts_to b v1);
    to_be_body v0 v1 va (SZ.v n) (SZ.v vi) (SZ.v off) x;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  pre_full va;
  Seq.lemma_eq_intro (Seq.slice v 0 (8 * SZ.v n)) v;
  ()
}

fn to_bytes_le (b: A.array S8.t) (a: A.array S64.t) (n: SZ.t)
               (#p: perm) (#vb: erased (Seq.seq S8.t)) (#va: erased (Seq.seq S64.t))
requires A.pts_to b vb ** A.pts_to a #p va **
  pure (Seq.length vb == 8 * SZ.v n /\ Seq.length va == SZ.v n /\ SZ.fits (8 * SZ.v n))
ensures exists* (v: Seq.seq S8.t).
  A.pts_to b v ** A.pts_to a #p va **
  pure (Seq.length v == 8 * SZ.v n /\ le_nat v == num va)
{
  A.pts_to_len b;
  A.pts_to_len a;
  let mut i = 0sz;
  pre_zero va;
  le_nat_empty (Seq.slice vb 0 0);
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to b v ** A.pts_to a #p va **
    pure (SZ.v vi <= SZ.v n /\ Seq.length v == 8 * SZ.v n /\
          le_nat (Seq.slice v 0 (8 * SZ.v vi)) == pre va (SZ.v vi))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    with v0. assert (A.pts_to b v0);
    let off = SZ.mul 8sz vi;
    assert (pure (SZ.v off == 8 * SZ.v vi));
    let x = A.(a.(vi));
    store_le #S64.t b off x;
    with v1. assert (A.pts_to b v1);
    to_le_body v0 v1 va (SZ.v n) (SZ.v vi) (SZ.v off) x;
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to b v);
  pre_full va;
  Seq.lemma_eq_intro (Seq.slice v 0 (8 * SZ.v n)) v;
  ()
}

#pop-options
