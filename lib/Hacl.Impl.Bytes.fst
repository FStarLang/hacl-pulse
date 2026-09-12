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

(** Reading and writing a big-endian machine word inside a byte slice.

    One loop each, generic in the width.  Custard specializes them per
    instance, so the generated C is the usual straight-line shift-and-or once
    the trip count is a constant. *)
module Hacl.Impl.Bytes

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Secret.Word
open Hacl.Spec.Bytes

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8

(** [be_nat] of a prefix of a window is [be_nat] of the corresponding prefix of
    the underlying sequence: the window is only there to name an offset. *)
let slice_prefix (s: Seq.seq S8.t) (off: nat) (n: nat { off + n <= Seq.length s }) (k: nat { k <= n })
  : Lemma (Seq.slice (Seq.slice s off (off + n)) 0 k == Seq.slice s off (off + k))
  = Seq.lemma_eq_intro (Seq.slice (Seq.slice s off (off + n)) 0 k) (Seq.slice s off (off + k))

(** The accumulator after [k] of [n] bytes is below [pow2 (8k)], so shifting it
    up by one more byte cannot overflow a word of [8n] bits. *)
let acc_fits (#t: Type0) {| word t |} (a: t) (s: Seq.seq S8.t) (k: nat { k < bytes #t })
  : Lemma (requires v a == be_nat s /\ Seq.length s == k)
          (ensures v a * 256 < pow2 (bits #t))
  = be_nat_bound s;
    Math.pow2_le_compat (bits #t - 8) (8 * k);
    Math.pow2_plus (bits #t - 8) 8

fn load_be (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t)
           (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
returns r: t
ensures A.pts_to b #p vb **
        pure (SZ.v off + bytes #t <= Seq.length vb /\
              v r == be_nat (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)))
{
  A.pts_to_len b;
  let n = nbytes #t #w;
  let z: t = zero #t #w;
  let mut acc = z;
  let mut j = 0sz;
  slice_prefix vb (SZ.v off) (bytes #t) 0;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (a: t).
    pts_to j vj ** pts_to acc a ** A.pts_to b #p vb **
    pure (SZ.v vj <= SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vb /\
          v a == be_nat (Seq.slice vb (SZ.v off) (SZ.v off + SZ.v vj)))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let byte = A.(b.(SZ.add off vj));
    let a = !acc;
    acc_fits a (Seq.slice vb (SZ.v off) (SZ.v off + SZ.v vj)) (SZ.v vj);
    load_step a byte;
    slice_prefix vb (SZ.v off) (bytes #t) (SZ.v vj);
    slice_prefix vb (SZ.v off) (bytes #t) (SZ.v vj + 1);
    be_nat_snoc (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)) (SZ.v vj);
    acc := logor #t (shift_left a 8ul) (of_byte byte);
    j := SZ.add vj 1sz;
  };
  !acc
}

fn store_be (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t) (x: t)
            (#vb: erased (Seq.seq S8.t))
requires A.pts_to b vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
ensures exists* vb'. A.pts_to b vb' **
        pure (Seq.length vb' == Seq.length vb /\
              SZ.v off + bytes #t <= Seq.length vb' /\
              (forall (k: nat). k < bytes #t ==>
                 S8.v (Seq.index vb' (SZ.v off + k)) == (v x / pow2 (8 * (bytes #t - 1 - k))) % 256) /\
              (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + bytes #t ==>
                 Seq.index vb' k == Seq.index vb k))
{
  A.pts_to_len b;
  let n = nbytes #t #w;
  let mut cur = x;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (c: t) (vb': Seq.seq S8.t).
    pts_to j vj ** pts_to cur c ** A.pts_to b vb' **
    pure (SZ.v vj <= SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vb /\
          Seq.length vb' == Seq.length vb /\
          v c == v x / pow2 (8 * SZ.v vj) /\
          (forall (k: nat). k < SZ.v vj ==>
             S8.v (Seq.index vb' (SZ.v off + SZ.v n - 1 - k)) == (v x / pow2 (8 * k)) % 256) /\
          (forall (k: nat). k < Seq.length vb ==>
             k < SZ.v off + SZ.v n - SZ.v vj \/ k >= SZ.v off + SZ.v n ==>
             Seq.index vb' k == Seq.index vb k))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let c = !cur;
    let pos = SZ.sub (SZ.add off n) (SZ.add vj 1sz);
    A.((b.(pos) <- to_byte c));
    store_step x c (SZ.v vj);
    cur := shift_right #t c 8ul;
    j := SZ.add vj 1sz;
  }
}

(** {2 The same, little end first}

    [load_le] reads the bytes from the top of the word down, so the
    accumulator holds the value of the *suffix* of the window read so far and
    each step multiplies by 256 and adds one more byte -- the same shape as
    [load_be], with the window traversed the other way.  [store_le] is
    simpler than [store_be]: the low byte comes first, so the write index
    advances with the loop counter instead of retreating. *)

let slice_suffix (s: Seq.seq S8.t) (off: nat) (n: nat { off + n <= Seq.length s }) (k: nat { k <= n })
  : Lemma (Seq.slice (Seq.slice s off (off + n)) k n == Seq.slice s (off + k) (off + n))
  = Seq.lemma_eq_intro (Seq.slice (Seq.slice s off (off + n)) k n) (Seq.slice s (off + k) (off + n))

let acc_fits_le (#t: Type0) {| word t |} (a: t) (s: Seq.seq S8.t) (k: nat { k < bytes #t })
  : Lemma (requires v a == le_nat s /\ Seq.length s == k)
          (ensures v a * 256 < pow2 (bits #t))
  = le_nat_bound s;
    Math.pow2_le_compat (bits #t - 8) (8 * k);
    Math.pow2_plus (bits #t - 8) 8

fn load_le (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t)
           (#p: perm) (#vb: erased (Seq.seq S8.t))
requires A.pts_to b #p vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
returns r: t
ensures A.pts_to b #p vb **
        pure (SZ.v off + bytes #t <= Seq.length vb /\
              v r == le_nat (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)))
{
  A.pts_to_len b;
  let n = nbytes #t #w;
  let z: t = zero #t #w;
  let mut acc = z;
  let mut j = 0sz;
  slice_suffix vb (SZ.v off) (bytes #t) (bytes #t);
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (a: t).
    pts_to j vj ** pts_to acc a ** A.pts_to b #p vb **
    pure (SZ.v vj <= SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vb /\
          v a == le_nat (Seq.slice vb (SZ.v off + SZ.v n - SZ.v vj) (SZ.v off + SZ.v n)))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let pos = SZ.sub (SZ.add off n) (SZ.add vj 1sz);
    let byte = A.(b.(pos));
    let a = !acc;
    acc_fits_le a (Seq.slice vb (SZ.v off + SZ.v n - SZ.v vj) (SZ.v off + SZ.v n)) (SZ.v vj);
    load_step a byte;
    slice_suffix vb (SZ.v off) (bytes #t) (SZ.v n - SZ.v vj);
    slice_suffix vb (SZ.v off) (bytes #t) (SZ.v n - SZ.v vj - 1);
    le_nat_cons (Seq.slice vb (SZ.v off) (SZ.v off + bytes #t)) (SZ.v n - SZ.v vj - 1);
    acc := logor #t (shift_left a 8ul) (of_byte byte);
    j := SZ.add vj 1sz;
  };
  !acc
}

fn store_le (#t: Type0) {| w: word t |} (b: A.array S8.t) (off: SZ.t) (x: t)
            (#vb: erased (Seq.seq S8.t))
requires A.pts_to b vb ** pure (SZ.v off + bytes #t <= Seq.length vb)
ensures exists* vb'. A.pts_to b vb' **
        pure (Seq.length vb' == Seq.length vb /\
              SZ.v off + bytes #t <= Seq.length vb' /\
              (forall (k: nat). k < bytes #t ==>
                 S8.v (Seq.index vb' (SZ.v off + k)) == (v x / pow2 (8 * k)) % 256) /\
              (forall (k: nat). k < Seq.length vb ==> k < SZ.v off \/ k >= SZ.v off + bytes #t ==>
                 Seq.index vb' k == Seq.index vb k))
{
  A.pts_to_len b;
  let n = nbytes #t #w;
  let mut cur = x;
  let mut j = 0sz;
  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (c: t) (vb': Seq.seq S8.t).
    pts_to j vj ** pts_to cur c ** A.pts_to b vb' **
    pure (SZ.v vj <= SZ.v n /\ SZ.v off + SZ.v n <= Seq.length vb /\
          Seq.length vb' == Seq.length vb /\
          v c == v x / pow2 (8 * SZ.v vj) /\
          (forall (k: nat). k < SZ.v vj ==>
             S8.v (Seq.index vb' (SZ.v off + k)) == (v x / pow2 (8 * k)) % 256) /\
          (forall (k: nat). k < Seq.length vb ==>
             k < SZ.v off \/ k >= SZ.v off + SZ.v vj ==>
             Seq.index vb' k == Seq.index vb k))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    let c = !cur;
    A.((b.(SZ.add off vj) <- to_byte c));
    store_step x c (SZ.v vj);
    cur := shift_right #t c 8ul;
    j := SZ.add vj 1sz;
  }
}
