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

(** Matrices of secret sixteen-bit words, in row-major order.

    A matrix is a flat array; its dimensions travel as ordinary arguments,
    not as type indices, because the unifier cannot recover [r] and [c] from
    a length of [r * c] and because the callers hold their dimensions in
    [SizeT] anyway.

    Everything here is modulo [2^16].  FrodoKEM's modulus is [2^logq] with
    [logq] fifteen or sixteen, and the reduction to [logq] bits happens only
    where the specification asks for it -- at packing time, and in the
    re-encryption check. *)
module Hacl.Frodo.Matrix

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module M = Spec.Frodo.Matrix
module Loops = Hacl.Spec.Loops

(** The three pointwise operations, from their flat-index characterization.
    The loops below establish exactly the hypothesis of these lemmas. *)

let add_eq (r: nat) (c: pos) (a b res: M.matrix r c)
  : Lemma (requires forall (t: nat). t < r * c ==>
                      Seq.index res t == S16.add_mod (Seq.index a t) (Seq.index b t))
          (ensures res == M.add r c a b)
  = FStar.Classical.forall_intro (M.add_index r c a b);
    Seq.lemma_eq_intro res (M.add r c a b)

let sub_eq (r: nat) (c: pos) (a b res: M.matrix r c)
  : Lemma (requires forall (t: nat). t < r * c ==>
                      Seq.index res t == S16.sub_mod (Seq.index a t) (Seq.index b t))
          (ensures res == M.sub r c a b)
  = FStar.Classical.forall_intro (M.sub_index r c a b);
    Seq.lemma_eq_intro res (M.sub r c a b)

let mod_pow2_eq (r: nat) (c: pos) (d: U32.t { U32.v d <= 16 }) (m res: M.matrix r c)
  : Lemma (requires forall (t: nat). t < r * c ==>
                      Seq.index res t == S16.logand (Seq.index m t) (S16.mask_low d))
          (ensures res == M.mod_pow2 r c d m)
  = FStar.Classical.forall_intro (M.mod_pow2_index r c d m);
    Seq.lemma_eq_intro res (M.mod_pow2 r c d m)

(** Serialization at a flat index: the loop writes the two bytes of entry
    [k] at [2k] and [2k+1], and every byte offset is of one of those two
    shapes. *)
let to_bytes_eq (r c: nat) (m: M.matrix r c) (res: Seq.lseq S8.t (2 * (r * c)))
  : Lemma (requires forall (k: nat). k < r * c ==>
                      Seq.index res (2 * k) == S16.lo (Seq.index m k) /\
                      Seq.index res (2 * k + 1) == S16.hi (Seq.index m k))
          (ensures res == M.to_bytes r c m)
  = let aux (t: nat { t < 2 * (r * c) })
      : Lemma (Seq.index res t == Seq.index (M.to_bytes r c m) t)
      = M.div_lt t (r * c) 2;
        FStar.Math.Lemmas.euclidean_division_definition t 2
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro res (M.to_bytes r c m)

#push-options "--z3rlimit 1000 --fuel 1 --ifuel 1"

(** [a <- a + b]. *)
fn add (a: A.array S16.t) (b: A.array S16.t) (len: SZ.t)
       (#r: erased nat) (#c: erased pos) (#p: perm)
       (#va: erased (M.matrix r c)) (#vb: erased (M.matrix r c))
requires A.pts_to a va ** A.pts_to b #p vb ** pure (SZ.v len == reveal r * reveal c)
ensures exists* v. A.pts_to a v ** A.pts_to b #p vb **
        pure (v == M.add r c va vb)
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v k == S16.add_mod (Seq.index va k) (Seq.index vb k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < SZ.v len ==>
             Seq.index v k == Seq.index va k))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((a.(vi) <- S16.add_mod x y));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to a v);
  assert (pure (Seq.length v == reveal r * reveal c /\
                (forall (t: nat). t < reveal r * reveal c ==>
                   Seq.index v t == S16.add_mod (Seq.index va t) (Seq.index vb t))));
  add_eq r c va vb v;
  assert (pure (v == M.add r c va vb));
}

(** [a <- a - b]. *)
fn sub (a: A.array S16.t) (b: A.array S16.t) (len: SZ.t)
       (#r: erased nat) (#c: erased pos) (#p: perm)
       (#va: erased (M.matrix r c)) (#vb: erased (M.matrix r c))
requires A.pts_to a va ** A.pts_to b #p vb ** pure (SZ.v len == reveal r * reveal c)
ensures exists* v. A.pts_to a v ** A.pts_to b #p vb **
        pure (v == M.sub r c va vb)
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to a v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v k == S16.sub_mod (Seq.index va k) (Seq.index vb k)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < SZ.v len ==>
             Seq.index v k == Seq.index va k))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    A.((a.(vi) <- S16.sub_mod x y));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to a v);
  assert (pure (Seq.length v == reveal r * reveal c /\
                (forall (t: nat). t < reveal r * reveal c ==>
                   Seq.index v t == S16.sub_mod (Seq.index va t) (Seq.index vb t))));
  sub_eq r c va vb v;
  assert (pure (v == M.sub r c va vb));
}

(** [a <- a mod 2^d], in place. *)
fn mod_pow2 (a: A.array S16.t) (len: SZ.t) (d: U32.t { U32.v d <= 16 })
            (#r: erased nat) (#c: erased pos) (#va: erased (M.matrix r c))
requires A.pts_to a va ** pure (SZ.v len == reveal r * reveal c)
ensures exists* v. A.pts_to a v ** pure (v == M.mod_pow2 r c d va)
{
  A.pts_to_len a;
  let mask = S16.mask_low d;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to a v **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v k == S16.logand (Seq.index va k) (S16.mask_low d)) /\
          (forall (k: nat). SZ.v vi <= k /\ k < SZ.v len ==>
             Seq.index v k == Seq.index va k))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(a.(vi));
    A.((a.(vi) <- S16.logand x mask));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to a v);
  assert (pure (Seq.length v == reveal r * reveal c /\
                (forall (t: nat). t < reveal r * reveal c ==>
                   Seq.index v t == S16.logand (Seq.index va t) (S16.mask_low d))));
  mod_pow2_eq r c d va v;
  assert (pure (v == M.mod_pow2 r c d va));
}

(** {2 Serialization}

    Two little-endian bytes per entry, in storage order.  Used only for the
    secret matrix inside the secret key; everything on the wire is packed. *)

fn to_bytes (out: A.array S8.t) (m: A.array S16.t) (len: SZ.t)
            (#r: erased nat) (#c: erased nat) (#p: perm)
            (#vo: erased (Seq.seq S8.t)) (#vm: erased (M.matrix r c))
requires A.pts_to out vo ** A.pts_to m #p vm **
         pure (SZ.v len == reveal r * reveal c /\ Seq.length vo == 2 * SZ.v len /\
               SZ.fits (2 * SZ.v len))
ensures exists* v. A.pts_to out v ** A.pts_to m #p vm **
        pure (v == M.to_bytes r c vm)
{
  A.pts_to_len out;
  A.pts_to_len m;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to out v ** A.pts_to m #p vm **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == 2 * SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v (2 * k) == S16.lo (Seq.index vm k) /\
             Seq.index v (2 * k + 1) == S16.hi (Seq.index vm k)))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(m.(vi));
    let j = SZ.mul 2sz vi;
    A.((out.(j) <- S16.lo x));
    A.((out.(SZ.add j 1sz) <- S16.hi x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to out v);
  assert (pure (Seq.length v == 2 * (reveal r * reveal c) /\
                (forall (k: nat). k < reveal r * reveal c ==>
                   Seq.index v (2 * k) == S16.lo (Seq.index vm k) /\
                   Seq.index v (2 * k + 1) == S16.hi (Seq.index vm k))));
  to_bytes_eq r c vm v;
  assert (pure (v == M.to_bytes r c vm));
}

fn from_bytes (m: A.array S16.t) (b: A.array S8.t) (len: SZ.t)
              (#r: erased nat) (#c: erased nat) (#p: perm)
              (#vm: erased (Seq.seq S16.t)) (#vb: erased (Seq.lseq S8.t (2 * (r * c))))
requires A.pts_to m vm ** A.pts_to b #p vb **
         pure (SZ.v len == reveal r * reveal c /\ Seq.length vm == SZ.v len /\
               SZ.fits (2 * SZ.v len))
ensures exists* v. A.pts_to m v ** A.pts_to b #p vb **
        pure (v == M.from_bytes r c vb)
{
  A.pts_to_len m;
  A.pts_to_len b;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to m v ** A.pts_to b #p vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v k == S16.of_bytes_le (Seq.index vb (2 * k)) (Seq.index vb (2 * k + 1))))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let j = SZ.mul 2sz vi;
    let lo = A.(b.(j));
    let hi = A.(b.(SZ.add j 1sz));
    A.((m.(vi) <- S16.of_bytes_le lo hi));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to m v);
  assert (pure (Seq.length v == reveal r * reveal c /\
                (forall (k: nat). k < reveal r * reveal c ==>
                   Seq.index v k ==
                     S16.of_bytes_le (Seq.index vb (2 * k)) (Seq.index vb (2 * k + 1)))));
  Seq.lemma_eq_intro v (M.from_bytes r c vb);
  assert (pure (v == M.from_bytes r c vb));
}

(** {2 Products}

    The two dot products, then the two double loops over them.  Both are
    only ever used on the small shapes -- eight by [n] against [n] by eight
    -- because the two products with A in them stream A row by row instead
    of materializing it; see [Hacl.Frodo.Gen]. *)

let mul_eq (r k: nat) (c: pos) (a: M.matrix r k) (b: M.matrix k c) (res: M.matrix r c)
  : Lemma (requires forall (i: nat) (j: nat). i < r /\ j < c ==>
                      Seq.index res (i * c + j) == M.dot r k c a b i j)
          (ensures res == M.mul r k c a b)
  = let aux (t: nat { t < r * c })
      : Lemma (Seq.index res t == Seq.index (M.mul r k c a b) t)
      = M.div_lt t r c;
        FStar.Math.Lemmas.euclidean_division_definition t c
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro res (M.mul r k c a b)

let mul_t_eq (r k: nat) (c: pos) (a: M.matrix r k) (bt: M.matrix c k) (res: M.matrix r c)
  : Lemma (requires forall (i: nat) (j: nat). i < r /\ j < c ==>
                      Seq.index res (i * c + j) == M.dot_t r k c a bt i j)
          (ensures res == M.mul_t r k c a bt)
  = let aux (t: nat { t < r * c })
      : Lemma (Seq.index res t == Seq.index (M.mul_t r k c a bt) t)
      = M.div_lt t r c;
        FStar.Math.Lemmas.euclidean_division_definition t c
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro res (M.mul_t r k c a bt)

#push-options "--z3rlimit 800 --fuel 1 --ifuel 1"

fn dot (a: A.array S16.t) (b: A.array S16.t) (r k c: SZ.t) (i: SZ.t) (j: SZ.t)
       (#pa: perm) (#pb: perm)
       (#va: erased (M.matrix (SZ.v r) (SZ.v k))) (#vb: erased (M.matrix (SZ.v k) (SZ.v c)))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (SZ.v i < SZ.v r /\ SZ.v j < SZ.v c /\
               SZ.fits (SZ.v r * SZ.v k) /\ SZ.fits (SZ.v k * SZ.v c))
returns x: S16.t
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (x == M.dot (SZ.v r) (SZ.v k) (SZ.v c) va vb (SZ.v i) (SZ.v j))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut acc = S16.zero;
  let mut l = 0sz;
  while (let vl = !l; SZ.lt vl k)
  invariant exists* (vl: SZ.t) (vacc: S16.t).
    pts_to l vl ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vl <= SZ.v k /\
          vacc == Loops.repeati (SZ.v vl)
                    (M.dot_step (SZ.v r) (SZ.v k) (SZ.v c) va vb (SZ.v i) (SZ.v j)) S16.zero)
  decreases (SZ.v k - SZ.v (!l))
  {
    let vl = !l;
    let vacc = !acc;
    let x = A.(a.(SZ.add (SZ.mul i k) vl));
    let y = A.(b.(SZ.add (SZ.mul vl c) j));
    Loops.unfold_repeati (SZ.v vl)
      (M.dot_step (SZ.v r) (SZ.v k) (SZ.v c) va vb (SZ.v i) (SZ.v j)) S16.zero;
    acc := S16.add_mod vacc (S16.mul_mod x y);
    l := SZ.add vl 1sz;
  };
  !acc
}

fn dot_t (a: A.array S16.t) (bt: A.array S16.t) (r k c: SZ.t) (i: SZ.t) (j: SZ.t)
         (#pa: perm) (#pb: perm)
         (#va: erased (M.matrix (SZ.v r) (SZ.v k))) (#vb: erased (M.matrix (SZ.v c) (SZ.v k)))
requires A.pts_to a #pa va ** A.pts_to bt #pb vb **
         pure (SZ.v i < SZ.v r /\ SZ.v j < SZ.v c /\
               SZ.fits (SZ.v r * SZ.v k) /\ SZ.fits (SZ.v c * SZ.v k))
returns x: S16.t
ensures A.pts_to a #pa va ** A.pts_to bt #pb vb **
        pure (x == M.dot_t (SZ.v r) (SZ.v k) (SZ.v c) va vb (SZ.v i) (SZ.v j))
{
  A.pts_to_len a;
  A.pts_to_len bt;
  let mut acc = S16.zero;
  let mut l = 0sz;
  while (let vl = !l; SZ.lt vl k)
  invariant exists* (vl: SZ.t) (vacc: S16.t).
    pts_to l vl ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to bt #pb vb **
    pure (SZ.v vl <= SZ.v k /\
          vacc == Loops.repeati (SZ.v vl)
                    (M.dot_t_step (SZ.v r) (SZ.v k) (SZ.v c) va vb (SZ.v i) (SZ.v j)) S16.zero)
  decreases (SZ.v k - SZ.v (!l))
  {
    let vl = !l;
    let vacc = !acc;
    let x = A.(a.(SZ.add (SZ.mul i k) vl));
    let y = A.(bt.(SZ.add (SZ.mul j k) vl));
    Loops.unfold_repeati (SZ.v vl)
      (M.dot_t_step (SZ.v r) (SZ.v k) (SZ.v c) va vb (SZ.v i) (SZ.v j)) S16.zero;
    acc := S16.add_mod vacc (S16.mul_mod x y);
    l := SZ.add vl 1sz;
  };
  !acc
}

(** [res <- a * b]. *)
fn mul (res: A.array S16.t) (a: A.array S16.t) (b: A.array S16.t)
       (r: SZ.t) (k: SZ.t) (c: SZ.t { 0 < SZ.v c })
       (#pa: perm) (#pb: perm) (#vres: erased (Seq.seq S16.t))
       (#va: erased (M.matrix (SZ.v r) (SZ.v k))) (#vb: erased (M.matrix (SZ.v k) (SZ.v c)))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length vres == SZ.v r * SZ.v c /\
               SZ.fits (SZ.v r * SZ.v k) /\ SZ.fits (SZ.v k * SZ.v c) /\
               SZ.fits (SZ.v r * SZ.v c))
ensures exists* v. A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure (v == M.mul (SZ.v r) (SZ.v k) (SZ.v c) va vb)
{
  A.pts_to_len res;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi r)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v r /\ Seq.length v == SZ.v r * SZ.v c /\
          (forall (ii: nat) (jj: nat). ii < SZ.v vi /\ jj < SZ.v c ==>
             Seq.index v (ii * SZ.v c + jj) ==
               M.dot (SZ.v r) (SZ.v k) (SZ.v c) va vb ii jj))
  decreases (SZ.v r - SZ.v (!i))
  {
    let vi = !i;
    let mut j = 0sz;
    while (let vj = !j; SZ.lt vj c)
    invariant exists* (vj: SZ.t) (v: Seq.seq S16.t).
      pts_to i vi ** pts_to j vj ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to b #pb vb **
      pure (SZ.v vi < SZ.v r /\ SZ.v vj <= SZ.v c /\ Seq.length v == SZ.v r * SZ.v c /\
            (forall (ii: nat) (jj: nat). ii < SZ.v vi /\ jj < SZ.v c ==>
               Seq.index v (ii * SZ.v c + jj) ==
                 M.dot (SZ.v r) (SZ.v k) (SZ.v c) va vb ii jj) /\
            (forall (jj: nat). jj < SZ.v vj ==>
               Seq.index v (SZ.v vi * SZ.v c + jj) ==
                 M.dot (SZ.v r) (SZ.v k) (SZ.v c) va vb (SZ.v vi) jj))
    decreases (SZ.v c - SZ.v (!j))
    {
      let vj = !j;
      let x = dot a b r k c vi vj;
      A.((res.(SZ.add (SZ.mul vi c) vj) <- x));
      j := SZ.add vj 1sz;
    };
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  assert (pure (Seq.length v == SZ.v r * SZ.v c /\
                (forall (ii: nat) (jj: nat). ii < SZ.v r /\ jj < SZ.v c ==>
                   Seq.index v (ii * SZ.v c + jj) ==
                     M.dot (SZ.v r) (SZ.v k) (SZ.v c) va vb ii jj)));
  mul_eq (SZ.v r) (SZ.v k) (SZ.v c) va vb v;
  assert (pure (v == M.mul (SZ.v r) (SZ.v k) (SZ.v c) va vb));
}

(** [res <- a * bt^T], with [bt] stored as [c] rows of [k]. *)
fn mul_t (res: A.array S16.t) (a: A.array S16.t) (bt: A.array S16.t)
         (r: SZ.t) (k: SZ.t) (c: SZ.t { 0 < SZ.v c })
         (#pa: perm) (#pb: perm) (#vres: erased (Seq.seq S16.t))
         (#va: erased (M.matrix (SZ.v r) (SZ.v k))) (#vb: erased (M.matrix (SZ.v c) (SZ.v k)))
requires A.pts_to res vres ** A.pts_to a #pa va ** A.pts_to bt #pb vb **
         pure (Seq.length vres == SZ.v r * SZ.v c /\
               SZ.fits (SZ.v r * SZ.v k) /\ SZ.fits (SZ.v c * SZ.v k) /\
               SZ.fits (SZ.v r * SZ.v c))
ensures exists* v. A.pts_to res v ** A.pts_to a #pa va ** A.pts_to bt #pb vb **
        pure (v == M.mul_t (SZ.v r) (SZ.v k) (SZ.v c) va vb)
{
  A.pts_to_len res;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi r)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to bt #pb vb **
    pure (SZ.v vi <= SZ.v r /\ Seq.length v == SZ.v r * SZ.v c /\
          (forall (ii: nat) (jj: nat). ii < SZ.v vi /\ jj < SZ.v c ==>
             Seq.index v (ii * SZ.v c + jj) ==
               M.dot_t (SZ.v r) (SZ.v k) (SZ.v c) va vb ii jj))
  decreases (SZ.v r - SZ.v (!i))
  {
    let vi = !i;
    let mut j = 0sz;
    while (let vj = !j; SZ.lt vj c)
    invariant exists* (vj: SZ.t) (v: Seq.seq S16.t).
      pts_to i vi ** pts_to j vj ** A.pts_to res v ** A.pts_to a #pa va ** A.pts_to bt #pb vb **
      pure (SZ.v vi < SZ.v r /\ SZ.v vj <= SZ.v c /\ Seq.length v == SZ.v r * SZ.v c /\
            (forall (ii: nat) (jj: nat). ii < SZ.v vi /\ jj < SZ.v c ==>
               Seq.index v (ii * SZ.v c + jj) ==
                 M.dot_t (SZ.v r) (SZ.v k) (SZ.v c) va vb ii jj) /\
            (forall (jj: nat). jj < SZ.v vj ==>
               Seq.index v (SZ.v vi * SZ.v c + jj) ==
                 M.dot_t (SZ.v r) (SZ.v k) (SZ.v c) va vb (SZ.v vi) jj))
    decreases (SZ.v c - SZ.v (!j))
    {
      let vj = !j;
      let x = dot_t a bt r k c vi vj;
      A.((res.(SZ.add (SZ.mul vi c) vj) <- x));
      j := SZ.add vj 1sz;
    };
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to res v);
  assert (pure (Seq.length v == SZ.v r * SZ.v c /\
                (forall (ii: nat) (jj: nat). ii < SZ.v r /\ jj < SZ.v c ==>
                   Seq.index v (ii * SZ.v c + jj) ==
                     M.dot_t (SZ.v r) (SZ.v k) (SZ.v c) va vb ii jj)));
  mul_t_eq (SZ.v r) (SZ.v k) (SZ.v c) va vb v;
  assert (pure (v == M.mul_t (SZ.v r) (SZ.v k) (SZ.v c) va vb));
}

#pop-options
