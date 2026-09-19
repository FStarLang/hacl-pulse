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


(** Constant-time comparison and selection over byte arrays.

    Both of the KEMs in this library end the same way: decapsulation
    re-encrypts, compares, and returns either the real shared secret or a
    rejection value.  Which of the two happened must not be observable, so
    the comparison produces a mask rather than a [bool] -- secret integers
    carry no decidable equality, which is the point of them -- and the
    selection is branch-free. *)
module Hacl.Impl.Select

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module UInt = FStar.UInt
module SEM = FStar.IndefiniteDescription

(** Prefix agreement, as a ghost boolean: the loop below cannot test
    equality of secrets, so its invariant is stated with this. *)
let agree (va vb: Seq.seq S8.t) (i: nat) : GTot bool =
  SEM.strong_excluded_middle
    (forall (k: nat). k < i /\ k < Seq.length va /\ k < Seq.length vb ==>
       Seq.index va k == Seq.index vb k)

(** At full length, agreement is equality. *)
let eq_from_agree (va vb: Seq.seq S8.t)
  : Lemma (requires Seq.length va == Seq.length vb)
          (ensures (agree va vb (Seq.length va) <==> va == vb))
  = if agree va vb (Seq.length va) then Seq.lemma_eq_intro va vb

(** All ones if the two arrays are equal, all zeroes otherwise. *)
fn eq_mask_bytes (a: A.array S8.t) (b: A.array S8.t) (len: SZ.t)
                 (#pa: perm) (#pb: perm)
                 (#va: erased (Seq.seq S8.t)) (#vb: erased (Seq.seq S8.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len)
returns m: S8.t
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure ((S8.v m == 0 \/ S8.v m == pow2 8 - 1) /\
              (S8.v m == pow2 8 - 1 <==> reveal va == reveal vb))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut acc = S8.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (vacc: S8.t).
    pts_to i vi ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v len /\
          S8.v vacc == (if agree va vb (SZ.v vi) then pow2 8 - 1 else 0))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let vacc = !acc;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let m = S8.eq_mask x y;
    UInt.logand_lemma_1 #8 (S8.v vacc);
    UInt.logand_lemma_2 #8 (S8.v vacc);
    UInt.logand_commutative #8 (S8.v vacc) (S8.v m);
    UInt.logand_lemma_1 #8 (S8.v m);
    UInt.logand_lemma_2 #8 (S8.v m);
    acc := S8.logand vacc m;
    i := SZ.add vi 1sz;
  };
  let r = !acc;
  eq_from_agree va vb;
  r
}

(** [dst[dbase + k] <- select mask x[k] y[k]], for a mask that is all ones
    or all zeroes.  This is the implicit rejection. *)
fn select_copy (dst: A.array S8.t) (dbase: SZ.t) (x: A.array S8.t) (y: A.array S8.t)
               (len: SZ.t) (mask: S8.t { S8.v mask == 0 \/ S8.v mask == pow2 8 - 1 })
               (#px: perm) (#py: perm) (#vd: erased (Seq.seq S8.t))
               (#vx: erased (Seq.seq S8.t)) (#vy: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to x #px vx ** A.pts_to y #py vy **
         pure (SZ.v dbase + SZ.v len <= Seq.length vd /\
               Seq.length vx == SZ.v len /\ Seq.length vy == SZ.v len)
ensures exists* v. A.pts_to dst v ** A.pts_to x #px vx ** A.pts_to y #py vy **
        pure (Seq.length v == Seq.length vd /\
              SZ.v dbase + SZ.v len <= Seq.length v /\
              Seq.length vx == SZ.v len /\ Seq.length vy == SZ.v len /\
              (forall (k: nat). k < SZ.v len ==>
                 Seq.index v (SZ.v dbase + k) ==
                   (if S8.v mask = 0 then Seq.index vy k else Seq.index vx k)) /\
              (forall (k: nat). k < Seq.length vd /\
                               (k < SZ.v dbase \/ SZ.v dbase + SZ.v len <= k) ==>
                 Seq.index v k == Seq.index vd k))
{
  A.pts_to_len dst;
  A.pts_to_len x;
  A.pts_to_len y;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to dst v ** A.pts_to x #px vx ** A.pts_to y #py vy **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == Seq.length vd /\
          SZ.v dbase + SZ.v len <= Seq.length v /\
          Seq.length vx == SZ.v len /\ Seq.length vy == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v (SZ.v dbase + k) ==
               (if S8.v mask = 0 then Seq.index vy k else Seq.index vx k)) /\
          (forall (k: nat). k < Seq.length vd /\
                           (k < SZ.v dbase \/ SZ.v dbase + SZ.v vi <= k) ==>
             Seq.index v k == Seq.index vd k))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(x.(vi));
    let b = A.(y.(vi));
    A.((dst.(SZ.add dbase vi) <- S8.select mask a b));
    i := SZ.add vi 1sz;
  };
}
