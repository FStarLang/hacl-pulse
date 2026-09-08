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

(** Copying bytes between slices.

    Three loops that every algorithm here ends up needing: copy a prefix, copy
    at an offset, and copy as much of a digest as still fits in an output
    buffer.  All three are stated pointwise, because that is the shape their
    callers' loop invariants are in. *)
module Hacl.Impl.Copy

#lang-pulse

open Pulse.Lib.Pervasives

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8

inline_for_extraction
let szmin (a b: SZ.t) : r: SZ.t { SZ.v r == (if SZ.v a <= SZ.v b then SZ.v a else SZ.v b) } =
  if SZ.lte a b then a else b

#push-options "--z3rlimit 200 --fuel 1 --ifuel 1"

(** [dst[0 .. n) <- src[0 .. n)]. *)
fn copy_prefix (dst: S.slice S8.t) (src: S.slice S8.t) (n: SZ.t)
               (#vd: erased (Seq.seq S8.t)) (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires S.pts_to dst vd ** S.pts_to src #ps vs **
         pure (SZ.v n <= Seq.length vd /\ SZ.v n <= Seq.length vs)
ensures exists* vd'. S.pts_to dst vd' ** S.pts_to src #ps vs **
        pure (Seq.length vd' == Seq.length vd /\
              SZ.v n <= Seq.length vd' /\ SZ.v n <= Seq.length vs /\
              (forall (k: nat). k < SZ.v n ==> Seq.index vd' k == Seq.index vs k) /\
              (forall (k: nat). SZ.v n <= k /\ k < Seq.length vd ==>
                 Seq.index vd' k == Seq.index vd k))
{
  S.pts_to_len dst;
  S.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vd': Seq.seq S8.t).
    pts_to i vi ** S.pts_to dst vd' ** S.pts_to src #ps vs **
    pure (SZ.v vi <= SZ.v n /\ Seq.length vd' == Seq.length vd /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index vd' k == Seq.index vs k) /\
          (forall (k: nat). SZ.v vi <= k /\ k < Seq.length vd ==>
             Seq.index vd' k == Seq.index vd k))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    let x = S.(src.(vi));
    S.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
}

(** [dst[base .. base+n) <- src[0 .. n)]. *)
fn copy_at (dst: S.slice S8.t) (base: SZ.t) (src: S.slice S8.t) (n: SZ.t)
           (#vd: erased (Seq.seq S8.t)) (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires S.pts_to dst vd ** S.pts_to src #ps vs **
         pure (SZ.v base + SZ.v n <= Seq.length vd /\ SZ.v n <= Seq.length vs)
ensures exists* vd'. S.pts_to dst vd' ** S.pts_to src #ps vs **
        pure (Seq.length vd' == Seq.length vd /\
              SZ.v base + SZ.v n <= Seq.length vd' /\ SZ.v n <= Seq.length vs /\
              (forall (k: nat). k < SZ.v n ==>
                 Seq.index vd' (SZ.v base + k) == Seq.index vs k) /\
              (forall (k: nat). k < Seq.length vd /\ (k < SZ.v base \/ SZ.v base + SZ.v n <= k) ==>
                 Seq.index vd' k == Seq.index vd k))
{
  S.pts_to_len dst;
  S.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vd': Seq.seq S8.t).
    pts_to i vi ** S.pts_to dst vd' ** S.pts_to src #ps vs **
    pure (SZ.v vi <= SZ.v n /\ Seq.length vd' == Seq.length vd /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index vd' (SZ.v base + k) == Seq.index vs k) /\
          (forall (k: nat). k < Seq.length vd /\ (k < SZ.v base \/ SZ.v base + SZ.v vi <= k) ==>
             Seq.index vd' k == Seq.index vd k))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    SZ.fits_lte (SZ.v base + SZ.v vi) (Seq.length vd);
    let x = S.(src.(vi));
    S.((dst.(SZ.add base vi) <- x));
    i := SZ.add vi 1sz;
  };
}

(** Write as much of the digest [dg] into [out] at offset [base] as fits. *)
fn write_chunk (out: S.slice S8.t) (base: SZ.t) (dg: S.slice S8.t)
               (#vout: erased (Seq.seq S8.t)) (#pd: perm) (#vdg: erased (Seq.seq S8.t))
requires S.pts_to out vout ** S.pts_to dg #pd vdg **
         pure (SZ.v base <= Seq.length vout)
ensures exists* vout'. S.pts_to out vout' ** S.pts_to dg #pd vdg **
        pure (Seq.length vout' == Seq.length vout /\
              SZ.v base <= Seq.length vout' /\
              (forall (k: nat). k < SZ.v base ==> Seq.index vout' k == Seq.index vout k) /\
              (forall (k: nat). k < Seq.length vdg /\ SZ.v base + k < Seq.length vout ==>
                 Seq.index vout' (SZ.v base + k) == Seq.index vdg k))
{
  S.pts_to_len out;
  S.pts_to_len dg;
  let ol = S.len out;
  let dl = S.len dg;
  let cnt = szmin dl (SZ.sub ol base);
  copy_at out base dg cnt;
}

(** [dst[dbase .. dbase+n) <- src[sbase .. sbase+n)]. *)
fn copy_range (dst: S.slice S8.t) (dbase: SZ.t) (src: S.slice S8.t) (sbase: SZ.t) (n: SZ.t)
              (#vd: erased (Seq.seq S8.t)) (#ps: perm) (#vs: erased (Seq.seq S8.t))
requires S.pts_to dst vd ** S.pts_to src #ps vs **
         pure (SZ.v dbase + SZ.v n <= Seq.length vd /\ SZ.v sbase + SZ.v n <= Seq.length vs)
ensures exists* vd'. S.pts_to dst vd' ** S.pts_to src #ps vs **
        pure (Seq.length vd' == Seq.length vd /\
              SZ.v dbase + SZ.v n <= Seq.length vd' /\ SZ.v sbase + SZ.v n <= Seq.length vs /\
              (forall (k: nat). k < SZ.v n ==>
                 Seq.index vd' (SZ.v dbase + k) == Seq.index vs (SZ.v sbase + k)) /\
              (forall (k: nat). k < Seq.length vd /\ (k < SZ.v dbase \/ SZ.v dbase + SZ.v n <= k) ==>
                 Seq.index vd' k == Seq.index vd k))
{
  S.pts_to_len dst;
  S.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi n)
  invariant exists* (vi: SZ.t) (vd': Seq.seq S8.t).
    pts_to i vi ** S.pts_to dst vd' ** S.pts_to src #ps vs **
    pure (SZ.v vi <= SZ.v n /\ Seq.length vd' == Seq.length vd /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index vd' (SZ.v dbase + k) == Seq.index vs (SZ.v sbase + k)) /\
          (forall (k: nat). k < Seq.length vd /\ (k < SZ.v dbase \/ SZ.v dbase + SZ.v vi <= k) ==>
             Seq.index vd' k == Seq.index vd k))
  decreases (SZ.v n - SZ.v (!i))
  {
    let vi = !i;
    SZ.fits_lte (SZ.v dbase + SZ.v vi) (Seq.length vd);
    SZ.fits_lte (SZ.v sbase + SZ.v vi) (Seq.length vs);
    let x = S.(src.(SZ.add sbase vi));
    S.((dst.(SZ.add dbase vi) <- x));
    i := SZ.add vi 1sz;
  };
}

#pop-options
