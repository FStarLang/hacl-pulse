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

(** Sampling the error distribution.

    Sixteen bits of randomness become one sample: the low bit is the sign
    and the other fifteen are compared against a cumulative table.  The
    magnitude is how many table entries the value exceeds, which is counted
    with a mask rather than a branch -- the table is public but the value
    compared against it is not, and a data-dependent branch here would leak
    the secret matrix one entry at a time.

    The table itself is public data, so it is an array of ordinary
    [UInt16]s that the caller supplies and that the parameter record's
    erased copy describes. *)
module Hacl.Frodo.Sample

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Frodo.Params

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module M = Spec.Frodo.Matrix
module F = Spec.Frodo
module Loops = Hacl.Spec.Loops
module G = FStar.Ghost

(** The sampled matrix, at a flat index.  [Spec.Frodo.sample_matrix] reads
    its argument as a matrix and samples pointwise; in storage order that is
    just two bytes at a time. *)
let sample_matrix_eq (p: params) (r: nat) (c: pos)
                     (b: Seq.lseq S8.t (2 * (r * c))) (res: M.matrix r c)
  : Lemma (requires forall (t: nat). t < r * c ==>
                      Seq.index res t ==
                        F.sample p (S16.of_bytes_le (Seq.index b (2 * t))
                                                    (Seq.index b (2 * t + 1))))
          (ensures res == F.sample_matrix p r c b)
  = let aux (t: nat { t < r * c })
      : Lemma (Seq.index res t == Seq.index (F.sample_matrix p r c b) t)
      = M.div_lt t r c;
        M.get_flat r c (M.from_bytes r c b) t
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro res (F.sample_matrix p r c b)

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

(** One sample.  [cdf] is the parameter set's table, which the caller owns
    and which the erased field of [p] describes. *)
fn sample ([@@@FStar.Attributes.monomorphize] p: params)
          (cdf: A.array U16.t) (r: S16.t)
          (#pc: perm) (#vcdf: erased (Seq.lseq U16.t (cdf_len p)))
requires A.pts_to cdf #pc vcdf ** pure (reveal vcdf == reveal p.cdf)
returns x: S16.t
ensures A.pts_to cdf #pc vcdf ** pure (x == F.sample p r)
{
  A.pts_to_len cdf;
  let t = S16.shift_right r 1ul;
  S16.logand_mask_low r 1ul;
  let sign = S16.logand r (S16.mask_low 1ul);
  let last = SZ.sub p.ncdf 1sz;
  let mut acc = S16.zero;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi last)
  invariant exists* (vi: SZ.t) (vacc: S16.t).
    pts_to i vi ** pts_to acc vacc ** A.pts_to cdf #pc vcdf **
    pure (SZ.v vi <= cdf_len p - 1 /\
          S16.v vacc == Loops.repeati_g (SZ.v vi) (F.sample_step p (S16.v r / 2)) 0)
  decreases (cdf_len p - 1 - SZ.v (!i))
  {
    let vi = !i;
    let vacc = !acc;
    let ci = S16.classify A.(cdf.(vi));
    F.sample_e_bound p (S16.v r / 2) (SZ.v vi + 1);
    Loops.unfold_repeati_g (SZ.v vi) (F.sample_step p (S16.v r / 2)) 0;
    acc := S16.sub_mod vacc (S16.lt_mask ci t);
    i := SZ.add vi 1sz;
  };
  let e = !acc;
  F.sample_e_bound p (S16.v r / 2) (cdf_len p - 1);
  assert (pure (S16.v e == F.sample_e p (S16.v r / 2)));
  let neg = S16.sub_mod S16.zero e;
  let m = S16.eq_mask sign S16.one;
  S16.select m neg e
}

(** [m <- sample_matrix p r c (slice b base ...)].  The offset is there
    because the KEM draws two or three matrices from a single SHAKE output
    and there is no reason to copy each slice out first. *)
fn sample_matrix ([@@@FStar.Attributes.monomorphize] p: params)
                 (cdf: A.array U16.t) (m: A.array S16.t) (b: A.array S8.t)
                 (r: SZ.t) (c: SZ.t { 0 < SZ.v c }) (blen: SZ.t)
                 (base: SZ.t { SZ.v base + 2 * (SZ.v r * SZ.v c) <= SZ.v blen })
                 (#pc: perm) (#pb: perm)
                 (#vcdf: erased (Seq.lseq U16.t (cdf_len p)))
                 (#vm: erased (Seq.seq S16.t))
                 (#vb: erased (Seq.lseq S8.t (SZ.v blen)))
requires A.pts_to cdf #pc vcdf ** A.pts_to m vm ** A.pts_to b #pb vb **
         pure (reveal vcdf == reveal p.cdf /\
               Seq.length vm == SZ.v r * SZ.v c /\ SZ.v blen < pow2 32)
ensures exists* v. A.pts_to cdf #pc vcdf ** A.pts_to m v ** A.pts_to b #pb vb **
        pure (v == F.sample_matrix p (SZ.v r) (SZ.v c)
                     (Seq.slice vb (SZ.v base) (SZ.v base + 2 * (SZ.v r * SZ.v c))))
{
  A.pts_to_len m;
  A.pts_to_len b;
  Hacl.SizeT.fits32 ();
  SZ.fits_u32_implies_fits (SZ.v r * SZ.v c);
  SZ.fits_u32_implies_fits (2 * (SZ.v r * SZ.v c));
  let len = SZ.mul r c;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to cdf #pc vcdf ** A.pts_to m v ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v k ==
               F.sample p (S16.of_bytes_le (Seq.index vb (SZ.v base + 2 * k))
                                           (Seq.index vb (SZ.v base + 2 * k + 1)))))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let j = SZ.add base (SZ.mul 2sz vi);
    let lo = A.(b.(j));
    let hi = A.(b.(SZ.add j 1sz));
    let x = sample p cdf (S16.of_bytes_le lo hi);
    A.((m.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to m v);
  let sl = G.hide (Seq.slice (reveal vb) (SZ.v base) (SZ.v base + 2 * (SZ.v r * SZ.v c)));
  assert (pure (Seq.length v == SZ.v r * SZ.v c /\
                (forall (k: nat). k < SZ.v r * SZ.v c ==>
                   Seq.index v k ==
                     F.sample p (S16.of_bytes_le (Seq.index (reveal sl) (2 * k))
                                                 (Seq.index (reveal sl) (2 * k + 1))))));
  sample_matrix_eq p (SZ.v r) (SZ.v c) sl v;
  assert (pure (v == F.sample_matrix p (SZ.v r) (SZ.v c) sl));
}

#pop-options
