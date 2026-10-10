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

(** A, and the two products that are taken against it.

    A is [n] by [n] -- one and three quarter megabytes at the largest
    parameter set -- and it is used exactly twice, each time against a
    matrix that is only eight wide.  There is no reason to have it in
    memory.  Both products here expand one row of A at a time, use it, and
    throw it away: the working set is a single row, twenty-one kilobytes at
    Frodo-1344 instead of three and a half megabytes, and the arithmetic is
    the same O(n^2 * 8) either way.

    The two products have different shapes and so stream differently.

    - [mul_t_as] computes A S^T, whose entry [(i, j)] needs only row [i] of
      A.  The rows come out in order and each is consumed immediately.

    - [mul_sa] computes S' A, whose entry [(i, j)] needs {i column} [j] of
      A.  Row [k] of A instead contributes one term to every entry of the
      result, so the loop is a rank-one update: having drawn row [k], add
      [S'(i,k) * A(k,j)] to [acc(i,j)] for all [i] and [j].  That is the
      same accumulation order the specification's [repeati] uses.

    A is always expanded with SHAKE-128, in every parameter set, including
    the two that use SHAKE-256 for everything else. *)
module Hacl.Frodo.Gen

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
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module G = FStar.Ghost

let fits_small (x: nat) : Lemma (requires x < pow2 32) (ensures SZ.fits x) =
  Hacl.SizeT.fits32 (); SZ.fits_u32_implies_fits x

(** A product built by filling in entry [(i, j)] at flat position
    [i * c + j] is the product the specification builds pointwise.  Both
    loops below finish with one of these. *)
let mul_eq (r: nat) (k: nat) (c: pos) (a: M.matrix r k) (b: M.matrix k c)
           (res: M.matrix r c)
  : Lemma (requires forall (i: nat) (j: nat). i < r /\ j < c ==>
                      M.get r c res i j == M.dot r k c a b i j)
          (ensures res == M.mul r k c a b)
  = let aux (t: nat { t < r * c }) : Lemma (Seq.index res t == Seq.index (M.mul r k c a b) t) =
      M.div_lt t r c;
      M.get_flat r c res t;
      M.get_flat r c (M.mul r k c a b) t
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro res (M.mul r k c a b)

let mul_t_eq (r: nat) (k: nat) (c: pos) (a: M.matrix r k) (bt: M.matrix c k)
             (res: M.matrix r c)
  : Lemma (requires forall (i: nat) (j: nat). i < r /\ j < c ==>
                      Seq.index res (i * c + j) == M.dot_t r k c a bt i j)
          (ensures res == M.mul_t r k c a bt)
  = let aux (t: nat { t < r * c })
      : Lemma (Seq.index res t == Seq.index (M.mul_t r k c a bt) t) =
      M.div_lt t r c;
      M.index_bound r c (t / c) (t % c);
      Math.euclidean_division_definition t c
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro res (M.mul_t r k c a bt)

(** Updating entry [(i, j)] leaves every other entry alone, for all
    indices at once: the rank-one update below rewrites the whole result
    matrix, and [i * c + j] is nonlinear in [c] when [c] is the parameter
    set's [n], so the bound has to come from a lemma rather than from
    arithmetic. *)
let upd_other (r: nat) (c: pos) (m: M.matrix r c)
              (i: nat { i < r }) (j: nat { j < c }) (x: S16.t)
  : Lemma (forall (i': nat) (j': nat). i' < r /\ j' < c ==>
             M.get r c (M.upd r c m i j x) i' j' ==
               (if i' = i && j' = j then x else M.get r c m i' j'))
  = FStar.Classical.forall_intro_2
      (fun (i': nat { i' < r }) (j': nat { j' < c }) -> M.get_upd r c m i j x i' j'
         <: Lemma (M.get r c (M.upd r c m i j x) i' j' ==
                     (if i' = i && j' = j then x else M.get r c m i' j')))

(** One more row of the product settled: the rows below [i] and row [i]
    itself together cover everything below [i + 1].  Hoisted out of the loop
    in {!mul_sa}, where the case split is not found in practice. *)
let rows_extend (r: nat) (c: pos) (m: M.matrix r c) (i: nat { i < r })
                (f: nat -> nat -> GTot S16.t)
  : Lemma (requires (forall (i': nat) (j': nat). i' < i /\ j' < c ==>
                       M.get r c m i' j' == f i' j') /\
                    (forall (j': nat). j' < c ==> M.get r c m i j' == f i j'))
          (ensures (forall (i': nat) (j': nat). i' < i + 1 /\ j' < c ==>
                      M.get r c m i' j' == f i' j'))
  = ()

(** The same, at the flat positions {!mul_t_as} writes to. *)
let rows_extend_t (r: nat) (m: Seq.lseq S16.t (r * nbar)) (i: nat { i < r })
                  (f: nat -> nat -> GTot S16.t)
  : Lemma (requires (forall (i': nat) (j': nat). i' < i /\ j' < nbar ==>
                       Seq.index m (i' * nbar + j') == f i' j') /\
                    (forall (j': nat). j' < nbar ==> Seq.index m (i * nbar + j') == f i j'))
          (ensures (forall (i': nat) (j': nat). i' < i + 1 /\ j' < nbar ==>
                      Seq.index m (i' * nbar + j') == f i' j'))
  = ()

(** The eighteen bytes A's expansion is applied to: the row index, little
    endian, then the seed. *)
let msg_eq (i: nat { i < pow2 16 }) (seed: Seq.lseq S8.t 16) (m: Seq.lseq S8.t 18)
  : Lemma (requires (let x = S16.classify (U16.uint_to_t i) in
                     Seq.index m 0 == S16.lo x /\ Seq.index m 1 == S16.hi x /\
                     (forall (k: nat). k < 16 ==> Seq.index m (2 + k) == Seq.index seed k)))
          (ensures m == Seq.append (F.index_bytes i) seed)
  = Seq.lemma_eq_intro m (Seq.append (F.index_bytes i) seed)

#push-options "--z3rlimit 800 --fuel 1 --ifuel 0"

(** Row [i] of A, as [n] entries rather than as [2n] bytes.  [msg] and
    [row] are scratch the caller owns; keeping them out of here means the
    loops below allocate once instead of once per row. *)
fn gen_row ([@@@FStar.Attributes.monomorphize] p: params)
           (seed: A.array S8.t) (i: SZ.t { SZ.v i < n p })
           (msg: A.array S8.t) (row: A.array S8.t) (out: A.array S16.t)
           (#ps: perm) (#vseed: erased (Seq.lseq S8.t 16))
           (#vmsg0: erased (Seq.seq S8.t)) (#vrow0: erased (Seq.seq S8.t))
           (#vout0: erased (Seq.seq S16.t))
requires A.pts_to seed #ps vseed ** A.pts_to msg vmsg0 **
         A.pts_to row vrow0 ** A.pts_to out vout0 **
         pure (Seq.length vmsg0 == 18 /\ Seq.length vrow0 == 2 * n p /\
               Seq.length vout0 == n p)
ensures exists* vmsg vrow vout.
        A.pts_to seed #ps vseed ** A.pts_to msg vmsg **
        A.pts_to row vrow ** A.pts_to out vout **
        pure (Seq.length vmsg == 18 /\ Seq.length vrow == 2 * n p /\
              Seq.length vout == n p /\
              (forall (l: nat). l < n p ==>
                 Seq.index vout l ==
                   M.get (n p) (n p) (F.gen_matrix p vseed) (SZ.v i) l))
{
  A.pts_to_len seed;
  A.pts_to_len msg;
  A.pts_to_len row;
  A.pts_to_len out;
  assert_norm (1344 < pow2 16);
  let x = S16.classify (FStar.Int.Cast.uint32_to_uint16 (SZ.sizet_to_uint32 i));
  A.((msg.(0sz) <- S16.lo x));
  A.((msg.(1sz) <- S16.hi x));
  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk 16sz)
  invariant exists* (vk: SZ.t) (vmsg: Seq.seq S8.t).
    pts_to k vk ** A.pts_to seed #ps vseed ** A.pts_to msg vmsg **
    A.pts_to row vrow0 ** A.pts_to out vout0 **
    pure (SZ.v vk <= 16 /\ Seq.length vmsg == 18 /\
          Seq.index vmsg 0 == S16.lo x /\ Seq.index vmsg 1 == S16.hi x /\
          (forall (l: nat). l < SZ.v vk ==>
             Seq.index vmsg (2 + l) == Seq.index vseed l))
  decreases (16 - SZ.v (!k))
  {
    let vk = !k;
    let b = A.(seed.(vk));
    A.((msg.(SZ.add 2sz vk) <- b));
    k := SZ.add vk 1sz;
  };
  with vmsg. assert (A.pts_to msg vmsg);
  msg_eq (SZ.v i) vseed vmsg;
  fits_small (2 * n p);
  let two_n = SZ.mul 2sz p.nn;
  Hacl.Hash.SHA3.shake128 row two_n msg 18sz;
  with vrow. assert (A.pts_to row vrow);
  let mut l = 0sz;
  while (let vl = !l; SZ.lt vl p.nn)
  invariant exists* (vl: SZ.t) (vout: Seq.seq S16.t).
    pts_to l vl ** A.pts_to seed #ps vseed ** A.pts_to msg vmsg **
    A.pts_to row vrow ** A.pts_to out vout **
    pure (SZ.v vl <= n p /\ Seq.length vout == n p /\
          (forall (t: nat). t < SZ.v vl ==>
             Seq.index vout t ==
               S16.of_bytes_le (Seq.index vrow (2 * t)) (Seq.index vrow (2 * t + 1))))
  decreases (n p - SZ.v (!l))
  {
    let vl = !l;
    let j = SZ.mul 2sz vl;
    let lo = A.(row.(j));
    let hi = A.(row.(SZ.add j 1sz));
    A.((out.(vl) <- S16.of_bytes_le lo hi));
    l := SZ.add vl 1sz;
  };
  assert (pure (vrow == F.gen_row p vseed (SZ.v i)));
}

(** [b <- A S^T], with A given by its seed and S stored transposed.  The
    result is [n] by [nbar]. *)
fn mul_t_as ([@@@FStar.Attributes.monomorphize] p: params)
            (seed: A.array S8.t) (st: A.array S16.t) (b: A.array S16.t)
            (#ps: perm) (#pt: perm)
            (#vseed: erased (Seq.lseq S8.t 16))
            (#vst: erased (Seq.lseq S16.t (nbar * n p)))
            (#vb0: erased (Seq.lseq S16.t (n p * nbar)))
requires A.pts_to seed #ps vseed ** A.pts_to st #pt vst ** A.pts_to b vb0
ensures exists* vb.
        A.pts_to seed #ps vseed ** A.pts_to st #pt vst ** A.pts_to b vb **
        pure (vb == M.mul_t (n p) (n p) nbar (F.gen_matrix p vseed) vst)
{
  A.pts_to_len seed;
  A.pts_to_len st;
  A.pts_to_len b;
  fits_small (2 * n p);
  let two_n = SZ.mul 2sz p.nn;
  let mut msg = [| (S8.zero <: S8.t); 18sz |];
  let mut rowb = [| (S8.zero <: S8.t); two_n |];
  let mut rowa = [| (S16.zero <: S16.t); p.nn |];
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi p.nn)
  invariant exists* (vi: SZ.t) (vmsg: Seq.seq S8.t) (vrowb: Seq.seq S8.t)
                    (vrowa: Seq.seq S16.t) (vb: Seq.seq S16.t).
    pts_to i vi ** A.pts_to seed #ps vseed ** A.pts_to st #pt vst **
    A.pts_to b vb ** A.pts_to msg vmsg ** A.pts_to rowb vrowb ** A.pts_to rowa vrowa **
    pure (SZ.v vi <= n p /\ Seq.length vmsg == 18 /\ Seq.length vrowb == 2 * n p /\
          Seq.length vrowa == n p /\ Seq.length vb == n p * nbar /\
          (forall (i': nat) (j': nat). i' < SZ.v vi /\ j' < nbar ==>
             Seq.index vb (i' * nbar + j') ==
               M.dot_t (n p) (n p) nbar (F.gen_matrix p vseed) vst i' j'))
  decreases (n p - SZ.v (!i))
  {
    let vi = !i;
    gen_row p seed vi msg rowb rowa;
    with vm1 vr1 vrowa.
      assert (A.pts_to msg vm1 ** A.pts_to rowb vr1 ** A.pts_to rowa vrowa);
    let mut j = 0sz;
    while (let vj = !j; SZ.lt vj 8sz)
    invariant exists* (vj: SZ.t) (vmsg: Seq.seq S8.t) (vrowb: Seq.seq S8.t)
                      (vb: Seq.seq S16.t).
      pts_to i vi ** pts_to j vj ** A.pts_to seed #ps vseed ** A.pts_to st #pt vst **
      A.pts_to b vb ** A.pts_to msg vmsg ** A.pts_to rowb vrowb ** A.pts_to rowa vrowa **
      pure (SZ.v vj <= nbar /\ Seq.length vmsg == 18 /\ Seq.length vrowb == 2 * n p /\
            Seq.length vb == n p * nbar /\
            (forall (i': nat) (j': nat). i' < SZ.v vi /\ j' < nbar ==>
               Seq.index vb (i' * nbar + j') ==
                 M.dot_t (n p) (n p) nbar (F.gen_matrix p vseed) vst i' j') /\
            (forall (j': nat). j' < SZ.v vj ==>
               Seq.index vb (SZ.v vi * nbar + j') ==
                 M.dot_t (n p) (n p) nbar (F.gen_matrix p vseed) vst (SZ.v vi) j'))
    decreases (nbar - SZ.v (!j))
    {
      let vj = !j;
      let mut acc = S16.zero;
      let mut l = 0sz;
      while (let vl = !l; SZ.lt vl p.nn)
      invariant exists* (vl: SZ.t) (vacc: S16.t).
        pts_to i vi ** pts_to j vj ** pts_to l vl ** pts_to acc vacc **
        A.pts_to seed #ps vseed ** A.pts_to st #pt vst ** A.pts_to rowa vrowa **
        pure (SZ.v vl <= n p /\
              vacc == Loops.repeati (SZ.v vl)
                        (M.dot_t_step (n p) (n p) nbar (F.gen_matrix p vseed) vst (SZ.v vi) (SZ.v vj))
                        S16.zero)
      decreases (n p - SZ.v (!l))
      {
        let vl = !l;
        let vacc = !acc;
        Loops.unfold_repeati (SZ.v vl)
          (M.dot_t_step (n p) (n p) nbar (F.gen_matrix p vseed) vst (SZ.v vi) (SZ.v vj)) S16.zero;
        M.index_bound nbar (n p) (SZ.v vj) (SZ.v vl);
        let s = A.(st.(SZ.add (SZ.mul vj p.nn) vl));
        let r = A.(rowa.(vl));
        acc := S16.add_mod vacc (S16.mul_mod r s);
        l := SZ.add vl 1sz;
      };
      let res = !acc;
      M.index_bound (n p) nbar (SZ.v vi) (SZ.v vj);
      A.((b.(SZ.add (SZ.mul vi 8sz) vj) <- res));
      j := SZ.add vj 1sz;
    };
    with vbf. assert (A.pts_to b vbf);
    rows_extend_t (n p) vbf (SZ.v vi)
      (fun i' j' -> M.dot_t (n p) (n p) nbar (F.gen_matrix p vseed) vst i' j');
    i := SZ.add vi 1sz;
  };
  with vb. assert (A.pts_to b vb);
  assert (pure (forall (i': nat) (j': nat). i' < n p /\ j' < nbar ==>
                  Seq.index vb (i' * nbar + j') ==
                    M.dot_t (n p) (n p) nbar (F.gen_matrix p vseed) vst i' j'));
  mul_t_eq (n p) (n p) nbar (F.gen_matrix p vseed) vst vb;
  assert (pure (vb == M.mul_t (n p) (n p) nbar (F.gen_matrix p vseed) vst));
}

(** [b <- S' A].  The result is [nbar] by [n], and every row of A touches
    every entry of it, so A is streamed on the outside and the result is
    updated in place. *)
fn mul_sa ([@@@FStar.Attributes.monomorphize] p: params)
          (seed: A.array S8.t) (sp: A.array S16.t) (b: A.array S16.t)
          (#ps: perm) (#pt: perm)
          (#vseed: erased (Seq.lseq S8.t 16))
          (#vsp: erased (Seq.lseq S16.t (nbar * n p)))
          (#vb0: erased (Seq.lseq S16.t (nbar * n p)))
requires A.pts_to seed #ps vseed ** A.pts_to sp #pt vsp ** A.pts_to b vb0
ensures exists* vb.
        A.pts_to seed #ps vseed ** A.pts_to sp #pt vsp ** A.pts_to b vb **
        pure (vb == M.mul nbar (n p) (n p) vsp (F.gen_matrix p vseed))
{
  A.pts_to_len seed;
  A.pts_to_len sp;
  A.pts_to_len b;
  fits_small (2 * n p);
  fits_small (nbar * n p);
  let two_n = SZ.mul 2sz p.nn;
  let bsize = SZ.mul 8sz p.nn;
  let mut msg = [| (S8.zero <: S8.t); 18sz |];
  let mut rowb = [| (S8.zero <: S8.t); two_n |];
  let mut rowa = [| (S16.zero <: S16.t); p.nn |];

  let mut z = 0sz;
  while (let vz = !z; SZ.lt vz bsize)
  invariant exists* (vz: SZ.t) (vb: Seq.lseq S16.t (nbar * n p)) (vmsg: Seq.seq S8.t)
                    (vrowb: Seq.seq S8.t) (vrowa: Seq.seq S16.t).
    pts_to z vz ** A.pts_to seed #ps vseed ** A.pts_to sp #pt vsp ** A.pts_to b vb **
    A.pts_to msg vmsg ** A.pts_to rowb vrowb ** A.pts_to rowa vrowa **
    pure (SZ.v vz <= nbar * n p /\           Seq.length vmsg == 18 /\ Seq.length vrowb == 2 * n p /\
          Seq.length vrowa == n p /\
          (forall (t: nat). t < SZ.v vz ==> Seq.index vb t == S16.zero))
  decreases (nbar * n p - SZ.v (!z))
  {
    let vz = !z;
    A.((b.(vz) <- S16.zero));
    z := SZ.add vz 1sz;
  };

  let mut k = 0sz;
  while (let vk = !k; SZ.lt vk p.nn)
  invariant exists* (vk: SZ.t) (vmsg: Seq.seq S8.t) (vrowb: Seq.seq S8.t)
                    (vrowa: Seq.seq S16.t) (vb: Seq.lseq S16.t (nbar * n p)).
    pts_to k vk ** A.pts_to seed #ps vseed ** A.pts_to sp #pt vsp **
    A.pts_to b vb ** A.pts_to msg vmsg ** A.pts_to rowb vrowb ** A.pts_to rowa vrowa **
    pure (SZ.v vk <= n p /\ Seq.length vmsg == 18 /\ Seq.length vrowb == 2 * n p /\
          Seq.length vrowa == n p /\           (forall (i': nat) (j': nat). i' < nbar /\ j' < n p ==>
             M.get nbar (n p) vb i' j' ==
               Loops.repeati (SZ.v vk)
                 (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) i' j') S16.zero))
  decreases (n p - SZ.v (!k))
  {
    let vk = !k;
    gen_row p seed vk msg rowb rowa;
    with vm1 vr1 vrowa.
      assert (A.pts_to msg vm1 ** A.pts_to rowb vr1 ** A.pts_to rowa vrowa);
    let mut i = 0sz;
    while (let vi = !i; SZ.lt vi 8sz)
    invariant exists* (vi: SZ.t) (vmsg: Seq.seq S8.t) (vrowb: Seq.seq S8.t)
                      (vb: Seq.lseq S16.t (nbar * n p)).
      pts_to k vk ** pts_to i vi ** A.pts_to seed #ps vseed ** A.pts_to sp #pt vsp **
      A.pts_to b vb ** A.pts_to msg vmsg ** A.pts_to rowb vrowb ** A.pts_to rowa vrowa **
      pure (SZ.v vi <= nbar /\ Seq.length vmsg == 18 /\ Seq.length vrowb == 2 * n p /\
                        (forall (i': nat) (j': nat). SZ.v vi <= i' /\ i' < nbar /\ j' < n p ==>
               M.get nbar (n p) vb i' j' ==
                 Loops.repeati (SZ.v vk)
                   (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) i' j') S16.zero) /\
            (forall (i': nat) (j': nat). i' < SZ.v vi /\ j' < n p ==>
               M.get nbar (n p) vb i' j' ==
                 Loops.repeati (SZ.v vk + 1)
                   (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) i' j') S16.zero))
    decreases (nbar - SZ.v (!i))
    {
      let vi = !i;
      M.index_bound nbar (n p) (SZ.v vi) (SZ.v vk);
      let s = A.(sp.(SZ.add (SZ.mul vi p.nn) vk));
      let base = SZ.mul vi p.nn;
      let mut j = 0sz;
      while (let vj = !j; SZ.lt vj p.nn)
      invariant exists* (vj: SZ.t) (vmsg: Seq.seq S8.t) (vrowb: Seq.seq S8.t)
                        (vb: Seq.lseq S16.t (nbar * n p)).
        pts_to k vk ** pts_to i vi ** pts_to j vj **
        A.pts_to seed #ps vseed ** A.pts_to sp #pt vsp **
        A.pts_to b vb ** A.pts_to msg vmsg ** A.pts_to rowb vrowb ** A.pts_to rowa vrowa **
        pure (SZ.v vj <= n p /\ Seq.length vmsg == 18 /\ Seq.length vrowb == 2 * n p /\
                            (forall (i': nat) (j': nat). SZ.v vi < i' /\ i' < nbar /\ j' < n p ==>
                 M.get nbar (n p) vb i' j' ==
                   Loops.repeati (SZ.v vk)
                     (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) i' j') S16.zero) /\
              (forall (i': nat) (j': nat). i' < SZ.v vi /\ j' < n p ==>
                 M.get nbar (n p) vb i' j' ==
                   Loops.repeati (SZ.v vk + 1)
                     (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) i' j') S16.zero) /\
              (forall (j': nat). SZ.v vj <= j' /\ j' < n p ==>
                 M.get nbar (n p) vb (SZ.v vi) j' ==
                   Loops.repeati (SZ.v vk)
                     (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) (SZ.v vi) j') S16.zero) /\
              (forall (j': nat). j' < SZ.v vj ==>
                 M.get nbar (n p) vb (SZ.v vi) j' ==
                   Loops.repeati (SZ.v vk + 1)
                     (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) (SZ.v vi) j') S16.zero))
      decreases (n p - SZ.v (!j))
      {
        let vj = !j;
        with vb. assert (A.pts_to b vb);
        Loops.unfold_repeati (SZ.v vk)
          (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) (SZ.v vi) (SZ.v vj)) S16.zero;
        M.index_bound nbar (n p) (SZ.v vi) (SZ.v vj);
        let old = A.(b.(SZ.add base vj));
        let r = A.(rowa.(vj));
        upd_other nbar (n p) vb (SZ.v vi) (SZ.v vj) (S16.add_mod old (S16.mul_mod s r));
        A.((b.(SZ.add base vj) <- S16.add_mod old (S16.mul_mod s r)));
        j := SZ.add vj 1sz;
      };
      with vbf. assert (A.pts_to b vbf);
      rows_extend nbar (n p) vbf (SZ.v vi)
        (fun i' j' -> Loops.repeati (SZ.v vk + 1)
           (M.dot_step nbar (n p) (n p) vsp (F.gen_matrix p vseed) i' j') S16.zero);
      i := SZ.add vi 1sz;
    };
    k := SZ.add vk 1sz;
  };
  with vb. assert (A.pts_to b vb);
  assert (pure (forall (i': nat) (j': nat). i' < nbar /\ j' < n p ==>
                  M.get nbar (n p) vb i' j' ==
                    M.dot nbar (n p) (n p) vsp (F.gen_matrix p vseed) i' j'));
  mul_eq nbar (n p) (n p) vsp (F.gen_matrix p vseed) vb;
  assert (pure (vb == M.mul nbar (n p) (n p) vsp (F.gen_matrix p vseed)));
}

#pop-options
