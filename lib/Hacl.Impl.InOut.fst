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

(** An output array that may or may not be the input array.

    Stream ciphers write [out[i]] from [inp[i]] and never look back, so the
    same code serves [out == inp] (in place) and disjoint arrays, which is
    what the C API has always promised.  [inout out inp pi pos vo vi] says
    that [out] holds [vo] and that the input [vi] is still available from
    position [pos] on: either in [inp], owned separately at [pi], or -- when
    the two are the same array -- in the not-yet-overwritten suffix of [out].

    Nothing here is computational: the case split is on [out == inp], which
    no code tests.  A loop is written once against [inout], reading input
    through [read_in] (or [borrow_in] for a wide load) and writing output at
    the boundary [pos]; the four [intro_]/[elim_] lemmas convert at the
    entry points.

    [intro_disjoint] cannot rule out [out == inp] for empty arrays (there is
    no permission to overflow), so it allows that case and [elim_disjoint]
    rebuilds the input's [pts_to] out of nothing, which is sound because an
    empty array can be shared at any fraction. *)
module Hacl.Impl.InOut

#lang-pulse

open Pulse.Lib.Pervasives

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT

let suffix_eq (#t: Type0) (pos: nat) (vo vi: Seq.seq t) : prop =
  Seq.length vo == Seq.length vi /\ pos <= Seq.length vi /\
  (forall (k: nat). pos <= k /\ k < Seq.length vi ==> Seq.index vo k == Seq.index vi k)

let inout_case (#t: Type0) (out inp: A.array t) (pi: perm) (pos: nat) (vo vi: Seq.seq t) : slprop =
  if out == inp then pure (suffix_eq pos vo vi) else A.pts_to inp #pi vi

let inout (#t: Type0) (out inp: A.array t) (pi: perm) (pos: nat) (vo vi: Seq.seq t) : slprop =
  A.pts_to out vo ** inout_case out inp pi pos vo vi

(** {2 Empty arrays} *)

ghost fn rescale_empty (#t: Type0) (arr: A.array t) (#p: perm) (#v: erased (Seq.seq t)) (q: perm)
  requires A.pts_to arr #p v ** pure (Seq.length v == 0)
  ensures A.pts_to arr #q v
{
  A.to_mask arr;
  A.mask_empty_perm arr q;
  A.from_mask arr;
  with v'. assert (A.pts_to arr #q v');
  assert (pure (Seq.equal v' v));
  rewrite A.pts_to arr #q v' as A.pts_to arr #q v;
}

ghost fn dup_empty (#t: Type0) (arr: A.array t) (#p: perm) (#v: erased (Seq.seq t)) (q: perm)
  preserves A.pts_to arr #p v
  requires pure (Seq.length v == 0)
  ensures A.pts_to arr #q v
{
  A.share arr;
  rescale_empty arr #(p /. 2.0R) q;
  rescale_empty arr #(p /. 2.0R) p;
}

(** {2 Entry and exit} *)

ghost fn intro_inplace (#t: Type0) (buf: A.array t) (#v: erased (Seq.seq t))
  requires A.pts_to buf v
  ensures inout buf buf 1.0R 0 v v
{
  A.pts_to_len buf;
  rewrite pure (suffix_eq 0 v v) as inout_case buf buf 1.0R 0 v v;
  fold (inout buf buf 1.0R 0 v v)
}

ghost fn elim_inplace (#t: Type0) (buf: A.array t) (#pi: perm) (#pos: nat) (#vo #vi: erased (Seq.seq t))
  requires inout buf buf pi pos vo vi
  ensures A.pts_to buf vo ** pure (suffix_eq pos vo vi)
{
  unfold inout;
  rewrite inout_case buf buf pi pos vo vi as pure (suffix_eq pos vo vi);
}

ghost fn intro_disjoint (#t: Type0) (out inp: A.array t) (#pi: perm) (#vo #vi: erased (Seq.seq t))
  requires A.pts_to out vo ** A.pts_to inp #pi vi ** pure (Seq.length vo == Seq.length vi)
  ensures inout out inp pi 0 vo vi ** pure (out == inp ==> Seq.length vi == 0)
{
  A.pts_to_len out;
  A.pts_to_len inp;
  let b : bool = FStar.IndefiniteDescription.strong_excluded_middle (out == inp);
  if b {
    rewrite A.pts_to inp #pi vi as A.pts_to out #pi vi;
    let nz : bool = Seq.length vi > 0;
    if nz {
      A.gather out;
      A.pts_to_perm_bound out;
      unreachable ()
    } else {
      (* Both halves describe the same empty array: merge them back to one. *)
      A.gather out;
      rescale_empty out #(1.0R +. pi) 1.0R;
      rewrite pure (suffix_eq 0 vo vi) as inout_case out inp pi 0 vo vi;
      fold (inout out inp pi 0 vo vi)
    }
  } else {
    rewrite A.pts_to inp #pi vi as inout_case out inp pi 0 vo vi;
    fold (inout out inp pi 0 vo vi)
  }
}

ghost fn elim_disjoint (#t: Type0) (out inp: A.array t) (#pi: perm) (#pos: nat) (#vo #vi: erased (Seq.seq t))
  requires inout out inp pi pos vo vi ** pure (out == inp ==> Seq.length vi == 0)
  ensures A.pts_to out vo ** A.pts_to inp #pi vi
{
  unfold inout;
  let b : bool = FStar.IndefiniteDescription.strong_excluded_middle (out == inp);
  if b {
    rewrite inout_case out inp pi pos vo vi as pure (suffix_eq pos vo vi);
    A.pts_to_len out;
    dup_empty out pi;
    assert (pure (Seq.equal vo vi));
    rewrite A.pts_to out #pi vo as A.pts_to inp #pi vi;
  } else {
    rewrite inout_case out inp pi pos vo vi as A.pts_to inp #pi vi;
  }
}

(** {2 Writing}

    After writing [out] directly (unfold [inout] to get at it), move the
    boundary up to [pos'], which needs [out]'s new contents to agree with the
    old from [pos'] on. *)

ghost fn inout_advance (#t: Type0) (out inp: A.array t) (#pi: perm) (#pos: nat) (pos': nat)
                       (#vo #vo' #vi: erased (Seq.seq t))
  requires A.pts_to out vo' ** inout_case out inp pi pos vo vi **
           pure (pos <= pos' /\ pos' <= Seq.length vi /\
                 Seq.length vo' == Seq.length vo /\
                 (forall (k: nat). pos' <= k /\ k < Seq.length vo ==> Seq.index vo' k == Seq.index vo k))
  ensures inout out inp pi pos' vo' vi
{
  let b : bool = FStar.IndefiniteDescription.strong_excluded_middle (out == inp);
  if b {
    rewrite inout_case out inp pi pos vo vi as pure (suffix_eq pos vo vi);
    rewrite pure (suffix_eq pos' vo' vi) as inout_case out inp pi pos' vo' vi;
  } else {
    rewrite inout_case out inp pi pos vo vi as A.pts_to inp #pi vi;
    rewrite A.pts_to inp #pi vi as inout_case out inp pi pos' vo' vi;
  };
  fold (inout out inp pi pos' vo' vi)
}

(** Write one element at the boundary. *)
inline_for_extraction
fn write_out (#t: Type0) (out inp: A.array t) (i: SZ.t) (x: t)
             (#pi: perm) (#pos: nat) (#vo #vi: erased (Seq.seq t))
  requires inout out inp pi pos vo vi **
           pure (SZ.v i == pos /\ pos < Seq.length vi /\ Seq.length vo == Seq.length vi)
  ensures exists* (vo': Seq.seq t). inout out inp pi (pos + 1) vo' vi **
    pure (SZ.v i < Seq.length vo /\ vo' == Seq.upd vo (SZ.v i) x)
{
  unfold inout;
  A.(out.(i) <- x);
  inout_advance out inp (pos + 1);
}

(** {2 Reading}

    [borrow_in] presents the input as a single array [inp], at some
    permission, agreeing with [vi] from [pos] on; [return_in] gives it back.
    In between, [inp] can be read like any other array. *)

let borrowed (#t: Type0) (out inp: A.array t) (pi: perm) (pos: nat) (vo vi: Seq.seq t)
             (q: perm) (v: Seq.seq t) : slprop =
  if out == inp then pure (q == 1.0R /\ v == vo /\ suffix_eq pos vo vi)
  else A.pts_to out vo ** pure (q == pi /\ v == vi)

ghost fn borrow_in (#t: Type0) (out inp: A.array t) (#pi: perm) (#pos: nat) (#vo #vi: erased (Seq.seq t))
  requires inout out inp pi pos vo vi
  ensures exists* (q: perm) (v: Seq.seq t).
    A.pts_to inp #q v ** borrowed out inp pi pos vo vi q v **
    pure (Seq.length v == Seq.length vi /\
          (forall (k: nat). pos <= k /\ k < Seq.length vi ==> Seq.index v k == Seq.index vi k))
{
  unfold inout;
  let b : bool = FStar.IndefiniteDescription.strong_excluded_middle (out == inp);
  if b {
    rewrite inout_case out inp pi pos vo vi as pure (suffix_eq pos vo vi);
    rewrite A.pts_to out vo as A.pts_to inp #1.0R vo;
    rewrite pure (1.0R == 1.0R /\ reveal vo == reveal vo /\ suffix_eq pos vo vi)
         as borrowed out inp pi pos vo vi 1.0R vo;
  } else {
    rewrite inout_case out inp pi pos vo vi as A.pts_to inp #pi vi;
    A.pts_to_len inp;
    rewrite (A.pts_to out vo ** pure (pi == pi /\ reveal vi == reveal vi))
         as borrowed out inp pi pos vo vi pi vi;
  }
}

ghost fn return_in (#t: Type0) (out inp: A.array t) (#pi: perm) (#pos: nat) (#vo #vi: erased (Seq.seq t))
                   (#q: perm) (#v: erased (Seq.seq t))
  requires A.pts_to inp #q v ** borrowed out inp pi pos vo vi q v
  ensures inout out inp pi pos vo vi
{
  let b : bool = FStar.IndefiniteDescription.strong_excluded_middle (out == inp);
  if b {
    rewrite borrowed out inp pi pos vo vi q v
         as pure (q == 1.0R /\ reveal v == reveal vo /\ suffix_eq pos vo vi);
    rewrite A.pts_to inp #q v as A.pts_to out vo;
    rewrite pure (suffix_eq pos vo vi) as inout_case out inp pi pos vo vi;
  } else {
    rewrite borrowed out inp pi pos vo vi q v
         as (A.pts_to out vo ** pure (q == pi /\ reveal v == reveal vi));
    rewrite A.pts_to inp #q v as inout_case out inp pi pos vo vi;
  };
  fold (inout out inp pi pos vo vi)
}

(** The input's length is an array length, so it fits a [SZ.t]. *)
ghost fn inout_len (#t: Type0) (out inp: A.array t) (#pi: perm) (#pos: nat) (#vo #vi: erased (Seq.seq t))
  preserves inout out inp pi pos vo vi
  ensures pure (A.length inp == Seq.length vi /\ SZ.fits (Seq.length vi))
{
  borrow_in out inp;
  A.pts_to_len inp;
  return_in out inp;
}

(** Read one input element at or past the boundary. *)
inline_for_extraction
fn read_in (#t: Type0) (out inp: A.array t) (i: SZ.t)
           (#pi: perm) (#pos: nat) (#vo #vi: erased (Seq.seq t))
  preserves inout out inp pi pos vo vi
  requires pure (pos <= SZ.v i /\ SZ.v i < Seq.length vi)
  returns x: t
  ensures pure (SZ.v i < Seq.length vi /\ x == Seq.index vi (SZ.v i))
{
  borrow_in out inp;
  let x = A.(inp.(i));
  return_in out inp;
  x
}
