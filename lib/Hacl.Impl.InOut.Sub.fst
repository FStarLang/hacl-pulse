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

(** Windows of an {!Hacl.Impl.InOut.inout} pair.

    {!Hacl.Impl.Sub} hands out [a[i .. j)] as an array of its own.  For an
    output and an input that may be the same array, the window has to be
    taken of both, at the same offsets, and the result is again an [inout]
    pair: the same array twice if it was before, two disjoint ones if not.

    The output's window is taken with {!Hacl.Impl.Sub.sub} by the caller, who
    always owns [out].  The input's is taken here, by {!sub_in}, out of
    whatever permission on [inp] there is: [inp]'s own [pts_to] when the two
    are disjoint, and when they are the same array, the masked remainder of
    [out] that [Sub.sub] left behind -- [A.sub] does not care that the
    window it is asked for has been lent out already.  In C both are pointer
    arithmetic. *)
module Hacl.Impl.InOut.Sub

#lang-pulse

open Pulse.Lib.Pervasives
open Hacl.Impl.InOut

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module SZ = FStar.SizeT
module Sub = Hacl.Impl.Sub

(** What is left of the pair outside the window. *)
let sub_rest (#t: Type0) (out inp: A.array t) (pi: perm) (i j: nat) (vo vi: Seq.seq t) : slprop =
  if out == inp then Sub.rest out 1.0R i j vo ** pure (suffix_eq i vo vi)
  else Sub.rest out 1.0R i j vo ** Sub.rest inp pi i j vi **
       pure (i <= j /\ j <= A.length out /\ j <= A.length inp /\
                   (A.gsub out i j == A.gsub inp i j ==> i == j))

(** The permission on [inp] that {!sub_in} takes its window out of, and what
    else it has to remember to put things back. *)
let in_mask (#t: Type0) (out inp: A.array t) (pi: perm) (i j: nat) (vo vi: Seq.seq t)
            (f: perm) (s: Seq.seq (option t)) (m: nat -> prop) : slprop =
  if out == inp
  then pure (f == 1.0R /\ s == Sub.opt vo /\ suffix_eq i vo vi /\
             (forall (k: nat). m k <==> ~(i <= k /\ k < j)))
  else Sub.rest out 1.0R i j vo **
       pure (f == pi /\ s == Sub.opt vi /\ (forall (k: nat). m k))

#push-options "--z3rlimit 40"

ghost fn prep_in (#t: Type0) (out inp: A.array t) (i j: nat) (#pi: perm)
                 (#vo: erased (Seq.seq t) { Seq.length vo == A.length out })
                 (#vi: erased (Seq.seq t) { i <= j /\ j <= Seq.length vi /\
                                            Seq.length vo == Seq.length vi /\
                                            Seq.length vi == A.length inp })
requires Sub.rest out 1.0R i j vo ** inout_case out inp pi i vo vi
ensures exists* (f: perm) (s: Seq.seq (option t)) (m: nat -> prop).
  A.pts_to_mask inp #f s m ** in_mask out inp pi i j vo vi f s m **
  pure (Seq.length s == A.length inp)
{
  let b : bool = FStar.IndefiniteDescription.strong_excluded_middle (out == inp);
  if b {
    unfold (Sub.rest out 1.0R i j vo);
    rewrite inout_case out inp pi i vo vi as pure (suffix_eq i vo vi);
    rewrite A.pts_to_mask out #1.0R (Sub.opt vo) (fun k -> ~(i <= k /\ k < j))
         as A.pts_to_mask inp #1.0R (Sub.opt vo) (fun k -> ~(i <= k /\ k < j));
    rewrite pure (1.0R == 1.0R /\ Sub.opt vo == Sub.opt vo /\ suffix_eq i vo vi /\
                  (forall (k: nat). ~(i <= k /\ k < j) <==> ~(i <= k /\ k < j)))
         as in_mask out inp pi i j vo vi 1.0R (Sub.opt vo) (fun k -> ~(i <= k /\ k < j));
  } else {
    rewrite inout_case out inp pi i vo vi as A.pts_to inp #pi vi;
    A.to_mask inp;
    A.mask_ext inp (Sub.opt vi) (fun _ -> True);
    rewrite (Sub.rest out 1.0R i j vo **
             pure (pi == pi /\ Sub.opt vi == Sub.opt vi /\ (forall (k: nat). True)))
         as in_mask out inp pi i j vo vi pi (Sub.opt vi) (fun _ -> True);
  }
}

ghost fn finish_in (#t: Type0) (out inp os is: A.array t) (i j: nat) (#pi: perm)
                   (#vo: erased (Seq.seq t) { Seq.length vo == A.length out })
                   (#vi: erased (Seq.seq t) { i <= j /\ j <= Seq.length vi /\
                                              Seq.length vo == Seq.length vi /\
                                              Seq.length vi == A.length inp })
                   (#f: perm) (#s: Seq.seq (option t) { Seq.length s == A.length inp })
                   (#m: nat -> prop)
requires A.pts_to os (Seq.slice vo i j) **
         A.pts_to_mask is #f (Seq.slice s i j) (fun k -> m (k + i)) **
         A.pts_to_mask inp #f s (fun k -> m k /\ ~(i <= k /\ k < j)) **
         in_mask out inp pi i j vo vi f s m **
         pure (os == A.gsub out i j /\ is == A.gsub inp i j)
ensures inout os is pi 0 (Seq.slice vo i j) (Seq.slice vi i j) **
        sub_rest out inp pi i j vo vi
{
  let b : bool = FStar.IndefiniteDescription.strong_excluded_middle (out == inp);
  if b {
    rewrite in_mask out inp pi i j vo vi f s m
         as pure (f == 1.0R /\ s == Sub.opt vo /\ suffix_eq i vo vi /\
                  (forall (k: nat). m k <==> ~(i <= k /\ k < j)));
    (* The input's window is the output's, already lent out: nothing in it.
       Give the empty window back to [inp]. *)
    rewrite A.pts_to_mask is #f (Seq.slice s i j) (fun k -> m (k + i))
         as A.pts_to_mask (A.gsub inp i j) #f (Seq.slice s i j) (fun k -> m (k + i));
    A.return_sub inp;
    with v' mk. assert (A.pts_to_mask inp #f v' mk);
    A.mask_vext inp s;
    A.mask_mext inp (fun k -> ~(i <= k /\ k < j));
    rewrite A.pts_to_mask inp #f s (fun k -> ~(i <= k /\ k < j))
         as A.pts_to_mask out #1.0R (Sub.opt vo) (fun k -> ~(i <= k /\ k < j));
    fold (Sub.rest out 1.0R i j vo);
    rewrite (Sub.rest out 1.0R i j vo ** pure (suffix_eq i vo vi))
         as sub_rest out inp pi i j vo vi;
    assert (pure (suffix_eq 0 (Seq.slice vo i j) (Seq.slice vi i j)));
    rewrite pure (suffix_eq 0 (Seq.slice vo i j) (Seq.slice vi i j))
         as inout_case os is pi 0 (Seq.slice vo i j) (Seq.slice vi i j);
    fold (inout os is pi 0 (Seq.slice vo i j) (Seq.slice vi i j));
  } else {
    rewrite in_mask out inp pi i j vo vi f s m
         as (Sub.rest out 1.0R i j vo **
             pure (f == pi /\ s == Sub.opt vi /\ (forall (k: nat). m k)));
    A.mask_mext is (fun _ -> True);
    A.from_mask is;
    with w. assert (A.pts_to is #f w);
    assert (pure (Seq.equal w (Seq.slice vi i j)));
    rewrite A.pts_to is #f w as A.pts_to is #pi (Seq.slice vi i j);
    A.mask_mext inp (fun k -> ~(i <= k /\ k < j));
    rewrite A.pts_to_mask inp #f s (fun k -> ~(i <= k /\ k < j))
         as A.pts_to_mask inp #pi (Sub.opt vi) (fun k -> ~(i <= k /\ k < j));
    fold (Sub.rest inp pi i j vi);
    A.pts_to_len os;
    intro_disjoint os is;
    rewrite (Sub.rest out 1.0R i j vo ** Sub.rest inp pi i j vi **
             pure (i <= j /\ j <= A.length out /\ j <= A.length inp /\
                   (A.gsub out i j == A.gsub inp i j ==> i == j)))
         as sub_rest out inp pi i j vo vi;
  }
}

(** The input's window, after the caller has taken the output's with
    [Sub.sub out i j].  Both are at the boundary [i]. *)
inline_for_extraction
fn sub_in (#t: Type0) (out inp: A.array t) (os: A.array t) (i j: SZ.t)
          (#pi: perm) (#vo: erased (Seq.seq t) { Seq.length vo == A.length out })
          (#vi: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length vi /\
                                     Seq.length vo == Seq.length vi /\
                                     Seq.length vi == A.length inp })
requires Sub.rest out 1.0R (SZ.v i) (SZ.v j) vo **
         A.pts_to os (Seq.slice vo (SZ.v i) (SZ.v j)) **
         inout_case out inp pi (SZ.v i) vo vi **
         pure (os == A.gsub out (SZ.v i) (SZ.v j))
returns is: A.array t
ensures inout os is pi 0 (Seq.slice vo (SZ.v i) (SZ.v j)) (Seq.slice vi (SZ.v i) (SZ.v j)) **
        sub_rest out inp pi (SZ.v i) (SZ.v j) vo vi **
        pure (is == A.gsub inp (SZ.v i) (SZ.v j))
{
  prep_in out inp (SZ.v i) (SZ.v j);
  let is = A.sub inp i (hide (SZ.v j));
  finish_in out inp os is (SZ.v i) (SZ.v j);
  is
}

(** Give both windows back.  The callee has run to the end of its window, so
    the boundary of the whole pair is now [j]. *)
ghost fn unsub_inout (#t: Type0) (out inp os is: A.array t) (i: nat) (j: nat)
                     (#pi: perm) (#vo: erased (Seq.seq t))
                     (#vi: erased (Seq.seq t) { i <= j /\ j <= Seq.length vi /\
                                                Seq.length vo == Seq.length vi /\
                                                Seq.length vo == A.length out /\
                                                Seq.length vi == A.length inp })
                     (#vo': erased (Seq.seq t))
requires inout os is pi (j - i) vo' (Seq.slice vi i j) **
         sub_rest out inp pi i j vo vi **
         pure (os == A.gsub out i j /\ is == A.gsub inp i j /\
               Seq.length vo' == j - i)
ensures exists* (w: Seq.seq t).
  inout out inp pi j w vi **
  pure (Seq.length w == Seq.length vo /\
        (forall (k: nat). k < Seq.length w ==>
           Seq.index w k == (if i <= k && k < j then Seq.index vo' (k - i)
                             else Seq.index vo k)))
{
  let b : bool = FStar.IndefiniteDescription.strong_excluded_middle (out == inp);
  if b {
    unfold inout;
    rewrite sub_rest out inp pi i j vo vi
         as (Sub.rest out 1.0R i j vo ** pure (suffix_eq i vo vi));
    rewrite inout_case os is pi (j - i) vo' (Seq.slice vi i j)
         as pure (suffix_eq (j - i) vo' (Seq.slice vi i j));
    Sub.unsub out i j os;
    with w. assert (A.pts_to out w);
    assert (pure (suffix_eq j w vi));
    rewrite pure (suffix_eq j w vi) as inout_case out inp pi j w vi;
    fold (inout out inp pi j w vi);
  } else {
    rewrite sub_rest out inp pi i j vo vi
         as (Sub.rest out 1.0R i j vo ** Sub.rest inp pi i j vi **
             pure (i <= j /\ j <= A.length out /\ j <= A.length inp /\
                   (A.gsub out i j == A.gsub inp i j ==> i == j)));
    elim_disjoint os is;
    Sub.unsub out i j os;
    Sub.unsub_id inp i j is;
    with w. assert (A.pts_to out w);
    rewrite A.pts_to inp #pi vi as inout_case out inp pi j w vi;
    fold (inout out inp pi j w vi);
  }
}

#pop-options
