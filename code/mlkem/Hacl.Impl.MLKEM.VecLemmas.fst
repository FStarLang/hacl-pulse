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

(** The pure lemmas behind the vector loops.

    These live in a module of their own, and one that deliberately does not
    open the Pulse implementation modules, because opening a large Pulse
    module puts its whole encoding into the solver's context: the very same
    lemmas take four seconds here and eight minutes when
    {!Hacl.Impl.MLKEM.NTT} is in scope. *)
module Hacl.Impl.MLKEM.VecLemmas

open Spec.MLKEM.Zq
open Spec.MLKEM.NTT
open Hacl.Impl.MLKEM.Zq

module Seq = FStar.Seq
module S16 = Hacl.Secret.UInt16
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** Coefficient [i m + j] of a flat sequence is coefficient [j] of block
    [i]. *)
let flat_index (#a: Type) (k: pos) (m: pos) (v: Seq.lseq a (k * m))
               (i: nat { i < k }) (j: nat { j < m })
  : Lemma (Seq.index v (i * m + j) == Seq.index (flat_at k m v i) j)
  = Math.lemma_mult_le_right m (i + 1) k;
    Seq.lemma_index_slice v (i * m) (i * m + m) j

(** Every coefficient of block [i] at once. *)
let flat_index_all (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (forall (j: nat). j < n ==> Seq.index v (i * n + j) == Seq.index (vec_at v i) j)
  = FStar.Classical.forall_intro (flat_index k n v i)

(** Two blocks of a flat sequence do not overlap. *)
let flat_disjoint (k: pos) (m: pos) (i: nat { i < k }) (j: nat { j < k })
  : Lemma (requires i <> j)
          (ensures (i < j ==> i * m + m <= j * m) /\ (j < i ==> j * m + m <= i * m))
  = if i < j then Math.lemma_mult_le_right m (i + 1) j
             else Math.lemma_mult_le_right m (j + 1) i

(** One step of a per-entry loop: entries below [i] already hold [f] applied
    to the corresponding entry of the input, entry [i] has just been replaced
    by [b], and the rest is untouched.  Stating this once, as a pure lemma,
    keeps the loop's own verification condition small. *)
let entry_step (k: pos) (i: nat { i < k })
               (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n) (r: pvec k)
  : Lemma (requires
      Seq.length vv == k * n /\ Seq.length w0 == k * n /\
      Seq.length w1 == k * n /\ Seq.length b == n /\
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==> S16.v (Seq.index w0 t) == Seq.index r t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == vec_at #k r i)
    (ensures
      (forall (t: nat). t < (i + 1) * n ==> S16.v (Seq.index w1 t) == Seq.index r t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = flat_index_all k r i

(** Entrywise characterisation of [vec_ntt]. *)
let vec_ntt_at (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_ntt #k v) i == ntt (vec_at #k v i))
  = vec_at_of_fun k (fun j -> ntt (vec_at #k v j)) i

(** The two specialisations of the lemmas above to [vec_ntt].  Their whole
    point is that a caller never has to write [vec_ntt] as an argument:
    a lemma argument mentioning it costs minutes of elaboration, whereas the
    same term inside a [pure] assertion is free. *)
let ntt_entry_step (k: pos) (i: nat { i < k })
                   (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      Seq.length vv == k * n /\ Seq.length w0 == k * n /\
      Seq.length w1 == k * n /\ Seq.length b == n /\
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S16.v (Seq.index w0 t) == Seq.index (vec_ntt #k (as_zqs vv)) t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == ntt (vec_at #k (as_zqs vv) i))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S16.v (Seq.index w1 t) == Seq.index (vec_ntt #k (as_zqs vv)) t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = vec_ntt_at k (as_zqs vv) i;
    entry_step k i vv w0 w1 b (vec_ntt #k (as_zqs vv))

let ntt_entry_done (k: pos) (vv w: Seq.lseq zqt (k * n))
  : Lemma (requires
      Seq.length vv == k * n /\ Seq.length w == k * n /\
      (forall (t: nat). t < k * n ==>
         S16.v (Seq.index w t) == Seq.index (vec_ntt #k (as_zqs vv)) t))
    (ensures as_zqs w == vec_ntt #k (as_zqs vv))
  = as_zqs_intro w (vec_ntt #k (as_zqs vv))


#pop-options
