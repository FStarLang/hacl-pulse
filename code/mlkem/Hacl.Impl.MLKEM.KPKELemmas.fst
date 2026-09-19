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


(** The pure obligations of K-PKE.

    Two kinds live here.  The first is the arithmetic of reading a
    concatenation back: the Pulse functions fill a buffer a piece at a
    time and the specification says what it is with [Seq.append] and
    [Seq.slice].  The second is one "spelled out" lemma per algorithm,
    which takes the equations the Pulse function establishes -- one per
    buffer, each naming its own intermediate -- and folds them into the
    specification in a single pure query.  Asking the solver to do that
    fold inside the Pulse function is what runs out of rlimit; see
    {!Hacl.Frodo.KEM} for the same device.

    The module opens only specifications and the (small, pure)
    {!Hacl.Impl.MLKEM.Zq}, because a pure lemma that sees a large Pulse
    module in its context can cost minutes. *)
module Hacl.Impl.MLKEM.KPKELemmas

open Spec.MLKEM
open Spec.MLKEM.Zq
open Spec.MLKEM.Params
open Spec.MLKEM.NTT
open Spec.MLKEM.Encode
open Spec.MLKEM.Sample
open Hacl.Impl.MLKEM.Zq

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 Reading a concatenation back} *)

let seq_eq (a b: Seq.seq S8.t)
  : Lemma (requires Seq.length a == Seq.length b /\
                    (forall (t: nat). t < Seq.length a ==> Seq.index a t == Seq.index b t))
          (ensures a == b)
  = Seq.lemma_eq_intro a b

let slice_eq (v: Seq.seq S8.t) (base: nat) (r: Seq.seq S8.t)
  : Lemma (requires base + Seq.length r <= Seq.length v /\
                    (forall (t: nat). t < Seq.length r ==>
                       Seq.index r t == Seq.index v (base + t)))
          (ensures r == Seq.slice v base (base + Seq.length r))
  = Seq.lemma_eq_intro r (Seq.slice v base (base + Seq.length r))

let append2_eq (a b res: Seq.seq S8.t)
  : Lemma (requires Seq.length res == Seq.length a + Seq.length b /\
                    (forall (t: nat). t < Seq.length a ==> Seq.index res t == Seq.index a t) /\
                    (forall (t: nat). t < Seq.length b ==>
                       Seq.index res (Seq.length a + t) == Seq.index b t))
          (ensures res == Seq.append a b)
  = Seq.lemma_eq_intro res (Seq.append a b)

(** The module rank goes on the end of the key-generation seed, so that
    the same seed under two parameter sets gives unrelated keys. *)
let snoc_eq (s: Seq.seq S8.t) (x: S8.t) (res: Seq.seq S8.t)
  : Lemma (requires Seq.length res == Seq.length s + 1 /\
                    (forall (t: nat). t < Seq.length s ==> Seq.index res t == Seq.index s t) /\
                    Seq.index res (Seq.length s) == x)
          (ensures res == Seq.snoc s x)
  = Seq.lemma_eq_intro res (Seq.snoc s x)

(** {2 Views} *)

(** The elementwise loops of {!Hacl.Impl.MLKEM.Vec} leave a pointwise
    statement about [S16.v]; the specifications are [vec_add] and
    [vec_sub] of the views. *)
let vec_add_intro (k: pos) (a b r: Seq.lseq zqt (k * n))
  : Lemma (requires forall (t: nat). t < k * n ==>
             S16.v (Seq.index r t) == add (S16.v (Seq.index a t)) (S16.v (Seq.index b t)))
          (ensures as_zqs r == vec_add #k (as_zqs a) (as_zqs b))
  = Seq.lemma_eq_intro (as_zqs r) (vec_add #k (as_zqs a) (as_zqs b))

let vec_sub_intro (k: pos) (a b r: Seq.lseq zqt (k * n))
  : Lemma (requires forall (t: nat). t < k * n ==>
             S16.v (Seq.index r t) == sub (S16.v (Seq.index a t)) (S16.v (Seq.index b t)))
          (ensures as_zqs r == vec_sub #k (as_zqs a) (as_zqs b))
  = Seq.lemma_eq_intro (as_zqs r) (vec_sub #k (as_zqs a) (as_zqs b))

let poly_add_intro (a b r: Seq.lseq zqt n)
  : Lemma (requires forall (t: nat). t < n ==>
             S16.v (Seq.index r t) == add (S16.v (Seq.index a t)) (S16.v (Seq.index b t)))
          (ensures as_poly r == poly_add (as_poly a) (as_poly b))
  = Seq.lemma_eq_intro (as_poly r) (poly_add (as_poly a) (as_poly b))

let poly_sub_intro (a b r: Seq.lseq zqt n)
  : Lemma (requires forall (t: nat). t < n ==>
             S16.v (Seq.index r t) == sub (S16.v (Seq.index a t)) (S16.v (Seq.index b t)))
          (ensures as_poly r == poly_sub (as_poly a) (as_poly b))
  = Seq.lemma_eq_intro (as_poly r) (poly_sub (as_poly a) (as_poly b))

(** {2 The three algorithms, spelled out} *)

(** Algorithm 13. *)
let keygen_eq (p: params) (d: Seq.lseq S8.t 32)
              (vek: Seq.lseq S8.t (ek_len p)) (vdk: Seq.lseq S8.t (dk_pke_len p))
  : Lemma
      (requires
        (let g = hash_g (Seq.snoc d (S8.classify (U8.uint_to_t p.k))) in
         let rho = Seq.slice g 0 32 in
         let sigma = Seq.slice g 32 64 in
         let a = gen_matrix p.k rho false in
         let s = vec_ntt (noise_vec p.k p.eta1 sigma 0) in
         let e = vec_ntt (noise_vec p.k p.eta1 sigma p.k) in
         let t = vec_add (mat_vec_mul a s) e in
         vek == Seq.append (vec_encode_12 t) rho /\ vdk == vec_encode_12 s))
      (ensures vek == fst (kpke_keygen p d) /\ vdk == snd (kpke_keygen p d))
  = ()

#pop-options
