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

(** The pure lemmas behind the matrix and noise loops.

    As in {!Hacl.Impl.MLKEM.VecLemmas}, they live apart from the Pulse code
    that uses them: a statement mentioning [sample_ntt] unfolds into
    Keccak, and the elaborator will happily spend minutes on it at every
    call site.  Stated here once and applied to sequences only, the callers
    never have to write [gen_matrix] or [noise_vec] as an argument. *)
module Hacl.Impl.MLKEM.GenLemmas

open Spec.MLKEM.Zq
open Spec.MLKEM.Sample
open Spec.MLKEM
open Hacl.Impl.MLKEM.Zq
open Hacl.Impl.MLKEM.VecLemmas

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The matrix} *)

(** Entry [c] of the matrix is [SampleNTT] of the seed built from the two
    indices [c] decomposes into. *)
let gen_matrix_at (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool)
                  (c: nat { c < k * k })
  : Lemma (div_lt c k k;
           flat_at (k * k) n (gen_matrix k rho tr) c ==
             (let i = c / k in
              let j = c % k in
              if tr then sample_ntt (matrix_seed rho j i)
              else sample_ntt (matrix_seed rho i j)))
  = flat_at_of_fun_g (k * k) n
      (fun c ->
         div_lt c k k;
         let i = c / k in
         let j = c % k in
         if tr then sample_ntt (matrix_seed rho j i)
         else sample_ntt (matrix_seed rho i j))
      c

let gen_entry_step (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool)
                   (c: nat { c < k * k })
                   (w0 w1: Seq.lseq zqt (k * k * n)) (b: Seq.lseq zqt n)
                   (sd: Seq.lseq S8.t 34)
  : Lemma (requires
      (forall (t: nat). t < k * k * n ==>
         Seq.index w1 t == (if c * n <= t && t < c * n + n
                            then Seq.index b (t - c * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < c * n ==>
         S16.v (Seq.index w0 t) == Seq.index (gen_matrix k rho tr) t) /\
      (div_lt c k k;
       sd == matrix_seed rho (if tr then c % k else c / k)
                             (if tr then c / k else c % k)) /\
      as_poly b == sample_ntt sd)
    (ensures forall (t: nat). t < (c + 1) * n ==>
       S16.v (Seq.index w1 t) == Seq.index (gen_matrix k rho tr) t)
  = gen_matrix_at k rho tr c;
    flat_step (k * k) n (fun (x: zqt) -> (S16.v x <: zq)) c w0 w1 b
              (gen_matrix k rho tr)

let gen_entry_done (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (tr: bool)
                   (w: Seq.lseq zqt (k * k * n))
  : Lemma (requires
      forall (t: nat). t < k * k * n ==>
        S16.v (Seq.index w t) == Seq.index (gen_matrix k rho tr) t)
    (ensures as_zqs w == gen_matrix k rho tr)
  = as_zqs_intro w (gen_matrix k rho tr)

(** {2 The noise vector} *)

let noise_vec_at (k: pos { k <= 4 }) (eta: pos { eta <= 3 })
                 (s: Seq.lseq S8.t 32) (start: nat { start + k <= 256 })
                 (i: nat { i < k })
  : Lemma (vec_at (noise_vec k eta s start) i ==
           sample_poly_cbd eta s (U8.uint_to_t (start + i)))
  = vec_at_of_fun_g k (fun j -> sample_poly_cbd eta s (U8.uint_to_t (start + j))) i

let noise_entry_step (k: pos { k <= 4 }) (eta: pos { eta <= 3 })
                     (s: Seq.lseq S8.t 32) (start: nat { start + k <= 256 })
                     (i: nat { i < k })
                     (w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S16.v (Seq.index w0 t) == Seq.index (noise_vec k eta s start) t) /\
      as_poly b == sample_poly_cbd eta s (U8.uint_to_t (start + i)))
    (ensures forall (t: nat). t < (i + 1) * n ==>
       S16.v (Seq.index w1 t) == Seq.index (noise_vec k eta s start) t)
  = noise_vec_at k eta s start i;
    flat_step k n (fun (x: zqt) -> (S16.v x <: zq)) i w0 w1 b
              (noise_vec k eta s start)

let noise_entry_done (k: pos { k <= 4 }) (eta: pos { eta <= 3 })
                     (s: Seq.lseq S8.t 32) (start: nat { start + k <= 256 })
                     (w: Seq.lseq zqt (k * n))
  : Lemma (requires
      forall (t: nat). t < k * n ==>
        S16.v (Seq.index w t) == Seq.index (noise_vec k eta s start) t)
    (ensures as_zqs w == noise_vec k eta s start)
  = as_zqs_intro w (noise_vec k eta s start)

(** The seed of entry [(a, b)], in the form the implementation builds it:
    [rho] then the column index then the row index, transposed or not. *)
let seed_eq (rho: Seq.lseq S8.t 32) (a: nat { a < 256 }) (b: nat { b < 256 })
            (tr: bool) (v: Seq.lseq S8.t 34)
  : Lemma (requires
      (forall (t: nat). t < 32 ==> Seq.index v t == Seq.index rho t) /\
      S8.v (Seq.index v 32) == (if tr then a else b) /\
      S8.v (Seq.index v 33) == (if tr then b else a))
    (ensures v == matrix_seed rho (if tr then b else a) (if tr then a else b))
  = if tr then Seq.lemma_eq_intro v (matrix_seed rho b a)
    else Seq.lemma_eq_intro v (matrix_seed rho a b)

#pop-options
