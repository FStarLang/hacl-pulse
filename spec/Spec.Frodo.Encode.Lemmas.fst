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

(** Decoding a noisy encoding recovers the message.

    [key_encode] puts each [bits]-wide field [k] of the message at the top
    of a [logq]-bit entry, as [k * 2^(logq - bits)], and [dc] rounds it back
    by adding half a step, [2^(logq - bits - 1)], and truncating.  So if the
    entry is perturbed by [e] with [-2^(logq - bits - 1) <= e < 2^(logq -
    bits - 1)] -- [e] is the centered representative of the perturbation
    modulo [q = 2^logq], and only its residue matters -- the rounding still
    lands on [k] ([dc_round]).  This is the exact tolerance of [dc]; the
    statement below asks for the symmetric [|e| < 2^(logq - bits - 1)], which
    is [q / 2^(bits + 1)] and the bound in the FrodoKEM specification's
    correctness analysis.

    [key_decode] then reassembles the fields of each row into the integer
    they came from ([row_head_chunk]: a little-endian number is the sum of
    its fields) and reads the bytes back out ([Hacl.Spec.Bytes.le_nat_byte]).
    The headline is [key_decode_noisy]. *)
module Spec.Frodo.Encode.Lemmas

open Spec.Frodo.Params
open Spec.Frodo

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module Math = FStar.Math.Lemmas
module M = Spec.Frodo.Matrix
module B = Hacl.Spec.Bytes

(** The representative of [x] modulo [q] in [[-q/2, q/2)]. *)
let centered (q: pos) (x: int) : int =
  let r = x % q in if r < q / 2 then r else r - q

(** An entry of the noise is small: its centered representative modulo
    [q = 2^logq] is less than [q / 2^(bits + 1)] in absolute value. *)
let small (p: params) (x: S16.t) : GTot prop =
  abs (centered (pow2 (logq p)) (S16.v x)) < pow2 (logq p - bits p - 1)

#push-options "--fuel 0 --ifuel 0"

let centered_mod (q: pos) (x: int) : Lemma (centered q x % q == x % q)
  = Math.lemma_mod_sub (x % q) q 1;
    Math.lemma_mod_twice x q

(** {2 Rounding one entry} *)

let dc_round (p: params) (c: S16.t) (kk: nat) (e: int)
  : Lemma (requires kk < pow2 (bits p) /\
                    - pow2 (logq p - bits p - 1) <= e /\ e < pow2 (logq p - bits p - 1) /\
                    S16.v c % pow2 (logq p) == (kk * pow2 (logq p - bits p) + e) % pow2 (logq p))
          (ensures dc p c == kk)
  = let q = pow2 (logq p) in
    let w = pow2 (logq p - bits p) in
    let h = pow2 (logq p - bits p - 1) in
    let y = (S16.v c + h) % pow2 16 in
    Math.pow2_plus (logq p - bits p) (bits p);
    Math.modulo_division_lemma y w (pow2 (bits p));
    Math.pow2_modulo_modulo_lemma_1 (S16.v c + h) (logq p) 16;
    Math.lemma_mod_plus_distr_l (S16.v c) h q;
    Math.lemma_mod_plus_distr_l (kk * w + e) h q;
    Math.pow2_double_sum (logq p - bits p - 1);
    Math.lemma_mult_le_right w kk (pow2 (bits p) - 1);
    Math.distributivity_sub_left (pow2 (bits p)) 1 w;
    Math.small_mod (kk * w + (e + h)) q;
    Math.lemma_div_plus (e + h) kk w;
    Math.small_div (e + h) w

(** {2 Reassembling a row} *)

let mod_split (x: nat) (a b: pos)
  : Lemma (x % (a * b) == x % a + ((x / a) % b) * a)
  = Math.modulo_modulo_lemma x a b;
    Math.modulo_division_lemma x a b;
    Math.euclidean_division_definition (x % (a * b)) a

(** [2^(bits * k)], the weight of field [k]. *)
let pw (p: params) (k: nat) : pos = pow2 (bits p * k)

let field (p: params) (x: nat) (k: nat) : nat = (x / pw p k) % pow2 (bits p)

let low (p: params) (x: nat) (k: nat) : nat = x % pw p k

let pw_step (p: params) (k: pos) : Lemma (pw p (k - 1) * pow2 (bits p) == pw p k)
  = Math.pow2_plus (bits p * (k - 1)) (bits p);
    Math.distributivity_sub_right (bits p) k 1

#push-options "--fuel 1"

let row_head_zero (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar })
  : Lemma (row_head p m i 0 == 0)
  = ()

let row_head_step (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar }) (k: pos { k <= nbar })
  : Lemma (row_head p m i k == row_head p m i (k - 1) + dc p (M.get nbar nbar m i (k - 1)) * pw p (k - 1))
  = ()

#pop-options

let rec row_head_chunk (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar }) (x: nat)
                       (k: nat { k <= nbar })
  : Lemma (requires forall (k': nat). k' < nbar ==> dc p (M.get nbar nbar m i k') == field p x k')
          (ensures row_head p m i k == low p x k)
          (decreases k)
  = if k = 0 then begin
      assert_norm (pow2 0 == 1);
      row_head_zero p m i;
      Math.cancel_mul_mod x 1
    end else begin
      row_head_chunk p m i x (k - 1);
      pw_step p k;
      mod_split x (pw p (k - 1)) (pow2 (bits p));
      row_head_step p m i k
    end


let key_decode_fields (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) (m: M.matrix nbar nbar)
  : Lemma (requires forall (i k: nat). i < nbar /\ k < nbar ==>
                      dc p (M.get nbar nbar m i k) == field p (mu_chunk p mu i) k)
          (ensures key_decode p m == mu)
  = let b = bits p in
    introduce forall (t: nat). t < bytes_mu p ==> Seq.index (key_decode p m) t == Seq.index mu t
    with introduce _ ==> _ with begin
      M.div_lt t nbar b;
      let i = t / b in
      let k = t % b in
      Math.lemma_mult_le_right b (i + 1) nbar;
      Math.distributivity_add_left i 1 b;
      let s = Seq.slice mu (i * b) (i * b + b) in
      let x = mu_chunk p mu i in
      assert (x == B.le_nat s);
      row_head_chunk p m i x nbar;
      B.le_nat_bound s;
      Math.small_mod x (pw p nbar);
      B.le_nat_byte s k;
      Math.euclidean_division_definition t b;
      assert (Seq.index s k == Seq.index mu t);
      assert (S8.v (Seq.index (key_decode p m) t) == S8.v (Seq.index mu t))
    end;
    Seq.lemma_eq_intro (key_decode p m) mu

(** {2 The headline} *)

let key_encode_get (p: params) (mu: Seq.lseq S8.t (bytes_mu p))
                   (i: nat { i < nbar }) (k: nat { k < nbar })
  : Lemma (S16.v (M.get nbar nbar (key_encode p mu) i k) ==
           field p (mu_chunk p mu i) k * pow2 (logq p - bits p))
  = M.index_bound nbar nbar i k;
    M.get_flat nbar nbar (key_encode p mu) (i * nbar + k);
    Math.lemma_div_plus k i nbar;
    Math.lemma_mod_plus k i nbar;
    Math.small_div k nbar;
    Math.small_mod k nbar;
    ec_bound p (mu_chunk p mu i) k

let entry_round (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) (m e: M.matrix nbar nbar)
                (i: nat { i < nbar }) (k: nat { k < nbar })
  : Lemma (requires small p (M.get nbar nbar e i k) /\
                    S16.v (M.get nbar nbar m i k) % pow2 (logq p) ==
                    (S16.v (M.get nbar nbar (key_encode p mu) i k) +
                     S16.v (M.get nbar nbar e i k)) % pow2 (logq p))
          (ensures dc p (M.get nbar nbar m i k) == field p (mu_chunk p mu i) k)
  = let q = pow2 (logq p) in
    let ev = S16.v (M.get nbar nbar e i k) in
    let c = centered q ev in
    let enc = field p (mu_chunk p mu i) k * pow2 (logq p - bits p) in
    key_encode_get p mu i k;
    centered_mod q ev;
    Math.lemma_mod_plus_distr_r enc ev q;
    Math.lemma_mod_plus_distr_r enc c q;
    dc_round p (M.get nbar nbar m i k) (field p (mu_chunk p mu i) k) c

(** If every entry of [m] is the encoding of [mu] plus a small error, modulo
    [2^logq], then [m] decodes to [mu]. *)
let key_decode_noisy (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) (m e: M.matrix nbar nbar)
  : Lemma (requires forall (i k: nat). i < nbar /\ k < nbar ==>
                      small p (M.get nbar nbar e i k) /\
                      S16.v (M.get nbar nbar m i k) % pow2 (logq p) ==
                      (S16.v (M.get nbar nbar (key_encode p mu) i k) +
                       S16.v (M.get nbar nbar e i k)) % pow2 (logq p))
          (ensures key_decode p m == mu)
  = introduce forall (i k: nat). i < nbar /\ k < nbar ==>
                dc p (M.get nbar nbar m i k) == field p (mu_chunk p mu i) k
    with introduce _ ==> _ with entry_round p mu m e i k;
    key_decode_fields p mu m

#pop-options
