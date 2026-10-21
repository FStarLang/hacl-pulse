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
module Loops = Hacl.Spec.Loops

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

(** The same three lemmas for the inverse transform. *)
let vec_intt_at (k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_intt #k v) i == intt (vec_at #k v i))
  = vec_at_of_fun k (fun j -> intt (vec_at #k v j)) i

let intt_entry_step (k: pos) (i: nat { i < k })
                    (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S16.v (Seq.index w0 t) == Seq.index (vec_intt #k (as_zqs vv)) t) /\
      (forall (t: nat). i * n <= t /\ t < k * n ==> Seq.index w0 t == Seq.index vv t) /\
      as_poly b == intt (vec_at #k (as_zqs vv) i))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S16.v (Seq.index w1 t) == Seq.index (vec_intt #k (as_zqs vv)) t) /\
      (forall (t: nat). (i + 1) * n <= t /\ t < k * n ==> Seq.index w1 t == Seq.index vv t))
  = vec_intt_at k (as_zqs vv) i;
    entry_step k i vv w0 w1 b (vec_intt #k (as_zqs vv))

let intt_entry_done (k: pos) (vv w: Seq.lseq zqt (k * n))
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         S16.v (Seq.index w t) == Seq.index (vec_intt #k (as_zqs vv)) t))
    (ensures as_zqs w == vec_intt #k (as_zqs vv))
  = as_zqs_intro w (vec_intt #k (as_zqs vv))

(** {2 The dot product} *)

(** The partial sum after [m] terms.  [dot] itself is the same [repeati] run
    to [k], so the two agree by definition once [m] is [k]. *)
let dot_acc (#k: pos) (u v: pvec k) (m: nat { m <= k }) : poly
  = Loops.repeati m
      (fun i acc ->
         if i < k then poly_add acc (multiply_ntts (vec_at u i) (vec_at v i))
         else acc)
      poly_zero

let dot_acc_zero (#k: pos) (u v: pvec k)
  : Lemma (dot_acc u v 0 == poly_zero)
  = Loops.repeati_zero #poly
      (fun i acc ->
         if i < k then poly_add acc (multiply_ntts (vec_at u i) (vec_at v i))
         else acc)
      poly_zero

let dot_acc_succ (#k: pos) (u v: pvec k) (m: nat { m < k })
  : Lemma (dot_acc u v (m + 1) ==
           poly_add (dot_acc u v m) (multiply_ntts (vec_at u m) (vec_at v m)))
  = Loops.unfold_repeati #poly m
      (fun i acc ->
         if i < k then poly_add acc (multiply_ntts (vec_at u i) (vec_at v i))
         else acc)
      poly_zero

let dot_acc_full (#k: pos) (u v: pvec k)
  : Lemma (dot_acc u v k == dot u v)
  = ()

(** {3 Pair by pair}

    The implementation does not form the [k] products and add them: every
    base-case product is a sum of products of coefficients, so the [k] of
    them for one pair are a longer such sum, accumulated exactly and reduced
    once.  [psum vu vv a b m] is that sum over the first [m] entries, of
    coefficient [a] of [u] times coefficient [b] of [v]; terms outside the
    sequences count as zero, which keeps it total. *)
let rec psum (vu vv: Seq.seq zqt) (a b: nat) (m: nat) : GTot nat (decreases m)
  = if m = 0 then 0
    else
      let j = m - 1 in
      psum vu vv a b j +
      (if j * n + a < Seq.length vu && j * n + b < Seq.length vv
       then S16.v (Seq.index vu (j * n + a)) * S16.v (Seq.index vv (j * n + b))
       else 0)

let prod_bound (a b: zq) : Lemma (a * b <= (q - 1) * (q - 1))
  = Math.lemma_mult_le_right b a (q - 1);
    Math.lemma_mult_le_left (q - 1) b (q - 1)

#push-options "--fuel 1"
let psum_zero (vu vv: Seq.seq zqt) (a b: nat) : Lemma (psum vu vv a b 0 == 0) = ()

let psum_succ (vu vv: Seq.seq zqt) (a b: nat) (j: nat)
  : Lemma (requires j * n + a < Seq.length vu /\ j * n + b < Seq.length vv)
          (ensures psum vu vv a b (j + 1) ==
                   psum vu vv a b j +
                   S16.v (Seq.index vu (j * n + a)) * S16.v (Seq.index vv (j * n + b)))
  = ()

let rec psum_bound (vu vv: Seq.seq zqt) (a b: nat) (m: nat)
  : Lemma (ensures psum vu vv a b m <= m * ((q - 1) * (q - 1))) (decreases m)
  = if m > 0 then begin
      let j = m - 1 in
      psum_bound vu vv a b j;
      if j * n + a < Seq.length vu && j * n + b < Seq.length vv then
        prod_bound (S16.v (Seq.index vu (j * n + a))) (S16.v (Seq.index vv (j * n + b)))
    end
#pop-options

(** What the accumulators can reach, for [k <= 4]. *)
let psum_small (vu vv: Seq.seq zqt) (a b: nat) (m: nat { m <= 4 })
  : Lemma (psum vu vv a b m <= 4 * ((q - 1) * (q - 1)))
  = psum_bound vu vv a b m;
    Math.lemma_mult_le_right ((q - 1) * (q - 1)) m 4

(** All four sums grow by one term per entry, at the two coefficients of
    pair [i]. *)
let psum_step (k: pos) (vu vv: Seq.seq zqt) (i: nat { i < 128 }) (j: nat { j < k })
  : Lemma (requires Seq.length vu == k * n /\ Seq.length vv == k * n)
          (ensures
             j * n + 2 * i + 1 < k * n /\
             (let a0 = S16.v (Seq.index vu (j * n + 2 * i)) in
              let a1 = S16.v (Seq.index vu (j * n + 2 * i + 1)) in
              let b0 = S16.v (Seq.index vv (j * n + 2 * i)) in
              let b1 = S16.v (Seq.index vv (j * n + 2 * i + 1)) in
              psum vu vv (2 * i) (2 * i) (j + 1) == psum vu vv (2 * i) (2 * i) j + a0 * b0 /\
              psum vu vv (2 * i + 1) (2 * i + 1) (j + 1) ==
                psum vu vv (2 * i + 1) (2 * i + 1) j + a1 * b1 /\
              psum vu vv (2 * i) (2 * i + 1) (j + 1) == psum vu vv (2 * i) (2 * i + 1) j + a0 * b1 /\
              psum vu vv (2 * i + 1) (2 * i) (j + 1) == psum vu vv (2 * i + 1) (2 * i) j + a1 * b0))
  = Math.lemma_mult_le_right n (j + 1) k;
    psum_succ vu vv (2 * i) (2 * i) j;
    psum_succ vu vv (2 * i + 1) (2 * i + 1) j;
    psum_succ vu vv (2 * i) (2 * i + 1) j;
    psum_succ vu vv (2 * i + 1) (2 * i) j

(** Coefficient [t] of entry [j] of a vector, in the flat sequence. *)
let vec_at_index (k: pos) (s: Seq.seq zqt { Seq.length s == k * n })
                 (j: nat { j < k }) (t: nat { t < n })
  : Lemma (j * n + t < k * n /\
           Seq.index (vec_at #k (as_zqs s) j) t == S16.v (Seq.index s (j * n + t)))
  = Math.lemma_mult_le_right n (j + 1) k;
    as_zqs_at k s j;
    as_poly_index (Seq.slice s (j * n) (j * n + n)) t

let add_mods (x y: nat) : Lemma (add (x % q) (y % q) == (x + y) % q)
  = Math.lemma_mod_add_distr (x % q) y q;
    Math.lemma_mod_add_distr y x q

(* The two coefficients of the [i]th base-case product. *)
let multiply_ntts_pair_spec (f g: poly) (i: nat { i < 128 })
  : Lemma (Seq.index (multiply_ntts f g) (2 * i) ==
             add (mul (Seq.index f (2 * i)) (Seq.index g (2 * i)))
                 (mul (mul (Seq.index f (2 * i + 1)) (Seq.index g (2 * i + 1)))
                      (gammas i)) /\
           Seq.index (multiply_ntts f g) (2 * i + 1) ==
             add (mul (Seq.index f (2 * i)) (Seq.index g (2 * i + 1)))
                 (mul (Seq.index f (2 * i + 1)) (Seq.index g (2 * i))))
  = multiply_ntts_index f g (2 * i);
    multiply_ntts_index f g (2 * i + 1);
    Math.cancel_mul_div i 2;
    Math.lemma_div_plus 1 i 2;
    Math.lemma_mod_plus 1 i 2;
    Math.lemma_mod_plus 0 i 2;
    assert ((2 * i) / 2 == i /\ (2 * i) % 2 == 0);
    assert ((2 * i + 1) / 2 == i /\ (2 * i + 1) % 2 == 1)

(** The [i]th pair of the partial dot product is the partial sums, reduced. *)
let rec dot_pair (k: pos) (vu vv: Seq.seq zqt) (i: nat { i < 128 }) (m: nat { m <= k })
  : Lemma (requires Seq.length vu == k * n /\ Seq.length vv == k * n)
          (ensures
             Seq.index (dot_acc #k (as_zqs vu) (as_zqs vv) m) (2 * i) ==
               (psum vu vv (2 * i) (2 * i) m +
                psum vu vv (2 * i + 1) (2 * i + 1) m * gammas i) % q /\
             Seq.index (dot_acc #k (as_zqs vu) (as_zqs vv) m) (2 * i + 1) ==
               (psum vu vv (2 * i) (2 * i + 1) m + psum vu vv (2 * i + 1) (2 * i) m) % q)
          (decreases m)
  = let u = as_zqs vu in
    let v = as_zqs vv in
    if m = 0 then begin
      dot_acc_zero #k u v;
      psum_zero vu vv (2 * i) (2 * i);
      psum_zero vu vv (2 * i + 1) (2 * i + 1);
      psum_zero vu vv (2 * i) (2 * i + 1);
      psum_zero vu vv (2 * i + 1) (2 * i)
    end else begin
      let j = m - 1 in
      dot_pair k vu vv i j;
      dot_acc_succ #k u v j;
      psum_step k vu vv i j;
      vec_at_index k vu j (2 * i);
      vec_at_index k vu j (2 * i + 1);
      vec_at_index k vv j (2 * i);
      vec_at_index k vv j (2 * i + 1);
      let a0 = S16.v (Seq.index vu (j * n + 2 * i)) in
      let a1 = S16.v (Seq.index vu (j * n + 2 * i + 1)) in
      let b0 = S16.v (Seq.index vv (j * n + 2 * i)) in
      let b1 = S16.v (Seq.index vv (j * n + 2 * i + 1)) in
      let g = gammas i in
      multiply_ntts_pair_spec (vec_at #k u j) (vec_at #k v j) i;
      let p00 = psum vu vv (2 * i) (2 * i) j in
      let p11 = psum vu vv (2 * i + 1) (2 * i + 1) j in
      let p01 = psum vu vv (2 * i) (2 * i + 1) j in
      let p10 = psum vu vv (2 * i + 1) (2 * i) j in
      (* the even coefficient *)
      Math.lemma_mod_mul_distr_l (a1 * b1) g q;
      add_mods (a0 * b0) ((a1 * b1) * g);
      add_mods (p00 + p11 * g) (a0 * b0 + (a1 * b1) * g);
      Math.distributivity_add_left p11 (a1 * b1) g;
      assert ((p00 + p11 * g) + (a0 * b0 + (a1 * b1) * g) ==
              (p00 + a0 * b0) + (p11 + a1 * b1) * g);
      (* the odd one *)
      add_mods (a0 * b1) (a1 * b0);
      add_mods (p01 + p10) (a0 * b1 + a1 * b0)
    end

(** What the implementation computes for pair [i]: the [gamma] term needs
    only its sum reduced, not the product. *)
let dot_pair_out (k: pos) (vu vv: Seq.seq zqt) (i: nat { i < 128 /\ 2 * i + 1 < n })
                 (s00 s11 s01 g: nat) (c0 c1: zqt)
  : Lemma (requires Seq.length vu == k * n /\ Seq.length vv == k * n /\
                    s00 == psum vu vv (2 * i) (2 * i) k /\
                    s11 == psum vu vv (2 * i + 1) (2 * i + 1) k /\
                    s01 == psum vu vv (2 * i) (2 * i + 1) k + psum vu vv (2 * i + 1) (2 * i) k /\
                    g == gammas i /\
                    S16.v c0 == (s00 + (s11 % q) * g) % q /\
                    S16.v c1 == s01 % q)
          (ensures S16.v c0 == Seq.index (dot #k (as_zqs vu) (as_zqs vv)) (2 * i) /\
                   S16.v c1 == Seq.index (dot #k (as_zqs vu) (as_zqs vv)) (2 * i + 1))
  = dot_pair k vu vv i k;
    dot_acc_full #k (as_zqs vu) (as_zqs vv);
    Math.lemma_mod_add_distr s00 ((s11 % q) * g) q;
    Math.lemma_mod_mul_distr_l s11 g q;
    Math.lemma_mod_add_distr s00 (s11 * g) q

(** The first [m] coefficients of [w] are those of the dot product.  Opaque,
    as {!Hacl.Impl.MLKEM.NTT.mul_prefix} is, for the same reason. *)
[@@"opaque_to_smt"]
let dot_prefix (k: pos) (w vu vv: Seq.seq zqt) (m: nat) : prop =
  Seq.length vu == k * n /\ Seq.length vv == k * n /\
  (forall (t: nat). t < m ==>
     t < n /\ t < Seq.length w /\
     S16.v (Seq.index w t) == Seq.index (dot #k (as_zqs vu) (as_zqs vv)) t)

let dot_prefix_zero (k: pos) (w vu vv: Seq.seq zqt)
  : Lemma (requires Seq.length vu == k * n /\ Seq.length vv == k * n)
          (ensures dot_prefix k w vu vv 0)
  = reveal_opaque (`%dot_prefix) (dot_prefix k w vu vv 0)

let dot_prefix_full (k: pos) (w vu vv: Seq.seq zqt)
  : Lemma (requires Seq.length w == n /\ dot_prefix k w vu vv n)
          (ensures Seq.length vu == k * n /\ Seq.length vv == k * n /\
                   as_poly w == dot #k (as_zqs vu) (as_zqs vv))
  = reveal_opaque (`%dot_prefix) (dot_prefix k w vu vv n);
    as_poly_intro w (dot #k (as_zqs vu) (as_zqs vv))

let dot_prefix_upd (k: pos) (w vu vv: Seq.seq zqt) (i: nat { i < 128 /\ 2 * i + 2 <= n })
                   (c0 c1: zqt)
  : Lemma (requires Seq.length w == n /\ Seq.length vu == k * n /\ Seq.length vv == k * n /\
                    dot_prefix k w vu vv (2 * i) /\
                    S16.v c0 == Seq.index (dot #k (as_zqs vu) (as_zqs vv)) (2 * i) /\
                    S16.v c1 == Seq.index (dot #k (as_zqs vu) (as_zqs vv)) (2 * i + 1))
          (ensures (let w' = Seq.upd (Seq.upd w (2 * i) c0) (2 * i + 1) c1 in
                    Seq.length w' == n /\ dot_prefix k w' vu vv (2 * i + 2)))
  = reveal_opaque (`%dot_prefix) (dot_prefix k w vu vv (2 * i));
    let w0 = Seq.upd w (2 * i) c0 in
    let w' = Seq.upd w0 (2 * i + 1) c1 in
    Seq.lemma_index_upd2 w0 (2 * i + 1) c1 (2 * i);
    Seq.lemma_index_upd1 w (2 * i) c0;
    Seq.lemma_index_upd1 w0 (2 * i + 1) c1;
    introduce forall (t: nat). t < 2 * i ==>
      S16.v (Seq.index w' t) == Seq.index (dot #k (as_zqs vu) (as_zqs vv)) t
    with introduce _ ==> _
    with (
      Seq.lemma_index_upd2 w0 (2 * i + 1) c1 t;
      Seq.lemma_index_upd2 w (2 * i) c0 t);
    reveal_opaque (`%dot_prefix) (dot_prefix k w' vu vv (2 * i + 2))
(** {2 The matrix-vector product} *)

(** A matrix row is a [k * n]-block of the flat matrix, so the view of the
    sub-array holding it is exactly that row. *)
let as_zqs_row (k: pos) (s: Seq.seq zqt { Seq.length s == k * (k * n) })
               (i: nat { i < k })
  : Lemma (requires Seq.length s == k * k * n)
          (ensures mat_row #k (as_zqs s) i ==
                   as_zqs (Seq.slice s (i * (k * n)) (i * (k * n) + k * n)))
  = as_zqs_flat_at k (k * n) s i

let mat_vec_mul_at (k: pos) (m: pmat k) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (mat_vec_mul #k m v) i == dot (mat_row #k m i) v)
  = vec_at_of_fun k (fun j -> dot (mat_row #k m j) v) i

let mv_entry_step (k: pos) (i: nat { i < k })
                  (vm: Seq.lseq zqt (k * k * n))
                  (vv w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n)
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==>
         S16.v (Seq.index w0 t) ==
           Seq.index (mat_vec_mul #k (as_zqs vm) (as_zqs vv)) t) /\
      as_poly b == dot (mat_row #k (as_zqs vm) i) (as_zqs vv))
    (ensures
      (forall (t: nat). t < (i + 1) * n ==>
         S16.v (Seq.index w1 t) ==
           Seq.index (mat_vec_mul #k (as_zqs vm) (as_zqs vv)) t))
  = mat_vec_mul_at k (as_zqs vm) (as_zqs vv) i;
    entry_step k i w0 w0 w1 b (mat_vec_mul #k (as_zqs vm) (as_zqs vv))

let mv_entry_done (k: pos) (vm: Seq.lseq zqt (k * k * n))
                  (vv w: Seq.lseq zqt (k * n))
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         S16.v (Seq.index w t) ==
           Seq.index (mat_vec_mul #k (as_zqs vm) (as_zqs vv)) t))
    (ensures as_zqs w == mat_vec_mul #k (as_zqs vm) (as_zqs vv))
  = as_zqs_intro w (mat_vec_mul #k (as_zqs vm) (as_zqs vv))
(** {2 Blocks of any size}

    The coders work on blocks of [32 d] bytes rather than [n] coefficients,
    and on three different views of an array, so the step lemma is stated
    once for an arbitrary block size and an arbitrary view. *)

let flat_index_all_m (#a: Type) (k m: pos) (v: Seq.lseq a (k * m)) (i: nat { i < k })
  : Lemma (forall (j: nat). j < m ==> Seq.index v (i * m + j) == Seq.index (flat_at k m v i) j)
  = FStar.Classical.forall_intro (flat_index k m v i)

let flat_step (#a #c: Type) (k m: pos) (view: (a -> GTot c)) (i: nat { i < k })
              (w0 w1: Seq.lseq a (k * m)) (b: Seq.lseq a m) (r: Seq.lseq c (k * m))
  : Lemma (requires
      (forall (t: nat). t < k * m ==>
         Seq.index w1 t == (if i * m <= t && t < i * m + m
                            then Seq.index b (t - i * m) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * m ==> view (Seq.index w0 t) == Seq.index r t) /\
      (forall (j: nat). j < m ==> view (Seq.index b j) == Seq.index (flat_at k m r i) j))
    (ensures forall (t: nat). t < (i + 1) * m ==> view (Seq.index w1 t) == Seq.index r t)
  = flat_index_all_m k m r i

#pop-options
