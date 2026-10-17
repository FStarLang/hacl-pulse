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


(** The pure lemmas behind {!Hacl.Impl.MLDSA.Sample}.

    The samplers' loop invariants say that the first [c] entries of the
    output array are the specification's partial accumulator ({!agree}),
    or, for [SampleInBall], that the array and the counter are the
    specification's state ({!ball_agree}).  Each step of a sampler is one
    of the lemmas here, stated over sequences only, so that the Pulse code
    never has to write a specification fold as an argument. *)
module Hacl.Impl.MLDSA.SampleLemmas

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Sample
open Hacl.Impl.MLDSA.Zq

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module U8 = FStar.UInt8
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module KZ = Spec.MLKEM.Zq
module Classical = FStar.Classical

#push-options "--fuel 0 --ifuel 0 --z3rlimit 50"

(** {2 Partial accumulators} *)

(** The first [c] entries of [v] are [acc], and [c] is its length. *)
let agree (v: Seq.seq zqt) (c: nat) (acc: partial) : prop
  = Seq.length v == n /\ c == Seq.length acc /\
    (forall (k: nat). k < c ==> S32.v (Seq.index v k) == Seq.index acc k)

(** What one conditional write leaves behind: entry [c] set to [x] and the
    count moved on if there was room and the candidate was accepted,
    nothing otherwise. *)
let push_post (v0 v: Seq.seq zqt) (c c': nat) (ok: bool) (x: int) : prop
  = Seq.length v0 == n /\ Seq.length v == n /\ c <= n /\ c' <= n /\
    (forall (k: nat). k < c ==> Seq.index v k == Seq.index v0 k) /\
    ((c < n /\ ok) ==> (c' == c + 1 /\ S32.v (Seq.index v c) == x)) /\
    (~(c < n /\ ok) ==> c' == c)

let agree_empty (v: Seq.seq zqt)
  : Lemma (requires Seq.length v == n) (ensures agree v 0 Seq.empty)
  = ()

let push_agree (v0 v: Seq.seq zqt) (c c': nat) (acc: partial) (ok: bool) (x: zq)
  : Lemma (requires agree v0 c acc /\ push_post v0 v c c' ok x)
          (ensures agree v c' (if Seq.length acc < n && ok then Seq.snoc acc x else acc))
  = if c < n && ok then begin
      let acc' = Seq.snoc acc x in
      let aux (k: nat { k < c' }) : Lemma (S32.v (Seq.index v k) == Seq.index acc' k)
        = if k < c then Seq.lemma_index_app1 acc (Seq.create 1 x) k
          else Seq.lemma_index_app2 acc (Seq.create 1 x) k
      in
      Classical.forall_intro aux
    end

(** {2 Uniform sampling} *)

let ntt_sampled_zero (sd: Seq.seq S8.t) : Lemma (ntt_sampled sd 0 == Seq.empty)
  = Loops.repeati_g_zero (ntt_step sd) Seq.empty

let ntt_push (sd: Seq.seq S8.t) (t: nat) (v0 v: Seq.seq zqt) (c c': nat) (ok: bool) (x: int)
  : Lemma (requires agree v0 c (ntt_sampled sd t) /\ push_post v0 v c c' ok x /\
                    x == ntt_cand sd t /\ (ok <==> x < q))
          (ensures agree v c' (ntt_sampled sd (t + 1)))
  = Loops.unfold_repeati_g t (ntt_step sd) Seq.empty;
    if ok then push_agree v0 v c c' (ntt_sampled sd t) ok x
    else push_agree v0 v c c' (ntt_sampled sd t) ok 0

let ntt_done (sd: Seq.seq S8.t) (t: nat) (v: Seq.seq zqt) (c: nat)
  : Lemma (requires agree v c (ntt_sampled sd t) /\ t <= max_triples /\
                    (c == n \/ t == max_triples))
          (ensures Seq.length v == n /\
                   (c == n ==> as_poly v == rej_ntt_poly sd) /\
                   (c < n ==> rej_ntt_poly sd == poly_zero))
  = if c = n then begin
      ntt_sampled_stable sd t max_triples;
      as_poly_intro v (ntt_sampled sd t)
    end

(** {2 Bounded sampling} *)

let bounded_sampled_zero (eta: pos) (sd: Seq.seq S8.t)
  : Lemma (bounded_sampled eta sd 0 == Seq.empty)
  = Loops.repeati_g_zero (bounded_step eta sd) Seq.empty

let half_push (eta: pos) (acc: partial) (z: nat) (v0 v: Seq.seq zqt) (c c': nat)
              (ok: bool) (x: int)
  : Lemma (requires agree v0 c acc /\ push_post v0 v c c' ok x /\
                    (ok <==> coeff_ok eta z) /\ x == coeff_of eta z)
          (ensures agree v c' (push_half eta acc z))
  = push_agree v0 v c c' acc ok (coeff_of eta z)

let bounded_succ (eta: pos) (sd: Seq.seq S8.t) (t: nat)
  : Lemma (bounded_sampled eta sd (t + 1) ==
           push_half eta (push_half eta (bounded_sampled eta sd t)
                                        (S8.v (shake256_byte sd t) % 16))
                         (S8.v (shake256_byte sd t) / 16))
  = Loops.unfold_repeati_g t (bounded_step eta sd) Seq.empty

let bounded_done (eta: pos) (sd: Seq.seq S8.t) (t: nat) (v: Seq.seq zqt) (c: nat)
  : Lemma (requires agree v c (bounded_sampled eta sd t) /\ t <= max_bounded /\
                    (c == n \/ t == max_bounded))
          (ensures Seq.length v == n /\
                   (c == n ==> as_poly v == rej_bounded_poly eta sd) /\
                   (c < n ==> rej_bounded_poly eta sd == poly_zero))
  = if c = n then begin
      bounded_sampled_stable eta sd t max_bounded;
      as_poly_intro v (bounded_sampled eta sd t)
    end

(** [CoeffFromHalfByte]'s value, as the implementation computes it: a
    reduction mod 5 by two conditional subtractions, then a subtraction in
    [Z_q]. *)
let mod5 (z: nat { z < 16 })
  : Lemma (let m1 = if z >= 10 then z - 10 else z in
           let m2 = if m1 >= 5 then m1 - 5 else m1 in
           m2 == z % 5)
  = let m1 = if z >= 10 then z - 10 else z in
    let m2 = if m1 >= 5 then m1 - 5 else m1 in
    if z >= 10 then Math.lemma_mod_plus m1 2 5
    else if z >= 5 then Math.lemma_mod_plus m2 1 5
    else Math.small_mod z 5;
    if m1 >= 5 then Math.lemma_mod_plus m2 1 5 else Math.small_mod m1 5;
    Math.small_mod m2 5

let sub_of_int (a: zq) (b: zq)
  : Lemma (sub a b == of_int (a - b))
  = Math.lemma_mod_plus (a - b) 1 q

(** {2 The challenge} *)

let ball_ok (tau: pos { tau <= 60 }) (st: ball_state) : prop
  = n - tau <= st.ball_i /\ st.ball_i <= n

let rec ball_sampled_ok (tau: pos { tau <= 60 }) (sd: Seq.seq S8.t) (m: nat)
  : Lemma (ensures ball_ok tau (ball_sampled tau sd m)) (decreases m)
  = if m = 0 then Loops.repeati_g_zero (ball_step tau sd) (ball_init tau)
    else begin
      ball_sampled_ok tau sd (m - 1);
      Loops.unfold_repeati_g (m - 1) (ball_step tau sd) (ball_init tau)
    end

(** The array is the state's polynomial and the counter its index. *)
let ball_agree (v: Seq.seq zqt) (i: nat) (st: ball_state) : prop
  = Seq.length v == n /\ i == st.ball_i /\ as_poly v == st.ball_c

let as_poly_upd (s: Seq.seq zqt { Seq.length s == n }) (i: nat { i < n }) (x: zqt)
  : Lemma (as_poly (Seq.upd s i x) == Seq.upd (as_poly s) i (S32.v x))
  = Seq.lemma_eq_intro (as_poly (Seq.upd s i x)) (Seq.upd (as_poly s) i (S32.v x))

let ball_start (tau: pos { tau <= 60 }) (sd: Seq.seq S8.t) (v: Seq.seq zqt)
  : Lemma (requires Seq.length v == n /\ as_poly v == poly_zero)
          (ensures ball_agree v (n - tau) (ball_sampled tau sd 0))
  = Loops.repeati_g_zero (ball_step tau sd) (ball_init tau)

let ball_push (tau: pos { tau <= 60 }) (sd: Seq.seq S8.t) (t: nat)
              (v0 v: Seq.seq zqt) (i i': nat) (j: nat) (sv: zqt)
  : Lemma (requires ball_agree v0 i (ball_sampled tau sd t) /\
                    ball_ok tau (ball_sampled tau sd t) /\
                    j == S8.v (shake256_byte sd (8 + t)) /\
                    ((i < n /\ j <= i) ==>
                       (i' == i + 1 /\
                        S32.v sv == (if sign_bit sd (i + tau - n) then q - 1 else 1) /\
                        v == Seq.upd (Seq.upd v0 i (Seq.index v0 j)) j sv)) /\
                    (~(i < n /\ j <= i) ==> (i' == i /\ v == v0)))
          (ensures ball_agree v i' (ball_sampled tau sd (t + 1)) /\
                   ball_ok tau (ball_sampled tau sd (t + 1)))
  = ball_sampled_ok tau sd (t + 1);
    Loops.unfold_repeati_g t (ball_step tau sd) (ball_init tau);
    if i < n && j <= i then begin
      let v1 = Seq.upd v0 i (Seq.index v0 j) in
      as_poly_upd v0 i (Seq.index v0 j);
      as_poly_upd v1 j sv
    end

let ball_done (tau: pos { tau <= 60 }) (sd: Seq.seq S8.t) (t: nat) (v: Seq.seq zqt) (i: nat)
  : Lemma (requires ball_agree v i (ball_sampled tau sd t) /\ t <= max_ball /\
                    (i == n \/ t == max_ball))
          (ensures Seq.length v == n /\
                   (i == n ==> as_poly v == (let st = ball_sampled tau sd max_ball in
                                            if st.ball_i = n then st.ball_c else poly_zero)) /\
                   (i <> n ==> (let st = ball_sampled tau sd max_ball in
                                if st.ball_i = n then st.ball_c else poly_zero) == poly_zero))
  = if i = n then ball_sampled_stable tau sd t max_ball

(** {2 Seeds} *)

let seed_2_eq (rho: Seq.seq S8.t) (a: nat { a < 256 }) (b: nat { b < 256 }) (v: Seq.seq S8.t)
  : Lemma (requires Seq.length v == Seq.length rho + 2 /\
                    (forall (t: nat). t < Seq.length rho ==> Seq.index v t == Seq.index rho t) /\
                    S8.v (Seq.index v (Seq.length rho)) == a /\
                    S8.v (Seq.index v (Seq.length rho + 1)) == b)
          (ensures v == seed_2 rho a b)
  = let s = seed_2 rho a b in
    let aux (t: nat { t < Seq.length v }) : Lemma (Seq.index v t == Seq.index s t)
      = if t < Seq.length rho then ()
        else S8.v_extensional (Seq.index v t) (Seq.index s t)
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro v s

let seed_16_eq (rho: Seq.seq S8.t) (x: nat { x < 256 }) (v: Seq.seq S8.t)
  : Lemma (requires Seq.length v == Seq.length rho + 2 /\
                    (forall (t: nat). t < Seq.length rho ==> Seq.index v t == Seq.index rho t) /\
                    S8.v (Seq.index v (Seq.length rho)) == x /\
                    S8.v (Seq.index v (Seq.length rho + 1)) == 0)
          (ensures (assert_norm (pow2 16 == 65536); v == seed_16 rho x))
  = assert_norm (pow2 16 == 65536);
    let s = seed_16 rho x in
    Math.small_mod x 256;
    Math.small_div x 256;
    let aux (t: nat { t < Seq.length v }) : Lemma (Seq.index v t == Seq.index s t)
      = if t < Seq.length rho then ()
        else S8.v_extensional (Seq.index v t) (Seq.index s t)
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro v s

(** {2 Expansion} *)

let flat_index (#a: Type) (k: pos) (m: pos) (v: Seq.lseq a (k * m))
               (i: nat { i < k }) (j: nat { j < m })
  : Lemma (Seq.index v (i * m + j) == Seq.index (KZ.flat_at k m v i) j)
  = Math.lemma_mult_le_right m (i + 1) k;
    Seq.lemma_index_slice v (i * m) (i * m + m) j

(** Writing block [i] of a flat sequence extends the prefix that agrees
    with the target by one block. *)
let flat_step (k: pos) (i: nat { i < k })
              (w0 w1: Seq.lseq zqt (k * n)) (b: Seq.lseq zqt n) (r: Seq.lseq zq (k * n))
  : Lemma (requires
      (forall (t: nat). t < k * n ==>
         Seq.index w1 t == (if i * n <= t && t < i * n + n
                            then Seq.index b (t - i * n) else Seq.index w0 t)) /\
      (forall (t: nat). t < i * n ==> S32.v (Seq.index w0 t) == Seq.index r t) /\
      as_poly b == KZ.flat_at k n r i)
    (ensures forall (t: nat). t < (i + 1) * n ==> S32.v (Seq.index w1 t) == Seq.index r t)
  = Math.lemma_mult_le_right n (i + 1) k;
    let aux (t: nat { t < (i + 1) * n }) : Lemma (S32.v (Seq.index w1 t) == Seq.index r t)
      = if t < i * n then ()
        else begin
          flat_index k n r i (t - i * n);
          as_poly_index b (t - i * n)
        end
    in
    Classical.forall_intro aux

let flat_done (k: pos) (w: Seq.lseq zqt (k * n)) (r: Seq.lseq zq (k * n))
  : Lemma (requires forall (t: nat). t < k * n ==> S32.v (Seq.index w t) == Seq.index r t)
          (ensures as_zqs w == r)
  = as_zqs_intro w r

let expand_a_at (p: params) (rho: Seq.lseq S8.t 32) (t: nat { t < p.k * p.l })
  : Lemma (KZ.div_lt t p.k p.l;
           KZ.flat_at (p.k * p.l) n (expand_a p rho) t ==
             rej_ntt_poly (seed_2 rho (t % p.l) (t / p.l)))
  = KZ.flat_at_of_fun_g (p.k * p.l) n (fun t ->
      KZ.div_lt t p.k p.l;
      rej_ntt_poly (seed_2 rho (t % p.l) (t / p.l))) t

let expand_s1_at (p: params) (rho': Seq.lseq S8.t 64) (r: nat { r < p.l })
  : Lemma (assert_norm (pow2 16 == 65536);
           KZ.flat_at p.l n (expand_s1 p rho') r == rej_bounded_poly p.eta (seed_16 rho' r))
  = assert_norm (pow2 16 == 65536);
    vec_at_of_fun_g p.l (fun r -> rej_bounded_poly p.eta (seed_16 rho' r)) r

let expand_s2_at (p: params) (rho': Seq.lseq S8.t 64) (r: nat { r < p.k })
  : Lemma (assert_norm (pow2 16 == 65536);
           KZ.flat_at p.k n (expand_s2 p rho') r ==
             rej_bounded_poly p.eta (seed_16 rho' (r + p.l)))
  = assert_norm (pow2 16 == 65536);
    vec_at_of_fun_g p.k (fun r -> rej_bounded_poly p.eta (seed_16 rho' (r + p.l))) r


(** The first [m] entries of [w] are those of [r]; opaque so that the
    loop invariants of the expansions stay cheap. *)
[@@"opaque_to_smt"]
let prefix_eq (w: Seq.seq zqt) (r: Seq.seq zq) (m: nat) : prop
  = forall (t: nat). t < m /\ t < Seq.length w /\ t < Seq.length r ==>
      S32.v (Seq.index w t) == Seq.index r t

let prefix_zero (w: Seq.seq zqt) (r: Seq.seq zq) : Lemma (prefix_eq w r 0)
  = reveal_opaque (`%prefix_eq) (prefix_eq w r 0)

let prefix_done (k: pos) (w: Seq.seq zqt) (r: Seq.lseq zq (k * n))
  : Lemma (requires Seq.length w == k * n /\ prefix_eq w r (k * n))
          (ensures as_zqs w == r)
  = reveal_opaque (`%prefix_eq) (prefix_eq w r (k * n));
    as_zqs_intro w r

(** The [SampleInBall] block arithmetic. *)
let ball_idx (j: nat { 1 <= j /\ j <= 8 })
  : Lemma (8 <= j * 136 /\ j * 136 - 8 <= max_ball /\
           (j == 8 ==> j * 136 - 8 == max_ball) /\
           j * 136 + 136 - 8 == (j + 1) * 136 - 8)
  = ()

(** The index arithmetic of one [ExpandA] iteration. *)
let expand_a_bounds (k: pos { k <= 8 }) (l: pos { l <= 7 }) (t: nat { t < k * l })
  : Lemma (k * l <= 56 /\ t / l < k /\ t / l < 8 /\ t % l < 7 /\
           t * n + n == (t + 1) * n /\ (t + 1) * n <= k * l * n /\ k * l * n <= 14336)
  = Math.lemma_mult_le_right l k 8;
    Math.lemma_mult_le_left 8 l 7;
    KZ.div_lt t k l;
    Math.distributivity_add_left t 1 n;
    Math.lemma_mult_le_right n (t + 1) (k * l);
    Math.lemma_mult_le_right n (k * l) 56

(** One entry of [A-hat]: the seed bytes, the sampled block and the
    write-back give one more block of the target. *)
let expand_a_step (p: params) (rho: Seq.lseq S8.t 32) (t: nat { t < p.k * p.l })
                  (w0 w1: Seq.seq zqt) (b: Seq.seq zqt) (sd: Seq.seq S8.t)
  : Lemma (requires
      Seq.length w0 == p.k * p.l * n /\ Seq.length w1 == p.k * p.l * n /\
      Seq.length b == n /\
      (forall (i: nat). i < p.k * p.l * n ==>
         Seq.index w1 i == (if t * n <= i && i < t * n + n
                            then Seq.index b (i - t * n) else Seq.index w0 i)) /\
      prefix_eq w0 (expand_a p rho) (t * n) /\
      Seq.length sd == 34 /\
      (forall (i: nat). i < 32 ==> Seq.index sd i == Seq.index rho i) /\
      S8.v (Seq.index sd 32) == t % p.l /\
      S8.v (Seq.index sd 33) == t / p.l /\
      as_poly b == rej_ntt_poly sd)
    (ensures prefix_eq w1 (expand_a p rho) ((t + 1) * n))
  = reveal_opaque (`%prefix_eq) (prefix_eq w0 (expand_a p rho) (t * n));
    reveal_opaque (`%prefix_eq) (prefix_eq w1 (expand_a p rho) ((t + 1) * n));
    KZ.div_lt t p.k p.l;
    seed_2_eq rho (t % p.l) (t / p.l) sd;
    expand_a_at p rho t;
    flat_step (p.k * p.l) t w0 w1 b (expand_a p rho)

(** [s1] and [s2] as one family: [s2]'s nonces start at [l]. *)
let s_count (p: params) (second: bool) : pos = if second then p.k else p.l

let s_off (p: params) (second: bool) : nat = if second then p.l else 0

let s_target (p: params) (rho': Seq.lseq S8.t 64) (second: bool)
  : GTot (Seq.lseq zq (s_count p second * n))
  = if second then expand_s2 p rho' else expand_s1 p rho'

let expand_s_step (p: params) (rho': Seq.lseq S8.t 64) (second: bool)
                  (t: nat { t < s_count p second })
                  (w0 w1: Seq.seq zqt) (b: Seq.seq zqt) (sd: Seq.seq S8.t)
  : Lemma (requires
      Seq.length w0 == s_count p second * n /\ Seq.length w1 == s_count p second * n /\
      Seq.length b == n /\
      (forall (i: nat). i < s_count p second * n ==>
         Seq.index w1 i == (if t * n <= i && i < t * n + n
                            then Seq.index b (i - t * n) else Seq.index w0 i)) /\
      prefix_eq w0 (s_target p rho' second) (t * n) /\
      Seq.length sd == 66 /\
      (forall (i: nat). i < 64 ==> Seq.index sd i == Seq.index rho' i) /\
      S8.v (Seq.index sd 64) == t + s_off p second /\
      S8.v (Seq.index sd 65) == 0 /\
      as_poly b == rej_bounded_poly p.eta sd)
    (ensures prefix_eq w1 (s_target p rho' second) ((t + 1) * n))
  = reveal_opaque (`%prefix_eq) (prefix_eq w0 (s_target p rho' second) (t * n));
    reveal_opaque (`%prefix_eq) (prefix_eq w1 (s_target p rho' second) ((t + 1) * n));
    seed_16_eq rho' (t + s_off p second) sd;
    if second then expand_s2_at p rho' t else expand_s1_at p rho' t;
    flat_step (s_count p second) t w0 w1 b (s_target p rho' second)

#pop-options
