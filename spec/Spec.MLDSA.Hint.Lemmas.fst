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

(** The hint encoding round-trips: unpacking a packed hint with at most
    [omega] ones gives the hint back.

    Both directions are folds, so the proof is two loop invariants over
    the prefix count {!cnt}: the packer writes the position of the one at
    [t] into byte [cnt h t] and the running count [cnt h ((i + 1) n)] at
    the end of polynomial [i]; the scatter, reading polynomial [i]'s
    bytes [cnt h (i n)] to [cnt h ((i + 1) n)], marks exactly the ones of
    polynomial [i] whose count is below the byte it has reached. *)
module Spec.MLDSA.Hint.Lemmas

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Rounding
open Spec.MLDSA.Encode

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Loops = Hacl.Spec.Loops
module Classical = FStar.Classical
module KZ = Spec.MLKEM.Zq
module Math = FStar.Math.Lemmas

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"

(** {2 Prefix counts} *)

let ind (b: bool) : nat = if b then 1 else 0

(** The number of ones among the first [t] entries. *)
let rec cnt (s: Seq.seq bool) (t: nat { t <= Seq.length s }) : Tot nat (decreases t)
  = if t = 0 then 0 else cnt s (t - 1) + ind (Seq.index s (t - 1))

#push-options "--fuel 2"
let rec cnt_tail (s: Seq.seq bool) (m: pos { m <= Seq.length s })
  : Lemma (ensures cnt s m == ind (Seq.index s 0) + cnt (Seq.tail s) (m - 1)) (decreases m)
  = if m = 1 then ()
    else begin
      cnt_tail s (m - 1);
      assert (Seq.index (Seq.tail s) (m - 2) == Seq.index s (m - 1))
    end
#pop-options

let rec cnt_count (s: Seq.seq bool)
  : Lemma (ensures cnt s (Seq.length s) == count_true s) (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      cnt_tail s (Seq.length s);
      cnt_count (Seq.tail s)
    end

let rec cnt_mono (s: Seq.seq bool) (a: nat) (b: nat { a <= b /\ b <= Seq.length s })
  : Lemma (ensures cnt s a <= cnt s b) (decreases b - a)
  = if a = b then () else cnt_mono s a (b - 1)

(** A one strictly raises the count. *)
let cnt_strict (s: Seq.seq bool) (b: nat { b <= Seq.length s }) (a: nat)
  : Lemma (requires a < b /\ Seq.index s a) (ensures cnt s a < cnt s b)
  = cnt_mono s (a + 1) b

let cnt_inj (s: Seq.seq bool) (a: nat { a < Seq.length s }) (b: nat { b < Seq.length s })
  : Lemma (requires Seq.index s a /\ Seq.index s b /\ cnt s a == cnt s b) (ensures a == b)
  = if a < b then cnt_strict s b a
    else if b < a then cnt_strict s a b

(** Every count between [cnt s a] and [cnt s b] is the count at some one
    in [[a, b)]. *)
let rec ivt (s: Seq.seq bool) (a: nat) (b: nat { a <= b /\ b <= Seq.length s }) (e: nat)
  : Pure nat (requires cnt s a <= e /\ e < cnt s b)
             (ensures fun t -> a <= t /\ t < b /\ Seq.index s t /\ cnt s t == e)
             (decreases b)
  = if e < cnt s (b - 1) then ivt s a (b - 1) e else b - 1

(** {2 The packer} *)

let pack_inv (p: params) (h: Seq.lseq bool (p.k * n)) (t: nat { t <= p.k * n })
             (st: hint_state p) : prop
  = let y, idx = st in
    idx == cnt h t /\
    (forall (t': nat). t' < t /\ Seq.index h t' ==>
       cnt h t' < p.omega /\ U8.v (Seq.index y (cnt h t')) == t' % n) /\
    (forall (e: nat). idx <= e /\ e < p.omega ==> U8.v (Seq.index y e) == 0) /\
    (forall (i: nat). i < p.k /\ (i + 1) * n <= t ==>
       U8.v (Seq.index y (p.omega + i)) == cnt h ((i + 1) * n))

let cnt_strict_all (s: Seq.seq bool) (b: nat { b <= Seq.length s })
  : Lemma (forall (a: nat). a < b /\ Seq.index s a ==> cnt s a < cnt s b)
  = introduce forall (a: nat). a < b /\ Seq.index s a ==> cnt s a < cnt s b
    with introduce _ ==> _ with cnt_strict s b a

(** The first half of a step: record the position of a one. *)
let pack_mark (p: params) (h: Seq.lseq bool (p.k * n)) (t: nat { t < p.k * n })
              (y: Seq.lseq U8.t (hint_len p)) (idx: nat)
  : Lemma (requires cnt h (p.k * n) <= p.omega /\ pack_inv p h t (y, idx))
          (ensures (let y1, idx1 =
                      if Seq.index h t && idx < p.omega
                      then Seq.upd y idx (U8.uint_to_t (t % n)), idx + 1
                      else y, idx in
                    idx1 == cnt h (t + 1) /\ idx1 <= p.omega /\
                    (forall (t': nat). t' < t + 1 /\ Seq.index h t' ==>
                       cnt h t' < p.omega /\ U8.v (Seq.index y1 (cnt h t')) == t' % n) /\
                    (forall (e: nat). idx1 <= e /\ e < p.omega ==> U8.v (Seq.index y1 e) == 0) /\
                    (forall (i: nat). i < p.k /\ (i + 1) * n <= t ==>
                       U8.v (Seq.index y1 (p.omega + i)) == cnt h ((i + 1) * n))))
  = cnt_mono h (t + 1) (p.k * n);
    cnt_strict_all h t;
    assert_norm (pow2 8 == 256)

(** The second half: at the end of a polynomial, record the count. *)
let pack_count (p: params) (h: Seq.lseq bool (p.k * n)) (t: nat { t < p.k * n })
               (y1: Seq.lseq U8.t (hint_len p)) (idx1: nat)
  : Lemma (requires idx1 == cnt h (t + 1) /\ idx1 <= p.omega /\
                    (forall (t': nat). t' < t + 1 /\ Seq.index h t' ==>
                       cnt h t' < p.omega /\ U8.v (Seq.index y1 (cnt h t')) == t' % n) /\
                    (forall (e: nat). idx1 <= e /\ e < p.omega ==> U8.v (Seq.index y1 e) == 0) /\
                    (forall (i: nat). i < p.k /\ (i + 1) * n <= t ==>
                       U8.v (Seq.index y1 (p.omega + i)) == cnt h ((i + 1) * n)))
          (ensures (let i = t / n in
                    let j = t % n in
                    KZ.div_lt t p.k n;
                    pack_inv p h (t + 1)
                      (if j = n - 1 && idx1 < 256
                       then Seq.upd y1 (p.omega + i) (U8.uint_to_t idx1), idx1
                       else y1, idx1)))
  = KZ.div_lt t p.k n;
    assert_norm (pow2 8 == 256)

let pack_step (p: params) (h: Seq.lseq bool (p.k * n)) (t: nat { t < p.k * n })
              (st: hint_state p)
  : Lemma (requires cnt h (p.k * n) <= p.omega /\ pack_inv p h t st)
          (ensures pack_inv p h (t + 1) (hint_pack_step p h t st))
  = let y, idx = st in
    pack_mark p h t y idx;
    let y1, idx1 =
      if Seq.index h t && idx < p.omega
      then Seq.upd y idx (U8.uint_to_t (t % n)), idx + 1
      else y, idx in
    pack_count p h t y1 idx1

let rec pack_loop (p: params) (h: Seq.lseq bool (p.k * n)) (t: nat { t <= p.k * n })
  : Lemma (requires cnt h (p.k * n) <= p.omega)
          (ensures pack_inv p h t
                     (Loops.repeati #(hint_state p) t (hint_pack_step p h) (Seq.create (hint_len p) 0uy, 0)))
          (decreases t)
  = let init : hint_state p = (Seq.create (hint_len p) 0uy, 0) in
    if t = 0 then Loops.repeati_zero (hint_pack_step p h) init
    else begin
      pack_loop p h (t - 1);
      Loops.unfold_repeati (t - 1) (hint_pack_step p h) init;
      pack_step p h (t - 1) (Loops.repeati (t - 1) (hint_pack_step p h) init)
    end

let lo_hi (p: params) (h: Seq.lseq bool (p.k * n)) (y: Seq.lseq S8.t (hint_len p))
          (i: nat { i < p.k })
  : Lemma (requires forall (j: nat). j < p.k ==>
                      S8.v (Seq.index y (p.omega + j)) == cnt h ((j + 1) * n))
          (ensures hint_lo p y i == cnt h (i * n) /\ hint_hi p y i == cnt h ((i + 1) * n))
  = if i > 0 then begin
      let i' : nat = i - 1 in
      assert (S8.v (Seq.index y (p.omega + i')) == cnt h ((i' + 1) * n))
    end

let pack_bytes (p: params) (h: Seq.lseq bool (p.k * n))
  : Lemma (requires cnt h (p.k * n) <= p.omega)
          (ensures (let y = hint_pack p h in
                    (forall (t: nat). t < p.k * n /\ Seq.index h t ==>
                       cnt h t < p.omega /\ S8.v (Seq.index y (cnt h t)) == t % n) /\
                    (forall (j: nat). j < p.k ==>
                       S8.v (Seq.index y (p.omega + j)) == cnt h ((j + 1) * n))))
  = pack_loop p h (p.k * n);
    let init : hint_state p = (Seq.create (hint_len p) 0uy, 0) in
    let st : hint_state p = Loops.repeati #(hint_state p) (p.k * n) (hint_pack_step p h) init in
    let yu : Seq.lseq U8.t (hint_len p) = fst st in
    let y = hint_pack p h in
    assert (forall (e: nat). e < hint_len p ==> S8.v (Seq.index y e) == U8.v (Seq.index yu e));
    introduce forall (j: nat). j < p.k ==> (j + 1) * n <= p.k * n
    with introduce _ ==> _ with Math.lemma_mult_le_right n (j + 1) p.k

(** What the packed bytes say, for a hint with at most [omega] ones. *)
let pack_facts (p: params) (h: Seq.lseq bool (p.k * n))
  : Lemma (requires cnt h (p.k * n) <= p.omega)
          (ensures (let y = hint_pack p h in
                    (forall (t: nat). t < p.k * n /\ Seq.index h t ==>
                       cnt h t < p.omega /\ S8.v (Seq.index y (cnt h t)) == t % n) /\
                    (forall (i: nat). i < p.k ==>
                       hint_lo p y i == cnt h (i * n) /\ hint_hi p y i == cnt h ((i + 1) * n))))
  = pack_bytes p h;
    introduce forall (i: nat). i < p.k ==>
                hint_lo p (hint_pack p h) i == cnt h (i * n) /\
                hint_hi p (hint_pack p h) i == cnt h ((i + 1) * n)
    with introduce _ ==> _ with lo_hi p h (hint_pack p h) i

(** {2 The scatter} *)

(** Inside polynomial [i], after the position bytes below [e]. *)
let sc_inv (p: params) (h: Seq.lseq bool (p.k * n)) (i: nat) (e: nat)
           (h': Seq.lseq bool (p.k * n)) : prop
  = forall (t: nat). t < p.k * n ==>
      Seq.index h' t ==
        (Seq.index h t && (t < i * n || (i * n <= t && t < (i + 1) * n && cnt h t < e)))

let cnt_bounds_all (s: Seq.seq bool) (a: nat) (b: nat { a <= b /\ b <= Seq.length s })
  : Lemma (forall (t: nat). a <= t /\ t < b /\ Seq.index s t ==>
             cnt s a <= cnt s t /\ cnt s t < cnt s b)
  = introduce forall (t: nat). a <= t /\ t < b /\ Seq.index s t ==>
                cnt s a <= cnt s t /\ cnt s t < cnt s b
    with introduce _ ==> _ with (cnt_mono s a t; cnt_strict s b t)

let cnt_inj_all (s: Seq.seq bool) (a: nat { a < Seq.length s })
  : Lemma (requires Seq.index s a)
          (ensures forall (t: nat). t < Seq.length s /\ Seq.index s t /\ cnt s t == cnt s a ==> t == a)
  = introduce forall (t: nat). t < Seq.length s /\ Seq.index s t /\ cnt s t == cnt s a ==> t == a
    with introduce _ ==> _ with cnt_inj s a t

let in_block (i: nat) (t: nat)
  : Lemma (requires i * n <= t /\ t < (i + 1) * n) (ensures i * n + t % n == t)
  = let r : nat = t - i * n in
    Math.lemma_mod_plus r i n;
    Math.small_mod r n

let scatter_step (p: params) (h: Seq.lseq bool (p.k * n)) (i: nat { i < p.k })
                 (e: nat { e < p.omega }) (h': Seq.lseq bool (p.k * n))
  : Lemma (requires cnt h (p.k * n) <= p.omega /\ sc_inv p h i e h')
          (ensures sc_inv p h i (e + 1) (hint_scatter_step p (hint_pack p h) i e h'))
  = let y = hint_pack p h in
    pack_facts p h;
    Math.lemma_mult_le_right n (i + 1) p.k;
    cnt_bounds_all h (i * n) ((i + 1) * n);
    if cnt h (i * n) <= e && e < cnt h ((i + 1) * n) then begin
      let t0 = ivt h (i * n) ((i + 1) * n) e in
      cnt_inj_all h t0;
      assert (S8.v (Seq.index y e) == t0 % n);
      in_block i t0;
      assert (i * n + S8.v (Seq.index y e) == t0)
    end

let rec scatter_inner (p: params) (h: Seq.lseq bool (p.k * n)) (i: nat { i < p.k })
                      (e: nat { e <= p.omega }) (h': Seq.lseq bool (p.k * n))
  : Lemma (requires cnt h (p.k * n) <= p.omega /\ sc_inv p h i 0 h')
          (ensures sc_inv p h i e (Loops.repeati_g e (hint_scatter_step p (hint_pack p h) i) h'))
          (decreases e)
  = let f = hint_scatter_step p (hint_pack p h) i in
    if e = 0 then Loops.repeati_g_zero f h'
    else begin
      scatter_inner p h i (e - 1) h';
      Loops.unfold_repeati_g (e - 1) f h';
      scatter_step p h i (e - 1) (Loops.repeati_g (e - 1) f h')
    end

let out_inv (p: params) (h: Seq.lseq bool (p.k * n)) (i: nat) (h': Seq.lseq bool (p.k * n)) : prop
  = forall (t: nat). t < p.k * n ==> Seq.index h' t == (Seq.index h t && t < i * n)

let scatter_poly (p: params) (h: Seq.lseq bool (p.k * n)) (i: nat { i < p.k })
                 (h': Seq.lseq bool (p.k * n))
  : Lemma (requires cnt h (p.k * n) <= p.omega /\ out_inv p h i h')
          (ensures out_inv p h (i + 1) (hint_scatter_poly p (hint_pack p h) i h'))
  = scatter_inner p h i p.omega h';
    cnt_bounds_all h 0 (p.k * n)

let rec scatter_outer (p: params) (h: Seq.lseq bool (p.k * n)) (i: nat { i <= p.k })
  : Lemma (requires cnt h (p.k * n) <= p.omega)
          (ensures out_inv p h i
                     (Loops.repeati_g i (hint_scatter_poly p (hint_pack p h))
                                        (Seq.create (p.k * n) false)))
          (decreases i)
  = let f = hint_scatter_poly p (hint_pack p h) in
    let init = Seq.create (p.k * n) false in
    if i = 0 then Loops.repeati_g_zero f init
    else begin
      scatter_outer p h (i - 1);
      Loops.unfold_repeati_g (i - 1) f init;
      scatter_poly p h (i - 1) (Loops.repeati_g (i - 1) f init)
    end

(** {2 The round trip} *)

let hint_scatter_pack (p: params) (h: Seq.lseq bool (p.k * n))
  : Lemma (requires count_true h <= p.omega)
          (ensures hint_scatter p (hint_pack p h) == h)
  = cnt_count h;
    scatter_outer p h p.k;
    Seq.lemma_eq_intro (hint_scatter p (hint_pack p h)) h

let hint_unpack_pack (p: params) (h: Seq.lseq bool (p.k * n))
  : Lemma (requires count_true h <= p.omega)
          (ensures hint_unpack p (hint_pack p h) == Some h)
  = hint_scatter_pack p h

#pop-options
