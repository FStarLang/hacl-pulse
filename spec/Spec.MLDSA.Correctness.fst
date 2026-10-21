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

(** Correctness of ML-DSA: a signature produced from a key pair verifies
    under the matching public key.

    The proof follows the standard one (FIPS 204, section 3.6 / the
    Dilithium paper).  Verification recomputes
    [w' = A z - c t1 2^d = w - c s2 + c t0] (all of it in the NTT domain,
    using {!Spec.MLDSA.NTT.Lemmas}); the hint recovers the high part of
    [w - c s2] from [w'] ({!Spec.MLDSA.Rounding.Lemmas.use_hint_make_hint});
    and that is the high part of [w] because [c s2] is at most [beta] and
    the signer checked that the low part of [w - c s2] is below
    [gamma2 - beta] ({!Spec.MLDSA.Rounding.Lemmas.high_bits_stable}).  The
    encodings round-trip, so the verifier sees what the signer packed. *)
module Spec.MLDSA.Correctness

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.NTT
open Spec.MLDSA.Ring
open Spec.MLDSA.Rounding
open Spec.MLDSA.Encode
open Spec.MLDSA.Sample
open Spec.MLDSA

module Seq = FStar.Seq
module KZ = Spec.MLKEM.Zq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module NL = Spec.MLDSA.NTT.Lemmas
module EL = Spec.MLDSA.Encode.Lemmas
module SL = Spec.MLDSA.Sample.Lemmas
module RL = Spec.MLDSA.Rounding.Lemmas
module S8 = Hacl.Secret.UInt8

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"

(** {2 Vectors, a block at a time} *)

let poly_ext (f g: poly)
  : Lemma (requires forall (i: nat). i < n ==> Seq.index f i == Seq.index g i) (ensures f == g)
  = Seq.lemma_eq_intro f g

let vec_ext (#k: pos) (u v: pvec k)
  : Lemma (requires forall (i: nat { i < k }). vec_at u i == vec_at v i) (ensures u == v)
  = EL.flat_ext k n u (fun i -> vec_at u i);
    EL.flat_ext k n v (fun i -> vec_at u i)

let vec_at_add (#k: pos) (u v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_add u v) i == poly_add (vec_at u i) (vec_at v i))
  = introduce forall (j: nat). j < n ==>
      Seq.index (vec_at (vec_add u v) i) j == Seq.index (poly_add (vec_at u i) (vec_at v i)) j
    with introduce _ ==> _
    with begin
      EL.flat_at_index k n (vec_add u v) i j;
      EL.flat_at_index k n u i j;
      EL.flat_at_index k n v i j
    end;
    poly_ext (vec_at (vec_add u v) i) (poly_add (vec_at u i) (vec_at v i))

let vec_at_sub (#k: pos) (u v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_sub u v) i == poly_sub (vec_at u i) (vec_at v i))
  = introduce forall (j: nat). j < n ==>
      Seq.index (vec_at (vec_sub u v) i) j == Seq.index (poly_sub (vec_at u i) (vec_at v i)) j
    with introduce _ ==> _
    with begin
      EL.flat_at_index k n (vec_sub u v) i j;
      EL.flat_at_index k n u i j;
      EL.flat_at_index k n v i j
    end;
    poly_ext (vec_at (vec_sub u v) i) (poly_sub (vec_at u i) (vec_at v i))

let vec_at_ntt (#k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_ntt v) i == ntt (vec_at v i))
  = vec_at_of_fun k (fun i -> ntt (vec_at v i)) i

let vec_at_intt (#k: pos) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_intt v) i == intt (vec_at v i))
  = vec_at_of_fun k (fun i -> intt (vec_at v i)) i

let vec_at_scale (#k: pos) (c: poly) (v: pvec k) (i: nat { i < k })
  : Lemma (vec_at (vec_scale c v) i == poly_mul c (vec_at v i))
  = vec_at_of_fun k (fun i -> poly_mul c (vec_at v i)) i

let vec_at_mat (#k #l: pos) (m: pmat k l) (v: pvec l) (i: nat { i < k })
  : Lemma (vec_at (mat_vec_mul m v) i == dot (mat_row m i) v)
  = vec_at_of_fun k (fun i -> dot (mat_row m i) v) i

(** {2 The NTT on vectors} *)

let vec_ntt_intt (#k: pos) (v: pvec k) : Lemma (vec_ntt (vec_intt v) == v)
  = introduce forall (i: nat { i < k }). vec_at (vec_ntt (vec_intt v)) i == vec_at v i
    with (vec_at_ntt (vec_intt v) i; vec_at_intt v i; NL.ntt_intt (vec_at v i));
    vec_ext (vec_ntt (vec_intt v)) v

let vec_ntt_add (#k: pos) (u v: pvec k)
  : Lemma (vec_ntt (vec_add u v) == vec_add (vec_ntt u) (vec_ntt v))
  = introduce forall (i: nat { i < k }).
      vec_at (vec_ntt (vec_add u v)) i == vec_at (vec_add (vec_ntt u) (vec_ntt v)) i
    with begin
      vec_at_ntt (vec_add u v) i; vec_at_add u v i;
      vec_at_add (vec_ntt u) (vec_ntt v) i; vec_at_ntt u i; vec_at_ntt v i;
      NL.ntt_add (vec_at u i) (vec_at v i)
    end;
    vec_ext (vec_ntt (vec_add u v)) (vec_add (vec_ntt u) (vec_ntt v))

let vec_ntt_sub (#k: pos) (u v: pvec k)
  : Lemma (vec_ntt (vec_sub u v) == vec_sub (vec_ntt u) (vec_ntt v))
  = introduce forall (i: nat { i < k }).
      vec_at (vec_ntt (vec_sub u v)) i == vec_at (vec_sub (vec_ntt u) (vec_ntt v)) i
    with begin
      vec_at_ntt (vec_sub u v) i; vec_at_sub u v i;
      vec_at_sub (vec_ntt u) (vec_ntt v) i; vec_at_ntt u i; vec_at_ntt v i;
      NL.ntt_sub (vec_at u i) (vec_at v i)
    end;
    vec_ext (vec_ntt (vec_sub u v)) (vec_sub (vec_ntt u) (vec_ntt v))

let vec_intt_add (#k: pos) (u v: pvec k)
  : Lemma (vec_intt (vec_add u v) == vec_add (vec_intt u) (vec_intt v))
  = introduce forall (i: nat { i < k }).
      vec_at (vec_intt (vec_add u v)) i == vec_at (vec_add (vec_intt u) (vec_intt v)) i
    with begin
      vec_at_intt (vec_add u v) i; vec_at_add u v i;
      vec_at_add (vec_intt u) (vec_intt v) i; vec_at_intt u i; vec_at_intt v i;
      NL.intt_add (vec_at u i) (vec_at v i)
    end;
    vec_ext (vec_intt (vec_add u v)) (vec_add (vec_intt u) (vec_intt v))

let vec_intt_sub (#k: pos) (u v: pvec k)
  : Lemma (vec_intt (vec_sub u v) == vec_sub (vec_intt u) (vec_intt v))
  = introduce forall (i: nat { i < k }).
      vec_at (vec_intt (vec_sub u v)) i == vec_at (vec_sub (vec_intt u) (vec_intt v)) i
    with begin
      vec_at_intt (vec_sub u v) i; vec_at_sub u v i;
      vec_at_sub (vec_intt u) (vec_intt v) i; vec_at_intt u i; vec_at_intt v i;
      NL.intt_sub (vec_at u i) (vec_at v i)
    end;
    vec_ext (vec_intt (vec_sub u v)) (vec_sub (vec_intt u) (vec_intt v))

(** {2 The matrix product is linear} *)

let dot_step (#l: pos) (u v: pvec l) (i: nat) (acc: poly) : poly
  = if i < l then poly_add acc (poly_mul (vec_at u i) (vec_at v i)) else acc

let dot_unfold (#l: pos) (u v: pvec l)
  : Lemma (dot u v == Loops.repeati #poly l (dot_step u v) poly_zero)
  = assert (dot u v == Loops.repeati #poly l (dot_step u v) poly_zero)
      by (FStar.Tactics.norm [delta_only [`%dot; `%dot_step]]; FStar.Tactics.trefl ())

let lin_coeff (a b r y c s: zq)
  : Lemma (add (add a (mul c b)) (mul r (add y (mul c s))) ==
           add (add a (mul r y)) (mul c (add b (mul r s))))
  = assert (add (add a (mul c b)) (mul r (add y (mul c s))) ==
            add (add a (mul r y)) (mul c (add b (mul r s)))) by (zring ())

let rec dot_lin_loop (#l: pos) (r y s: pvec l) (c: poly) (m: nat)
  : Lemma (ensures Loops.repeati #poly m (dot_step r (vec_add y (vec_scale c s))) poly_zero ==
                   poly_add (Loops.repeati #poly m (dot_step r y) poly_zero)
                            (poly_mul c (Loops.repeati #poly m (dot_step r s) poly_zero)))
          (decreases m)
  = let x = vec_add y (vec_scale c s) in
    if m = 0 then begin
      Loops.repeati_zero #poly (dot_step r x) poly_zero;
      Loops.repeati_zero #poly (dot_step r y) poly_zero;
      Loops.repeati_zero #poly (dot_step r s) poly_zero;
      introduce forall (j: nat). j < n ==>
        Seq.index (poly_zero) j == Seq.index (poly_add poly_zero (poly_mul c poly_zero)) j
      with introduce _ ==> _ with (mul_zero (Seq.index c j); add_zero 0);
      poly_ext poly_zero (poly_add poly_zero (poly_mul c poly_zero))
    end else begin
      dot_lin_loop r y s c (m - 1);
      Loops.unfold_repeati #poly (m - 1) (dot_step r x) poly_zero;
      Loops.unfold_repeati #poly (m - 1) (dot_step r y) poly_zero;
      Loops.unfold_repeati #poly (m - 1) (dot_step r s) poly_zero;
      let a = Loops.repeati #poly (m - 1) (dot_step r y) poly_zero in
      let b = Loops.repeati #poly (m - 1) (dot_step r s) poly_zero in
      if m - 1 < l then begin
        vec_at_add y (vec_scale c s) (m - 1);
        vec_at_scale c s (m - 1);
        let lhs = Loops.repeati #poly m (dot_step r x) poly_zero in
        let rhs = poly_add (Loops.repeati #poly m (dot_step r y) poly_zero)
                           (poly_mul c (Loops.repeati #poly m (dot_step r s) poly_zero)) in
        introduce forall (j: nat). j < n ==> Seq.index lhs j == Seq.index rhs j
        with introduce _ ==> _
        with lin_coeff (Seq.index a j) (Seq.index b j) (Seq.index (vec_at r (m - 1)) j)
                       (Seq.index (vec_at y (m - 1)) j) (Seq.index c j)
                       (Seq.index (vec_at s (m - 1)) j);
        poly_ext lhs rhs
      end
    end

let dot_lin (#l: pos) (r y s: pvec l) (c: poly)
  : Lemma (dot r (vec_add y (vec_scale c s)) == poly_add (dot r y) (poly_mul c (dot r s)))
  = dot_unfold r (vec_add y (vec_scale c s));
    dot_unfold r y;
    dot_unfold r s;
    dot_lin_loop r y s c l

let mat_lin (#k #l: pos) (a: pmat k l) (y s: pvec l) (c: poly)
  : Lemma (mat_vec_mul a (vec_add y (vec_scale c s)) ==
           vec_add (mat_vec_mul a y) (vec_scale c (mat_vec_mul a s)))
  = let lhs = mat_vec_mul a (vec_add y (vec_scale c s)) in
    let rhs = vec_add (mat_vec_mul a y) (vec_scale c (mat_vec_mul a s)) in
    introduce forall (i: nat { i < k }). vec_at lhs i == vec_at rhs i
    with begin
      vec_at_mat a (vec_add y (vec_scale c s)) i;
      vec_at_add (mat_vec_mul a y) (vec_scale c (mat_vec_mul a s)) i;
      vec_at_mat a y i;
      vec_at_scale c (mat_vec_mul a s) i;
      vec_at_mat a s i;
      dot_lin (mat_row a i) y s c
    end;
    vec_ext lhs rhs

(** {2 What the verifier recomputes} *)

let coeff_id (ay as1 s2 t0 c: zq)
  : Lemma (sub (add ay (mul c as1)) (mul c (sub (add as1 s2) t0)) ==
           add (sub ay (mul c s2)) (mul c t0))
  = mul_sub_distr c (add as1 s2) t0;
    mul_add_distr c as1 s2

let vec_id (#k: pos) (ay as1 s2 t0: pvec k) (c: poly)
  : Lemma (vec_sub (vec_add ay (vec_scale c as1)) (vec_scale c (vec_sub (vec_add as1 s2) t0)) ==
           vec_add (vec_sub ay (vec_scale c s2)) (vec_scale c t0))
  = let lhs = vec_sub (vec_add ay (vec_scale c as1)) (vec_scale c (vec_sub (vec_add as1 s2) t0)) in
    let rhs = vec_add (vec_sub ay (vec_scale c s2)) (vec_scale c t0) in
    introduce forall (i: nat { i < k }). vec_at lhs i == vec_at rhs i
    with begin
      vec_at_sub (vec_add ay (vec_scale c as1)) (vec_scale c (vec_sub (vec_add as1 s2) t0)) i;
      vec_at_add ay (vec_scale c as1) i;
      vec_at_scale c as1 i;
      vec_at_scale c (vec_sub (vec_add as1 s2) t0) i;
      vec_at_sub (vec_add as1 s2) t0 i;
      vec_at_add as1 s2 i;
      vec_at_add (vec_sub ay (vec_scale c s2)) (vec_scale c t0) i;
      vec_at_sub ay (vec_scale c s2) i;
      vec_at_scale c s2 i;
      vec_at_scale c t0 i;
      introduce forall (j: nat). j < n ==> Seq.index (vec_at lhs i) j == Seq.index (vec_at rhs i) j
      with introduce _ ==> _
      with coeff_id (Seq.index (vec_at ay i) j) (Seq.index (vec_at as1 i) j)
                    (Seq.index (vec_at s2 i) j) (Seq.index (vec_at t0 i) j) (Seq.index c j);
      poly_ext (vec_at lhs i) (vec_at rhs i)
    end;
    vec_ext lhs rhs

(** [t1 2^d = t - t0]. *)
let t1_shift_eq (#k: pos) (t: pvec k)
  : Lemma (t1_shift (vec_power2round_hi t) == vec_sub t (vec_power2round_lo t))
  = introduce forall (i: nat). i < k * n ==>
      Seq.index (t1_shift (vec_power2round_hi t)) i == Seq.index (vec_sub t (vec_power2round_lo t)) i
    with introduce _ ==> _
    with Spec.MLDSA.Rounding.Lemmas.power2round_props (Seq.index t i);
    Seq.lemma_eq_intro (t1_shift (vec_power2round_hi t)) (vec_sub t (vec_power2round_lo t))

(** The verifier's [w'] is the signer's [w - c s2 + c t0]. *)
let verify_w_eq (p: params) (a: pmat p.k p.l) (s1: pvec p.l) (s2: pvec p.k)
                (y: pvec p.l) (c: poly)
  : Lemma (let t = keygen_t p a s1 s2 in
           let t0 = vec_power2round_lo t in
           let ch = ntt c in
           let w = commit p a y in
           let cs1 = vec_intt (vec_scale ch (vec_ntt s1)) in
           let cs2 = vec_intt (vec_scale ch (vec_ntt s2)) in
           let ct0 = vec_intt (vec_scale ch (vec_ntt t0)) in
           verify_w p a (vec_power2round_hi t) c (vec_add y cs1) ==
           vec_add (vec_sub w cs2) ct0)
  = let t = keygen_t p a s1 s2 in
    let t0 = vec_power2round_lo t in
    let ch = ntt c in
    let ys = vec_ntt y in
    let s1h = vec_ntt s1 in
    let s2h = vec_ntt s2 in
    let t0h = vec_ntt t0 in
    let as1 = mat_vec_mul a s1h in
    let ay = mat_vec_mul a ys in
    let cs1 = vec_intt (vec_scale ch s1h) in
    vec_ntt_add y cs1;
    vec_ntt_intt (vec_scale ch s1h);
    mat_lin a ys s1h ch;
    t1_shift_eq t;
    vec_ntt_sub t t0;
    vec_ntt_add (vec_intt as1) s2;
    vec_ntt_intt as1;
    vec_id ay as1 s2h t0h ch;
    vec_intt_add (vec_sub ay (vec_scale ch s2h)) (vec_scale ch t0h);
    vec_intt_sub ay (vec_scale ch s2h)

(** {2 The high part survives} *)

(** [c s2] is at most [beta]: it is the negacyclic product of a
    challenge of [l1] norm at most [tau] with a vector bounded by [eta]. *)
let cs2_bound (p: params) (c: poly) (s2: pvec p.k)
  : Lemma (requires SL.l1 c n <= p.tau /\
                    (forall (i: nat). i < p.k * n ==> norm (Seq.index s2 i) <= p.eta))
          (ensures (let cs2 = vec_intt (vec_scale (ntt c) (vec_ntt s2)) in
                    forall (i: nat). i < p.k * n ==> norm (Seq.index cs2 i) <= beta p))
  = let cs2 = vec_intt (vec_scale (ntt c) (vec_ntt s2)) in
    Math.lemma_mult_le_left p.eta (SL.l1 c n) p.tau;
    introduce forall (i: nat). i < p.k * n ==> norm (Seq.index cs2 i) <= beta p
    with introduce _ ==> _
    with begin
      KZ.div_lt i p.k n;
      let m = i / n in
      let j = i % n in
      Math.euclidean_division_definition i n;
      EL.flat_at_index p.k n cs2 m j;
      vec_at_intt (vec_scale (ntt c) (vec_ntt s2)) m;
      vec_at_scale (ntt c) (vec_ntt s2) m;
      vec_at_ntt s2 m;
      NL.intt_poly_mul_ntt c (vec_at s2 m);
      introduce forall (j': nat). j' < n ==> norm (Seq.index (vec_at s2 m) j') <= p.eta
      with introduce _ ==> _ with EL.flat_at_index p.k n s2 m j';
      SL.ring_mul_bound c (vec_at s2 m) p.eta j;
      assert (vec_at cs2 m == ring_mul c (vec_at s2 m));
      assert (Seq.index cs2 i == Seq.index (ring_mul c (vec_at s2 m)) j);
      Math.swap_mul p.tau p.eta;
      assert (p.eta * SL.l1 c n <= beta p)
    end

(** One coefficient: the hint at [r + c t0] gives the high part of [w]. *)
let hint_coeff (p: params) (w cs2 ct0: zq)
  : Lemma (requires norm cs2 <= beta p /\ norm ct0 < gamma2 p /\
                    norm (low_bits p (sub w cs2)) < gamma2 p - beta p)
          (ensures (let r = sub w cs2 in
                    use_hint p (make_hint p (neg ct0) (add r ct0)) (add r ct0) == high_bits p w))
  = let r = sub w cs2 in
    SL.norm_neg ct0;
    RL.use_hint_make_hint p (neg ct0) (add r ct0);
    assert (add (add r ct0) (neg ct0) == r);
    RL.high_bits_stable p r cs2 (beta p);
    assert (add r cs2 == w)

let hint_vec (p: params) (w cs2 ct0: pvec p.k)
  : Lemma (requires (forall (i: nat). i < p.k * n ==> norm (Seq.index cs2 i) <= beta p) /\
                    all_lt ct0 (gamma2 p) /\
                    all_lt (vec_low_bits p (vec_sub w cs2)) (gamma2 p - beta p))
          (ensures (let r = vec_sub w cs2 in
                    vec_use_hint p (vec_make_hint p (vec_map neg ct0) (vec_add r ct0))
                                   (vec_add r ct0) == vec_high_bits p w))
  = let r = vec_sub w cs2 in
    all_lt_spec ct0 (gamma2 p);
    all_lt_spec (vec_low_bits p r) (gamma2 p - beta p);
    let lhs = vec_use_hint p (vec_make_hint p (vec_map neg ct0) (vec_add r ct0)) (vec_add r ct0) in
    introduce forall (i: nat). i < p.k * n ==> Seq.index lhs i == Seq.index (vec_high_bits p w) i
    with introduce _ ==> _
    with hint_coeff p (Seq.index w i) (Seq.index cs2 i) (Seq.index ct0 i);
    Seq.lemma_eq_intro lhs (vec_high_bits p w)

(** {2 Sign then verify} *)

(** Verification once the public key is decoded. *)
let verify_core (p: params) (a: pmat p.k p.l) (t1: Seq.lseq nat (p.k * n))
                (mu: Seq.lseq S8.t 64) (sg: Seq.lseq S8.t (sig_len p))
  : GTot bool
  = let ct, z, ho = sig_decode p sg in
    match ho with
    | None -> false
    | Some h ->
      beta_lt p;
      all_lt z (gamma1 p - beta p) &&
      (let w' = verify_w p a t1 (sample_in_ball p ct) z in
       FStar.IndefiniteDescription.strong_excluded_middle
         (ct == challenge_hash p mu (vec_use_hint p h w')))

let bounded (p: params) (#k: pos) (s: pvec k) : prop
  = forall (i: nat). i < k * n ==> norm (Seq.index s i) <= p.eta

let key_ctx (p: params) (a: pmat p.k p.l) (s1: pvec p.l) (s2: pvec p.k) : sign_ctx p
  = { sc_a = a; sc_s1 = vec_ntt s1; sc_s2 = vec_ntt s2;
      sc_t0 = vec_ntt (vec_power2round_lo (keygen_t p a s1 s2)) }

(** An attempt that is not rejected gives a signature that verifies. *)
let attempt_verifies (p: params) (a: pmat p.k p.l) (s1: pvec p.l) (s2: pvec p.k)
                     (mu rho'': Seq.lseq S8.t 64) (att: nat { att < max_attempts })
  : Lemma (requires bounded p s2 /\ Some? (sign_attempt p (key_ctx p a s1 s2) mu rho'' att))
          (ensures verify_core p a (vec_power2round_hi (keygen_t p a s1 s2)) mu
                     (Some?.v (sign_attempt p (key_ctx p a s1 s2) mu rho'' att)))
  = beta_lt p;
    let sc = key_ctx p a s1 s2 in
    let t = keygen_t p a s1 s2 in
    let t0 = vec_power2round_lo t in
    let y = expand_mask p rho'' att in
    let w = commit p a y in
    let ct = challenge_hash p mu (vec_high_bits p w) in
    let c0 = sample_in_ball p ct in
    let c = ntt c0 in
    let cs1 = vec_intt (vec_scale c sc.sc_s1) in
    let cs2 = vec_intt (vec_scale c sc.sc_s2) in
    let z = vec_add y cs1 in
    let r = vec_sub w cs2 in
    let ct0 = vec_intt (vec_scale c sc.sc_t0) in
    let h = vec_make_hint p (vec_map neg ct0) (vec_add r ct0) in
    assert (all_lt z (gamma1 p - beta p));
    assert (all_lt (vec_low_bits p r) (gamma2 p - beta p));
    assert (all_lt ct0 (gamma2 p));
    assert (count_true h <= p.omega);
    assert (sign_attempt p sc mu rho'' att == Some (sig_encode p ct z h));
    all_lt_spec z (gamma1 p - beta p);
    Spec.MLDSA.Hint.Lemmas.hint_scatter_pack p h;
    EL.sig_decode_encode p ct z h;
    verify_w_eq p a s1 s2 y c0;
    SL.sample_in_ball_l1 p ct;
    cs2_bound p c0 s2;
    hint_vec p w cs2 ct0

let rec loop_verifies (p: params) (a: pmat p.k p.l) (s1: pvec p.l) (s2: pvec p.k)
                      (mu rho'': Seq.lseq S8.t 64) (i: nat)
  : Lemma (requires bounded p s2 /\ Some? (sign_loop p (key_ctx p a s1 s2) mu rho'' i))
          (ensures verify_core p a (vec_power2round_hi (keygen_t p a s1 s2)) mu
                     (Some?.v (sign_loop p (key_ctx p a s1 s2) mu rho'' i)))
          (decreases max_attempts - i)
  = assert_norm (sign_loop p (key_ctx p a s1 s2) mu rho'' i ==
                 (if i >= max_attempts then None
                  else match sign_attempt p (key_ctx p a s1 s2) mu rho'' i with
                    | Some s -> Some s
                    | None -> sign_loop p (key_ctx p a s1 s2) mu rho'' (i + 1)));
    match sign_attempt p (key_ctx p a s1 s2) mu rho'' i with
    | Some _ -> attempt_verifies p a s1 s2 mu rho'' i
    | None -> loop_verifies p a s1 s2 mu rho'' (i + 1)

(** The keys from [keygen_internal] decode to what was encoded. *)
let keygen_decode (p: params) (xi: Seq.lseq S8.t 32)
  : Lemma (let h = hash (keygen_seed p xi) 128 in
           let rho : Seq.lseq S8.t 32 = Seq.slice h 0 32 in
           let rho' : Seq.lseq S8.t 64 = Seq.slice h 32 96 in
           let a = expand_a p rho in
           let s1 = expand_s1 p rho' in
           let s2 = expand_s2 p rho' in
           let t = keygen_t p a s1 s2 in
           let pk, sk = keygen_internal p xi in
           let sp = sk_decode p sk in
           pk_decode p pk == (rho, vec_power2round_hi t) /\
           sp.sk_rho == rho /\ sp.sk_s1 == s1 /\ sp.sk_s2 == s2 /\
           sp.sk_t0 == vec_power2round_lo t /\
           Seq.slice sk 64 128 == hash pk 64 /\
           bounded p s2)
  = let h = hash (keygen_seed p xi) 128 in
    let rho : Seq.lseq S8.t 32 = Seq.slice h 0 32 in
    let rho' : Seq.lseq S8.t 64 = Seq.slice h 32 96 in
    let key : Seq.lseq S8.t 32 = Seq.slice h 96 128 in
    let a = expand_a p rho in
    let s1 = expand_s1 p rho' in
    let s2 = expand_s2 p rho' in
    let t = keygen_t p a s1 s2 in
    let t1 = vec_power2round_hi t in
    let t0 = vec_power2round_lo t in
    let pk = pk_encode p rho t1 in
    let tr = hash pk 64 in
    SL.expand_s1_bound p rho';
    SL.expand_s2_bound p rho';
    introduce forall (i: nat). i < p.k * n ==>
      Seq.index t1 i < pow2 10 /\ - 4096 < centre (Seq.index t0 i) /\ centre (Seq.index t0 i) <= 4096
    with introduce _ ==> _ with RL.power2round_props (Seq.index t i);
    EL.pk_decode_encode p rho t1;
    EL.sk_decode_encode p rho key tr s1 s2 t0;
    EL.tr_of_sk p rho key tr s1 s2 t0

(** Correctness from [mu]: a signature made with a generated private key
    is accepted under the matching public key. *)
let sign_verify_mu (p: params) (xi: Seq.lseq S8.t 32) (mu: Seq.lseq S8.t 64)
                   (rnd: Seq.lseq S8.t 32)
  : Lemma (let pk, sk = keygen_internal p xi in
           match sign_mu p sk mu rnd with
           | Some sg -> verify_mu p pk mu sg
           | None -> True)
  = let h = hash (keygen_seed p xi) 128 in
    let rho : Seq.lseq S8.t 32 = Seq.slice h 0 32 in
    let rho' : Seq.lseq S8.t 64 = Seq.slice h 32 96 in
    let a = expand_a p rho in
    let s1 = expand_s1 p rho' in
    let s2 = expand_s2 p rho' in
    let pk, sk = keygen_internal p xi in
    let sp = sk_decode p sk in
    keygen_decode p xi;
    assert (sign_ctx_of p sp == key_ctx p a s1 s2);
    let rho'' = hash (Seq.append sp.sk_key (Seq.append rnd mu)) 64 in
    match sign_loop p (key_ctx p a s1 s2) mu rho'' 0 with
    | Some _ -> loop_verifies p a s1 s2 mu rho'' 0
    | None -> ()

let sign_verify_internal (p: params) (xi: Seq.lseq S8.t 32) (m': Seq.seq S8.t)
                         (rnd: Seq.lseq S8.t 32)
  : Lemma (let pk, sk = keygen_internal p xi in
           match sign_internal p sk m' rnd with
           | Some sg -> verify_internal p pk m' sg
           | None -> True)
  = let pk, sk = keygen_internal p xi in
    keygen_decode p xi;
    sign_verify_mu p xi (message_rep (hash pk 64) m') rnd

(** Correctness of the pure variant, for any message and context. *)
let sign_verify (p: params) (xi: Seq.lseq S8.t 32) (msg ctx: Seq.seq S8.t)
                (rnd: Seq.lseq S8.t 32)
  : Lemma (let pk, sk = keygen_internal p xi in
           match sign p sk msg ctx rnd with
           | Some sg -> verify p pk msg ctx sg
           | None -> True)
  = if Seq.length ctx < 256 then sign_verify_internal p xi (format_msg msg ctx) rnd

#pop-options
