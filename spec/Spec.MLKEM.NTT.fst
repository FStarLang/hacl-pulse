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

(** The number-theoretic transform, FIPS 203 algorithms 9 through 12.

    The standard specifies the NTT as an in-place iterative butterfly
    network over seven layers, not as the evaluation map it computes.  This
    module follows the standard.  That is the same bar met for Frodo --
    "the implementation computes what the standard's pseudocode computes" --
    and it is the property a reader of the C output can check against FIPS
    203 line by line.  The deeper theorem, that [NTT] is the isomorphism
    [R_q ~ prod_i Z_q[X]/(X^2 - zeta^(2 BitRev7(i) + 1))] and hence that
    [MultiplyNTTs] is multiplication in [R_q], is proved separately in
    {!Spec.MLKEM.NTT.Lemmas} ([intt_multiply_ntts]: [intt (multiply_ntts
    (ntt f) (ntt g)) == poly_mul f g]); it is about these definitions only
    and independent of the implementation.

    The one place this presentation departs from the pseudocode is that a
    layer is written {i pointwise} -- as a function of the input polynomial
    computing output coefficient [t] -- rather than as a pair of nested
    loops over [start] and [j].  Within one layer the butterflies are
    disjoint, so the two agree, and the pointwise form is what an
    implementation's loop invariant wants to say anyway.  All the index
    arithmetic then lives in four small lemmas at the top of the file
    instead of being rediscovered inside every proof. *)
module Spec.MLKEM.NTT

open Spec.MLKEM.Zq

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops

#push-options "--fuel 0 --ifuel 0"

(** {2 Index arithmetic}

    A layer with half-width [len = 2^e] pairs coefficient [t] with
    [t + len] when bit [e] of [t] is clear, and with [t - len] when it is
    set.  Both halves of that pairing have to be shown in range, and
    [pow2] makes the goals nonlinear, so they are proved once. *)

let n_pow2 () : Lemma (n == pow2 8) = assert_norm (256 == pow2 8)

(** A coefficient in the lower half of its butterfly has a partner. *)
let even_step (e: nat { e <= 7 }) (t: nat { t < n })
  : Lemma (requires (t / pow2 e) % 2 == 0) (ensures t + pow2 e < n)
  = let p = pow2 e in
    let m = pow2 (8 - e) in
    n_pow2 ();
    Math.pow2_plus (8 - e) e;
    assert (n == m * p);
    div_lt t m p;
    Math.pow2_plus 1 (7 - e);
    assert_norm (pow2 1 == 2);
    assert (m == 2 * pow2 (7 - e));
    assert (t / p <= m - 2);
    Math.lemma_div_mod t p;
    Math.distributivity_add_left (t / p) 1 p;
    Math.lemma_mult_le_right p (t / p + 1) (m - 1);
    Math.distributivity_sub_left m 1 p

(** A coefficient in the upper half is a partner. *)
let odd_step (e: nat { e <= 7 }) (t: nat { t < n })
  : Lemma (requires (t / pow2 e) % 2 <> 0) (ensures pow2 e <= t)
  = Math.lemma_div_mod t (pow2 e);
    Math.lemma_mult_le_right (pow2 e) 1 (t / pow2 e)

(** The zeta table index of the butterfly [t] belongs to, forward
    direction: [2^(7-e)] blocks have been used by the earlier layers, and
    [t / 2^(e+1)] blocks by this one. *)
let zidx (e: nat { 1 <= e /\ e <= 7 }) (t: nat { t < n }) : r: nat { r < 128 }
  = let b = t / pow2 (e + 1) in
    n_pow2 ();
    Math.pow2_plus (7 - e) (e + 1);
    div_lt t (pow2 (7 - e)) (pow2 (e + 1));
    Math.pow2_plus 1 (7 - e);
    Math.pow2_le_compat 7 (8 - e);
    assert_norm (pow2 1 == 2);
    assert_norm (pow2 7 == 128);
    pow2 (7 - e) + b

(** The same index read backwards, which is what algorithm 10 does: it
    starts at 127 and decrements, so the layer with half-width [2^e]
    consumes [2^(8-e) - 1] down to [2^(7-e)]. *)
let zidx_inv (e: nat { 1 <= e /\ e <= 7 }) (t: nat { t < n }) : r: nat { r < 128 }
  = let b = t / pow2 (e + 1) in
    n_pow2 ();
    Math.pow2_plus (7 - e) (e + 1);
    div_lt t (pow2 (7 - e)) (pow2 (e + 1));
    Math.pow2_plus 1 (7 - e);
    Math.pow2_le_compat 7 (8 - e);
    assert_norm (pow2 1 == 2);
    assert_norm (pow2 7 == 128);
    pow2 (8 - e) - 1 - b

(** {2 The roots of unity}

    [zetas.[i] = zeta^BitRev7(i)], the table FIPS 203 tabulates in appendix
    A.  The implementation will carry the 128 literals and prove them equal
    to this. *)

let zetas (i: nat { i < 128 }) : zq = pow zeta (bitrev7 i)

(** The [gamma] of algorithm 12: the modulus of the [i]th quadratic factor
    is [X^2 - zeta^(2 BitRev7(i) + 1)]. *)
let gammas (i: nat { i < 128 }) : zq = pow zeta (2 * bitrev7 i + 1)

(** ... which is [zetas.[i]^2 * zeta], so an implementation needs only the
    one table: two multiplications recover [gamma] from [zeta^BitRev7(i)]. *)

let gammas_zetas (i: nat { i < 128 })
  : Lemma (gammas i == mul (mul (zetas i) (zetas i)) zeta)
  = let b = bitrev7 i in
    pow_add zeta (2 * b) 1;
    pow_one zeta;
    assert (gammas i == mul (pow zeta (2 * b)) zeta);
    pow_add zeta b b;
    assert (pow zeta (2 * b) == mul (zetas i) (zetas i))

(** {2 The forward transform}

    One Cooley-Tukey layer, pointwise.  For a coefficient in the lower half
    of its butterfly the standard writes [f[j] + zeta * f[j + len]]; for one
    in the upper half, [f[j] - zeta * f[j + len]] with [j = t - len].  Both
    read the {i input} polynomial, which is why the in-place pseudocode
    ("write [j+len] before [j]") and this out-of-place reading agree. *)
let ntt_layer_at (e: nat { 1 <= e /\ e <= 7 }) (f: poly) (t: nat { t < n }) : zq
  = let len = pow2 e in
    let z = zetas (zidx e t) in
    if (t / len) % 2 = 0 then begin
      even_step e t;
      add (Seq.index f t) (mul z (Seq.index f (t + len)))
    end else begin
      odd_step e t;
      sub (Seq.index f (t - len)) (mul z (Seq.index f t))
    end

let ntt_layer (e: nat { 1 <= e /\ e <= 7 }) (f: poly) : poly
  = Seq.init n (ntt_layer_at e f)

let ntt_layer_index (e: nat { 1 <= e /\ e <= 7 }) (f: poly) (t: nat { t < n })
  : Lemma (Seq.index (ntt_layer e f) t == ntt_layer_at e f t)
  = Seq.init_index_ n (ntt_layer_at e f) t

(** Algorithm 9.  Seven layers, half-width 128 down to 2; the layer with
    half-width 1 is deliberately absent, which is what leaves the output in
    128 quadratic residues rather than 256 linear ones. *)
let ntt (f: poly) : poly
  = Loops.repeati 7 (fun l acc -> if l < 7 then ntt_layer (7 - l) acc else acc) f

(** The seven layers, spelled out: an implementation runs them one after
    another rather than as a fold, and this is the bridge. *)
#push-options "--fuel 8"
let ntt_unfold (f: poly)
  : Lemma (ntt f ==
           ntt_layer 1 (ntt_layer 2 (ntt_layer 3 (ntt_layer 4
             (ntt_layer 5 (ntt_layer 6 (ntt_layer 7 f)))))))
  = ()
#pop-options

(** {2 The inverse transform}

    One Gentleman-Sande layer.  The lower half adds, the upper half
    subtracts and then scales -- note that unlike the forward layer the
    multiplication by [zeta] happens after the subtraction, which is what
    makes the two layers mutually inverse rather than merely similar. *)
let intt_layer_at (e: nat { 1 <= e /\ e <= 7 }) (f: poly) (t: nat { t < n }) : zq
  = let len = pow2 e in
    let z = zetas (zidx_inv e t) in
    if (t / len) % 2 = 0 then begin
      even_step e t;
      add (Seq.index f t) (Seq.index f (t + len))
    end else begin
      odd_step e t;
      mul z (sub (Seq.index f t) (Seq.index f (t - len)))
    end

let intt_layer (e: nat { 1 <= e /\ e <= 7 }) (f: poly) : poly
  = Seq.init n (intt_layer_at e f)

let intt_layer_index (e: nat { 1 <= e /\ e <= 7 }) (f: poly) (t: nat { t < n })
  : Lemma (Seq.index (intt_layer e f) t == intt_layer_at e f t)
  = Seq.init_index_ n (intt_layer_at e f) t

(** [128^-1 mod q].  The seven layers each double the result, so the
    inverse transform ends by scaling the whole polynomial down. *)
let inv_128 : zq = 3303

let inv_128_correct () : Lemma (mul 128 inv_128 == 1) = assert_norm (mul 128 inv_128 == 1)

let poly_scale (c: zq) (f: poly) : poly
  = Seq.init n (fun i -> mul c (Seq.index f i))

let poly_scale_index (c: zq) (f: poly) (i: nat { i < n })
  : Lemma (Seq.index (poly_scale c f) i == mul c (Seq.index f i))
          [SMTPat (Seq.index (poly_scale c f) i)]
  = Seq.init_index_ n (fun j -> mul c (Seq.index f j)) i

(** Algorithm 10.  The layers run the other way, half-width 2 up to 128. *)
let intt (f: poly) : poly
  = poly_scale inv_128 (Loops.repeati 7 (fun l acc -> if l < 7 then intt_layer (1 + l) acc else acc) f)

#push-options "--fuel 8"
let intt_unfold (f: poly)
  : Lemma (intt f ==
           poly_scale inv_128
             (intt_layer 7 (intt_layer 6 (intt_layer 5 (intt_layer 4
               (intt_layer 3 (intt_layer 2 (intt_layer 1 f))))))))
  = ()
#pop-options

(** {2 Multiplication in the NTT domain} *)

(** Algorithm 12.  [(a0 + a1 X) * (b0 + b1 X)] modulo [X^2 - gamma]. *)
let base_case_multiply (a0 a1 b0 b1 g: zq) : zq & zq
  = add (mul a0 b0) (mul (mul a1 b1) g),
    add (mul a0 b1) (mul a1 b0)

(** Algorithm 11.  128 independent quadratic products, the [i]th modulo
    [X^2 - gammas i]. *)
let multiply_ntts_at (f g: poly) (t: nat { t < n }) : zq
  = let i = t / 2 in
    div_lt t 128 2;
    let c0, c1 =
      base_case_multiply (Seq.index f (2 * i)) (Seq.index f (2 * i + 1))
                         (Seq.index g (2 * i)) (Seq.index g (2 * i + 1))
                         (gammas i) in
    if t % 2 = 0 then c0 else c1

let multiply_ntts (f g: poly) : poly
  = Seq.init n (multiply_ntts_at f g)

let multiply_ntts_index (f g: poly) (t: nat { t < n })
  : Lemma (Seq.index (multiply_ntts f g) t == multiply_ntts_at f g t)
  = Seq.init_index_ n (multiply_ntts_at f g) t

(** {2 Vectors}

    The transform and the pointwise product lift to the [k]-vectors and
    [k x k] matrices of the scheme proper.  [dot] is the inner product that
    computes one entry of a matrix-vector product; it is a fold rather than
    a [Seq.init] because it accumulates. *)

let vec_ntt (#k: pos) (v: pvec k) : pvec k
  = vec_of_fun k (fun i -> ntt (vec_at v i))

let vec_intt (#k: pos) (v: pvec k) : pvec k
  = vec_of_fun k (fun i -> intt (vec_at v i))

let dot (#k: pos) (u v: pvec k) : poly
  = Loops.repeati k
      (fun i acc ->
         if i < k then poly_add acc (multiply_ntts (vec_at u i) (vec_at v i))
         else acc)
      poly_zero

(** A [k x k] matrix of polynomials, flat and row-major, as a vector of [k]
    rows.  Entry [(i, j)] is polynomial [i * k + j]. *)
let pmat (k: pos) = Seq.lseq zq (k * k * n)

let mat_row (#k: pos) (m: pmat k) (i: nat { i < k }) : pvec k
  = Math.lemma_mult_le_right (k * n) (i + 1) k;
    Math.paren_mul_right k k n;
    Seq.slice m (i * (k * n)) (i * (k * n) + k * n)

let mat_vec_mul (#k: pos) (m: pmat k) (v: pvec k) : pvec k
  = vec_of_fun k (fun i -> dot (mat_row m i) v)

(** The transpose-times-vector the encapsulator needs.  Rather than
    transposing and multiplying, index the other way. *)
let mat_transpose (#k: pos) (m: pmat k) : pmat k
  = Seq.init (k * k * n) (fun t ->
      Math.paren_mul_right k k n;
      div_lt t (k * k) n;
      let c = t / n in
      div_lt c k k;
      let i = c / k in
      let j = c % k in
      Math.lemma_mult_le_right k (i + 1) k;
      Seq.index m ((j * k + i) * n + t % n))

#pop-options
