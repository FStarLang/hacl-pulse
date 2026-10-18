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

(** Correctness of K-PKE and ML-KEM ({!Spec.MLKEM}), FIPS 203 section
    3.3, deterministically: decryption and decapsulation succeed whenever
    the accumulated noise is small.  How likely that is -- the [2^-138]
    and friends of the standard -- is a probabilistic statement about the
    noise distribution and is not proved here.

    {2 The noise}

    Write [s], [e] for the secret and error vectors of key generation and
    [y], [e1], [e2] for the randomness of encryption, all in [R_q]; write
    [u], [v] for the two ciphertext components before compression and
    [du = Decompress(Compress u) - u], [dv = Decompress(Compress v) - v]
    for the rounding errors compression introduces.  Then the polynomial
    [kpke_decrypt] rounds is

    [w = mu + e^T y - s^T (e1 + du) + e2 + dv]

    with [mu = Decompress_1 m] the message scaled to [{0, ceil(q/2)}]
    ([decrypt_w_noise]).  [kpke_noise] is that difference [w - mu].  It is
    determined by the seed [d] of key generation, the message and the
    encryption coins, and so is [noise_ok]: every coefficient, taken in the
    centred range [(-q/2, q/2)], has absolute value below [q / 4 = 832].
    [Compress_1] decodes [ceil(q/2) b + x] to [b] (for both [b]) for
    exactly the [x] in [-832, 831], so the bound, which is the usual
    [||w - mu||_inf < floor(q/4)], is sufficient, and misses only
    [x = -832] from being necessary.

    {2 The proof}

    - {b Serialisation} ({!Spec.MLKEM.Encode.Lemmas}): keys decode to what
      key generation computed, the ciphertext to [Compress u] and
      [Compress v], and the decoded message bits re-encode to [m].
    - {b Algebra} ({!Spec.MLKEM.Ring}): in the NTT domain, with
      [t = A s + e], [u = A^T y + e1] and the bilinearity of [dot],
      [t . y - s . (u + du) = e . y - s . (e1 + du)] because
      [(A s) . y = s . (A^T y)]; [gen_matrix ... true] is the transpose of
      [gen_matrix ... false] because the transposition is in the seed.
      [intt] then turns each NTT-domain inner product into the schoolbook
      one, by the isomorphism of {!Spec.MLKEM.NTT.Lemmas}.
    - {b Rounding} ([compress_1_decode]).
    - {b ML-KEM}: the decapsulation key carries [dk_pke], [ek], [H(ek)] and
      [z] at the offsets [decaps] reads them from; decryption recovers [m],
      so re-encryption recomputes the very same coins and ciphertext and
      the comparison selects the real key. *)
module Spec.MLKEM.Correctness

open FStar.Tactics.V2
open Spec.MLKEM.Zq
open Spec.MLKEM.Params
open Spec.MLKEM.NTT
open Spec.MLKEM.NTT.Lemmas
open Spec.MLKEM.Encode
open Spec.MLKEM.Encode.Lemmas
open Spec.MLKEM.Sample
open Spec.MLKEM.Ring
open Spec.MLKEM

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas

#push-options "--fuel 0 --ifuel 0"

(** {2 The quantities of one key generation and one encryption}

    Exactly what [kpke_keygen] and [kpke_encrypt] compute, named.  [s], [e]
    and [y] are the normal-domain vectors; the algorithms keep only their
    transforms. *)

let kg_rho (p: params) (d: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32)
  = Seq.slice (hash_g (Seq.snoc d (S8.classify (U8.uint_to_t p.k)))) 0 32

let kg_sigma (p: params) (d: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32)
  = Seq.slice (hash_g (Seq.snoc d (S8.classify (U8.uint_to_t p.k)))) 32 64

let kg_s (p: params) (d: Seq.lseq S8.t 32) : GTot (pvec p.k)
  = noise_vec p.k p.eta1 (kg_sigma p d) 0

let kg_e (p: params) (d: Seq.lseq S8.t 32) : GTot (pvec p.k)
  = noise_vec p.k p.eta1 (kg_sigma p d) p.k

(** [t-hat = A-hat s-hat + e-hat]. *)
let kg_t (p: params) (d: Seq.lseq S8.t 32) : GTot (pvec p.k)
  = vec_add (mat_vec_mul (gen_matrix p.k (kg_rho p d) false) (vec_ntt (kg_s p d)))
            (vec_ntt (kg_e p d))

let enc_y (p: params) (r: Seq.lseq S8.t 32) : GTot (pvec p.k) = noise_vec p.k p.eta1 r 0

let enc_e1 (p: params) (r: Seq.lseq S8.t 32) : GTot (pvec p.k) = noise_vec p.k p.eta2 r p.k

let enc_e2 (p: params) (r: Seq.lseq S8.t 32) : GTot poly
  = sample_poly_cbd p.eta2 r (U8.uint_to_t (2 * p.k))

(** [mu = Decompress_1 (ByteDecode_1 m)]. *)
let msg_poly (m: Seq.lseq S8.t 32) : GTot poly = poly_decompress 1 (widen (byte_decode 1 m))

(** [u = NTT^-1 (A-hat^T y-hat) + e1], before compression. *)
let enc_u (p: params) (d r: Seq.lseq S8.t 32) : GTot (pvec p.k)
  = vec_add (vec_intt (mat_vec_mul (gen_matrix p.k (kg_rho p d) true) (vec_ntt (enc_y p r))))
            (enc_e1 p r)

(** [v = NTT^-1 (t-hat^T y-hat) + e2 + mu], before compression. *)
let enc_v (p: params) (d m r: Seq.lseq S8.t 32) : GTot poly
  = poly_add (poly_add (intt (dot (kg_t p d) (vec_ntt (enc_y p r)))) (enc_e2 p r)) (msg_poly m)

(** The rounding errors of the two ciphertext components. *)
let delta_u (p: params) (d r: Seq.lseq S8.t 32) : GTot (pvec p.k)
  = let u = enc_u p d r in
    vec_sub (vec_decompress p.du p.k (vec_compress p.du u)) u

let delta_v (p: params) (d m r: Seq.lseq S8.t 32) : GTot poly
  = let v = enc_v p d m r in
    poly_sub (poly_decompress p.dv (poly_compress p.dv v)) v

(** {2 The noise and the bound} *)

(** [e^T y - s^T (e1 + du) + e2 + dv], in [R_q]. *)
let kpke_noise (p: params) (d m r: Seq.lseq S8.t 32) : GTot poly
  = poly_add
      (poly_add
        (poly_sub (rq_dot (kg_e p d) (enc_y p r))
                  (rq_dot (kg_s p d) (vec_add (enc_e1 p r) (delta_u p d r))))
        (enc_e2 p r))
      (delta_v p d m r)

(** The representative of [x] in [(-q/2, q/2)]. *)
let centered (x: zq) : int = if x > q / 2 then x - q else x

(** [||f||_inf < floor(q/4)]. *)
let noise_ok (f: poly) : prop = forall (i: nat { i < n }). abs (centered (Seq.index f i)) < q / 4

(** {2 Rounding} *)

let compress_1_decode (b: nat { b < 2 }) (x: zq)
  : Lemma (requires abs (centered x) < q / 4)
          (ensures compress 1 (add (decompress 1 b) x) == b)
  = assert_norm (decompress 1 0 == 0);
    assert_norm (decompress 1 1 == 1665);
    assert_norm (pow2 1 == 2);
    assert_norm (q / 2 == 1664 /\ q / 4 == 832);
    assert (x <= 831 \/ x >= 2498);
    let y = add (decompress 1 b) x in
    assert (compress 1 y == ((y * 2 + 1664) / 3329) % 2);
    if b = 0 then begin
      Math.small_mod x q;
      assert (y == x);
      if x <= 831 then Math.small_div (y * 2 + 1664) 3329
      else begin
        Math.lemma_div_plus (y * 2 + 1664 - 2 * 3329) 2 3329;
        Math.small_div (y * 2 + 1664 - 2 * 3329) 3329
      end
    end else begin
      if x <= 831 then begin
        Math.small_mod (1665 + x) q;
        assert (y == 1665 + x);
        Math.lemma_div_plus (y * 2 + 1664 - 3329) 1 3329;
        Math.small_div (y * 2 + 1664 - 3329) 3329
      end else begin
        Math.lemma_mod_sub (1665 + x) q 1;
        Math.small_mod (1665 + x - q) q;
        assert (y == 1665 + x - q);
        Math.lemma_div_plus (y * 2 + 1664 - 3329) 1 3329;
        Math.small_div (y * 2 + 1664 - 3329) 3329
      end
    end

let msg_round_trip (m: Seq.lseq S8.t 32) (f: poly)
  : Lemma (requires noise_ok f)
          (ensures byte_encode 1 (poly_compress 1 (poly_add (msg_poly m) f)) == m)
  = let bits = widen (byte_decode 1 m) in
    let w = poly_add (msg_poly m) f in
    introduce forall (i: nat { i < n }). Seq.index (poly_compress 1 w) i == Seq.index bits i
    with begin
      byte_decode_bound 1 m i;
      assert_norm (pow2 1 == 2);
      poly_decompress_index 1 bits i;
      poly_compress_index 1 w i;
      compress_1_decode (Seq.index bits i) (Seq.index f i)
    end;
    Seq.lemma_eq_intro (poly_compress 1 w) bits;
    byte_encode_decode 1 m

(** {2 Sequences} *)

let slice_append_l (#a: Type) (x y: Seq.seq a)
  : Lemma (Seq.slice (Seq.append x y) 0 (Seq.length x) == x)
  = Seq.lemma_eq_intro (Seq.slice (Seq.append x y) 0 (Seq.length x)) x

let slice_append_r (#a: Type) (x y: Seq.seq a)
  : Lemma (Seq.slice (Seq.append x y) (Seq.length x) (Seq.length x + Seq.length y) == y)
  = Seq.lemma_eq_intro (Seq.slice (Seq.append x y) (Seq.length x) (Seq.length x + Seq.length y)) y

(** {2 What travels on the wire} *)

let kpke_keygen_eq (p: params) (d: Seq.lseq S8.t 32)
  : Lemma (fst (kpke_keygen p d) == Seq.append (vec_encode_12 (kg_t p d)) (kg_rho p d) /\
           snd (kpke_keygen p d) == vec_encode_12 (vec_ntt (kg_s p d)))
  = ()

(** The encryption key decodes to [t-hat] and [rho]. *)
let ek_parts (p: params) (d: Seq.lseq S8.t 32)
  : Lemma (let ek = fst (kpke_keygen p d) in
           vec_decode 12 p.k (Seq.slice ek 0 (p.k * (32 * 12))) == kg_t p d /\
           Seq.slice ek (p.k * (32 * 12)) (ek_len p) == kg_rho p d)
  = kpke_keygen_eq p d;
    slice_append_l (vec_encode_12 (kg_t p d)) (kg_rho p d);
    slice_append_r (vec_encode_12 (kg_t p d)) (kg_rho p d);
    vec_decode_encode_12 (kg_t p d)

let ct (p: params) (d m r: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t (ct_len p))
  = Seq.append (vec_encode p.du p.k (vec_compress p.du (enc_u p d r)))
               (byte_encode p.dv (poly_compress p.dv (enc_v p d m r)))

let kpke_encrypt_eq (p: params) (d m r: Seq.lseq S8.t 32)
  : Lemma (kpke_encrypt p (fst (kpke_keygen p d)) m r == ct p d m r)
  = ek_parts p d

(** The polynomial [kpke_decrypt] rounds. *)
let decrypt_w (p: params) (dk: Seq.lseq S8.t (dk_pke_len p)) (c: Seq.lseq S8.t (ct_len p))
  : GTot poly
  = let c1 = Seq.slice c 0 (p.k * (32 * p.du)) in
    let c2 = Seq.slice c (p.k * (32 * p.du)) (ct_len p) in
    let u = vec_decompress p.du p.k (widen (vec_decode p.du p.k c1)) in
    let v = poly_decompress p.dv (widen (byte_decode p.dv c2)) in
    let s = vec_decode 12 p.k dk in
    poly_sub v (intt (dot s (vec_ntt u)))

let kpke_decrypt_w (p: params) (dk: Seq.lseq S8.t (dk_pke_len p)) (c: Seq.lseq S8.t (ct_len p))
  : Lemma (kpke_decrypt p dk c == byte_encode 1 (poly_compress 1 (decrypt_w p dk c)))
  = ()

let compress_bound (d: pos { d <= 11 }) (#k: pos) (u: pvec k)
  : Lemma (forall (t: nat). t < k * n ==>
             Seq.index (vec_compress d u) t < pow2 d /\ Seq.index (vec_compress d u) t < q)
  = Math.pow2_le_compat 11 d;
    assert_norm (pow2 11 < q);
    introduce forall (t: nat). t < k * n ==>
      Seq.index (vec_compress d u) t < pow2 d /\ Seq.index (vec_compress d u) t < q
    with introduce _ ==> _ with begin
      div_lt t k n;
      Math.lemma_mult_le_right n (t / n + 1) k;
      vec_compress_at d u (t / n);
      Math.euclidean_division_definition t n;
      poly_compress_index d (vec_at u (t / n)) (t % n);
      assert (Seq.index (vec_compress d u) t ==
              Seq.index (flat_at k n (vec_compress d u) (t / n)) (t % n))
    end

let poly_compress_bound (d: pos { d <= 11 }) (f: poly)
  : Lemma (forall (i: nat). i < n ==>
             Seq.index (poly_compress d f) i < pow2 d /\ Seq.index (poly_compress d f) i < q)
  = Math.pow2_le_compat 11 d;
    assert_norm (pow2 11 < q);
    introduce forall (i: nat). i < n ==>
      Seq.index (poly_compress d f) i < pow2 d /\ Seq.index (poly_compress d f) i < q
    with introduce _ ==> _ with poly_compress_index d f i

(** Decryption sees [Decompress (Compress u)], [Decompress (Compress v)]
    and [s-hat]. *)
let decrypt_w_ct (p: params) (d m r: Seq.lseq S8.t 32)
  : Lemma (decrypt_w p (snd (kpke_keygen p d)) (ct p d m r) ==
           poly_sub (poly_decompress p.dv (poly_compress p.dv (enc_v p d m r)))
                    (intt (dot (vec_ntt (kg_s p d))
                               (vec_ntt (vec_decompress p.du p.k (vec_compress p.du (enc_u p d r)))))))
  = let cu = vec_compress p.du (enc_u p d r) in
    let cv = poly_compress p.dv (enc_v p d m r) in
    let c1 = vec_encode p.du p.k cu in
    let c2 = byte_encode p.dv cv in
    slice_append_l c1 c2;
    slice_append_r c1 c2;
    compress_bound p.du (enc_u p d r);
    vec_decode_encode p.du p.k cu;
    poly_compress_bound p.dv (enc_v p d m r);
    byte_decode_encode p.dv cv;
    kpke_keygen_eq p d;
    vec_decode_encode_12 (vec_ntt (kg_s p d))

(** {2 The algebra} *)

let gen_matrix_at (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32) (b: bool)
                  (i: nat { i < k }) (j: nat { j < k })
  : Lemma (mat_at (gen_matrix k rho b) i j ==
           (if b then sample_ntt (matrix_seed rho j i) else sample_ntt (matrix_seed rho i j)))
  = mat_at_flat (gen_matrix k rho b) i j;
    flat_at_of_fun_g (k * k) n (fun c ->
      div_lt c k k;
      let i = c / k in
      let j = c % k in
      if b then sample_ntt (matrix_seed rho j i)
      else sample_ntt (matrix_seed rho i j)) (i * k + j);
    coeff_pos k i j

let gen_matrix_transpose (k: pos { k <= 4 }) (rho: Seq.lseq S8.t 32)
  : Lemma (forall (i j: (l: nat { l < k })).
             mat_at (gen_matrix k rho true) i j == mat_at (gen_matrix k rho false) j i)
  = introduce forall (i j: (l: nat { l < k })).
      mat_at (gen_matrix k rho true) i j == mat_at (gen_matrix k rho false) j i
    with begin
      gen_matrix_at k rho true i j;
      gen_matrix_at k rho false j i
    end

let vec_add_assoc (#k: pos) (a b c: pvec k)
  : Lemma (vec_add (vec_add a b) c == vec_add a (vec_add b c))
  = introduce forall (t: nat { t < k * n }).
      Seq.index (vec_add (vec_add a b) c) t == Seq.index (vec_add a (vec_add b c)) t
    with add_assoc (Seq.index a t) (Seq.index b t) (Seq.index c t);
    Seq.lemma_eq_intro (vec_add (vec_add a b) c) (vec_add a (vec_add b c))

let add_sub_cancel (a b: zq) : Lemma (add a (sub b a) == b)
  = sub_is_add_neg b a;
    add_comm a (add b (neg a));
    add_assoc b (neg a) a;
    add_comm (neg a) a;
    add_neg a;
    add_zero b

let vec_add_sub (#k: pos) (u u': pvec k) : Lemma (vec_add u (vec_sub u' u) == u')
  = introduce forall (t: nat { t < k * n }). Seq.index (vec_add u (vec_sub u' u)) t == Seq.index u' t
    with add_sub_cancel (Seq.index u t) (Seq.index u' t);
    Seq.lemma_eq_intro (vec_add u (vec_sub u' u)) u'

let poly_add_sub (v v': poly) : Lemma (poly_add v (poly_sub v' v) == v')
  = introduce forall (i: nat { i < n }). Seq.index (poly_add v (poly_sub v' v)) i == Seq.index v' i
    with add_sub_cancel (Seq.index v i) (Seq.index v' i);
    Seq.lemma_eq_intro (poly_add v (poly_sub v' v)) v'

(** NTT-domain: [s-hat . NTT(u + du) = s-hat . (A^T y-hat) + s-hat . NTT(e1 + du)]. *)
let su_split (p: params) (d r: Seq.lseq S8.t 32)
  : Lemma (let x = mat_vec_mul (gen_matrix p.k (kg_rho p d) true) (vec_ntt (enc_y p r)) in
           let sh = vec_ntt (kg_s p d) in
           let up = vec_decompress p.du p.k (vec_compress p.du (enc_u p d r)) in
           intt (dot sh (vec_ntt up)) ==
           poly_add (intt (dot sh x))
                    (rq_dot (kg_s p d) (vec_add (enc_e1 p r) (delta_u p d r))))
  = let x = mat_vec_mul (gen_matrix p.k (kg_rho p d) true) (vec_ntt (enc_y p r)) in
    let sh = vec_ntt (kg_s p d) in
    let u = enc_u p d r in
    let up = vec_decompress p.du p.k (vec_compress p.du u) in
    let z = vec_add (enc_e1 p r) (delta_u p d r) in
    vec_add_sub u up;
    vec_add_assoc (vec_intt x) (enc_e1 p r) (delta_u p d r);
    vec_ntt_add (vec_intt x) z;
    vec_ntt_intt x;
    dot_add_r sh x (vec_ntt z);
    intt_add (dot sh x) (dot sh (vec_ntt z));
    rq_dot_ntt (kg_s p d) z

(** NTT-domain: [t-hat . y-hat = s-hat . (A^T y-hat) + e-hat . y-hat]. *)
let ty_split (p: params) (d r: Seq.lseq S8.t 32)
  : Lemma (let x = mat_vec_mul (gen_matrix p.k (kg_rho p d) true) (vec_ntt (enc_y p r)) in
           let sh = vec_ntt (kg_s p d) in
           intt (dot (kg_t p d) (vec_ntt (enc_y p r))) ==
           poly_add (intt (dot sh x)) (rq_dot (kg_e p d) (enc_y p r)))
  = let a = gen_matrix p.k (kg_rho p d) false in
    let at = gen_matrix p.k (kg_rho p d) true in
    let sh = vec_ntt (kg_s p d) in
    let yh = vec_ntt (enc_y p r) in
    dot_add_l (mat_vec_mul a sh) (vec_ntt (kg_e p d)) yh;
    gen_matrix_transpose p.k (kg_rho p d);
    dot_mat_vec_transpose a at sh yh;
    intt_add (dot sh (mat_vec_mul at yh)) (dot (vec_ntt (kg_e p d)) yh);
    rq_dot_ntt (kg_e p d) (enc_y p r)

let w_identity (pp ee e2 mu dv np ns: zq)
  : Lemma (add (add (add (add (add pp ee) e2) mu) dv) (add np ns) ==
           add (add pp np) (add mu (add (add (add ee ns) e2) dv)))
  = assert (add (add (add (add (add pp ee) e2) mu) dv) (add np ns) ==
            add (add pp np) (add mu (add (add (add ee ns) e2) dv))) by (zring ())

let w_coeff (pp ee e2 mu dv ss: zq)
  : Lemma (sub (add (add (add (add pp ee) e2) mu) dv) (add pp ss) ==
           add mu (add (add (sub ee ss) e2) dv))
  = sub_is_add_neg (add (add (add (add pp ee) e2) mu) dv) (add pp ss);
    neg_add pp ss;
    sub_is_add_neg ee ss;
    w_identity pp ee e2 mu dv (neg pp) (neg ss);
    add_neg pp;
    add_comm 0 (add mu (add (add (add ee (neg ss)) e2) dv));
    add_zero (add mu (add (add (add ee (neg ss)) e2) dv))

(** [w = mu + noise]: what decryption rounds is the message plus
    [kpke_noise]. *)
let decrypt_w_noise (p: params) (d m r: Seq.lseq S8.t 32)
  : Lemma (decrypt_w p (snd (kpke_keygen p d)) (kpke_encrypt p (fst (kpke_keygen p d)) m r) ==
           poly_add (msg_poly m) (kpke_noise p d m r))
  = let x = mat_vec_mul (gen_matrix p.k (kg_rho p d) true) (vec_ntt (enc_y p r)) in
    let sh = vec_ntt (kg_s p d) in
    let pp = intt (dot sh x) in
    let ee = rq_dot (kg_e p d) (enc_y p r) in
    let ss = rq_dot (kg_s p d) (vec_add (enc_e1 p r) (delta_u p d r)) in
    let v = enc_v p d m r in
    let vp = poly_decompress p.dv (poly_compress p.dv v) in
    kpke_encrypt_eq p d m r;
    decrypt_w_ct p d m r;
    su_split p d r;
    ty_split p d r;
    poly_add_sub v vp;
    let lhs = poly_sub vp (poly_add pp ss) in
    let rhs = poly_add (msg_poly m) (kpke_noise p d m r) in
    introduce forall (i: nat { i < n }). Seq.index lhs i == Seq.index rhs i
    with w_coeff (Seq.index pp i) (Seq.index ee i) (Seq.index (enc_e2 p r) i)
                 (Seq.index (msg_poly m) i) (Seq.index (delta_v p d m r) i) (Seq.index ss i);
    Seq.lemma_eq_intro lhs rhs

(** {1 K-PKE is correct} *)

let kpke_correct (p: params) (d m r: Seq.lseq S8.t 32)
  : Lemma (requires noise_ok (kpke_noise p d m r))
          (ensures (let ek, dk = kpke_keygen p d in kpke_decrypt p dk (kpke_encrypt p ek m r) == m))
  = let ek = fst (kpke_keygen p d) in
    let dk = snd (kpke_keygen p d) in
    kpke_decrypt_w p dk (kpke_encrypt p ek m r);
    decrypt_w_noise p d m r;
    msg_round_trip m (kpke_noise p d m r)

(** {1 ML-KEM is correct} *)

(** The K-PKE coins [encaps] derives: the second half of [G(m || H(ek))]. *)
let encaps_coins (p: params) (ek: Seq.lseq S8.t (ek_len p)) (m: Seq.lseq S8.t 32)
  : GTot (Seq.lseq S8.t 32)
  = Seq.slice (hash_g (Seq.append m (hash_h ek))) 32 64

(** The decapsulation key is laid out as [decaps] reads it. *)
let dk_parts (p: params) (d z: Seq.lseq S8.t 32)
  : Lemma (let ek, dk = keygen p d z in
           Seq.slice dk 0 (dk_pke_len p) == snd (kpke_keygen p d) /\
           Seq.slice dk (dk_pke_len p) (dk_pke_len p + ek_len p) == ek /\
           Seq.slice dk (dk_pke_len p + ek_len p) (dk_pke_len p + ek_len p + 32) == hash_h ek /\
           Seq.slice dk (dk_pke_len p + ek_len p + 32) (dk_len p) == z)
  = let ek, dkp = kpke_keygen p d in
    let dk = snd (keygen p d z) in
    let o1 = dk_pke_len p in
    let o2 = o1 + ek_len p in
    let o3 = o2 + 32 in
    Seq.lemma_eq_intro (Seq.slice dk 0 o1) dkp;
    Seq.lemma_eq_intro (Seq.slice dk o1 o2) ek;
    Seq.lemma_eq_intro (Seq.slice dk o2 o3) (hash_h ek);
    Seq.lemma_eq_intro (Seq.slice dk o3 (dk_len p)) z

let mlkem_correct (p: params) (d z m: Seq.lseq S8.t 32)
  : Lemma (requires noise_ok (kpke_noise p d m (encaps_coins p (fst (keygen p d z)) m)))
          (ensures (let ek, dk = keygen p d z in
                    let k, c = encaps p ek m in
                    decaps p dk c == k))
  = let ek = fst (keygen p d z) in
    let dk = snd (keygen p d z) in
    let r = encaps_coins p ek m in
    let c = kpke_encrypt p ek m r in
    dk_parts p d z;
    kpke_correct p d m r;
    assert (Seq.equal c c)

(** {2 Key generation passes the input checks}

    The keys [keygen] produces pass both of FIPS 203's section 7 checks. *)

let keygen_ek_valid (p: params) (d z: Seq.lseq S8.t 32) : Lemma (ek_valid p (fst (keygen p d z)))
  = let ek = fst (kpke_keygen p d) in
    kpke_keygen_eq p d;
    slice_append_l (vec_encode_12 (kg_t p d)) (kg_rho p d);
    vec_decode_encode_12 (kg_t p d)

let keygen_dk_valid (p: params) (d z: Seq.lseq S8.t 32) : Lemma (dk_valid p (snd (keygen p d z)))
  = dk_parts p d z

#pop-options
