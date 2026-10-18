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

(** FrodoKEM decapsulates correctly whenever the noise is small.

    With [B = A S + E] from key generation and [B' = S' A + E'],
    [V = S' B + E'' + encode(mu)] from encapsulation, decryption computes

    [M = V - B' S = encode(mu) + (S' E + E'' - E' S)]

    because the two copies of [S' A S] cancel.  The matrix in parentheses
    is [noise], a function of the five small matrices only, and [noise_ok]
    says that each of its entries, as a centered representative modulo
    [q = 2^logq], is less than [q / 2^(bits + 1)] in absolute value: the
    condition under which rounding recovers each [bits]-wide field
    ({!Spec.Frodo.Encode.Lemmas}).  Whether that condition holds with
    overwhelming probability is a separate question, not addressed here; the
    theorems below are deterministic.

    - [pke_correct]: decryption of the matrices that [enc_ct] packs, after
      they have been through [pack]/[unpack], decodes to [mu].  Arithmetic is
      modulo [2^16] but [pack] keeps only [logq] bits, so everything is
      proved modulo [q], which divides [2^16]; and over [int] the
      cancellation is linearity of finite sums and an exchange of a double
      sum ({!Spec.Frodo.Matrix.Lemmas}).  S is stored transposed, as in the
      specification: the products with S are [mul_t].
    - [kem_correct]: for [(pk, sk) = keypair p coins] and
      [(ct, ss) = enc p mu pk], if [noise_ok] holds for the matrices that
      key generation and encapsulation sample, then [dec p ct sk == ss].
      Decapsulation reads [s], [pk], S and [pkh] back out of [sk], recovers
      [mu] by [pke_correct], hence derives the same seeds, re-encrypts to the
      same matrices modulo [q], and so selects the real key.

    These are statements about [Spec.Frodo.keypair], [enc] and [dec]
    themselves, which are what [Hacl.Frodo.KEM] is proved to implement. *)
module Spec.Frodo.Correctness

open Spec.Frodo.Params
open Spec.Frodo

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module Math = FStar.Math.Lemmas
module M = Spec.Frodo.Matrix
module ML = Spec.Frodo.Matrix.Lemmas
module PL = Spec.Frodo.Pack.Lemmas
module EL = Spec.Frodo.Encode.Lemmas
module SEM = FStar.IndefiniteDescription

(** {2 The noise} *)

(** [S' E + E'' - E' S], with S given transposed as [st]. *)
let noise (p: params) (st: M.matrix nbar (n p)) (e: M.matrix (n p) nbar)
          (sp ep: M.matrix nbar (n p)) (epp: M.matrix nbar nbar)
  : M.matrix nbar nbar
  = M.sub nbar nbar (M.add nbar nbar (M.mul nbar (n p) nbar sp e) epp)
                    (M.mul_t nbar (n p) nbar ep st)

(** Every entry of the noise is less than [q / 2^(bits + 1)] in absolute
    value, as a centered representative modulo [q = 2^logq]. *)
let noise_ok (p: params) (st: M.matrix nbar (n p)) (e: M.matrix (n p) nbar)
             (sp ep: M.matrix nbar (n p)) (epp: M.matrix nbar nbar)
  : GTot prop
  = forall (i j: nat). i < nbar /\ j < nbar ==>
      abs (EL.centered (pow2 (logq p)) (S16.v (M.get nbar nbar (noise p st e sp ep epp) i j)))
        < pow2 (logq p - bits p - 1)

(** {2 The public-key encryption scheme inside the KEM}

    The matrices as [keypair], [enc_ct] and [dec] compute them. *)

let pke_b (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
          (e: M.matrix (n p) nbar) : M.matrix (n p) nbar
  = M.add (n p) nbar (M.mul_t (n p) (n p) nbar a st) e

let pke_bp (p: params) (a: M.matrix (n p) (n p)) (sp ep: M.matrix nbar (n p))
  : M.matrix nbar (n p)
  = M.add nbar (n p) (M.mul nbar (n p) (n p) sp a) ep

let pke_v (p: params) (bm: M.matrix (n p) nbar) (sp: M.matrix nbar (n p))
          (epp: M.matrix nbar nbar) (mu: Seq.lseq S8.t (bytes_mu p))
  : GTot (M.matrix nbar nbar)
  = M.add nbar nbar (M.add nbar nbar (M.mul nbar (n p) nbar sp bm) epp) (key_encode p mu)

let pke_m (p: params) (bp: M.matrix nbar (n p)) (c: M.matrix nbar nbar)
          (st: M.matrix nbar (n p))
  : M.matrix nbar nbar
  = M.sub nbar nbar c (M.mul_t nbar (n p) nbar bp st)

(** What the receiver gets out of a packed matrix. *)
let unpacked_n (p: params) (r c: nat) (m: M.matrix r c { r * c == n p * nbar })
  : GTot (M.matrix r c)
  = as_matrix r c (unpack_n p (pack_n p m))

let unpacked_8 (p: params) (m: M.matrix nbar nbar) : GTot (M.matrix nbar nbar) =
  unpack_8 p (pack_8 p m)

#push-options "--fuel 0 --ifuel 0"

unfold let modq (p: params) : pos = pow2 (logq p)

let unpacked_n_get (p: params) (r c: nat) (m: M.matrix r c { r * c == n p * nbar })
                   (i: nat { i < r }) (j: nat { j < c })
  : Lemma (ML.vat r c (unpacked_n p r c m) i j == ML.vat r c m i j % modq p)
  = M.index_bound r c i j;
    PL.unpack_pack_n p m (i * c + j)

let unpacked_8_get (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar }) (j: nat { j < nbar })
  : Lemma (ML.vat nbar nbar (unpacked_8 p m) i j == ML.vat nbar nbar m i j % modq p)
  = M.index_bound nbar nbar i j;
    PL.unpack_pack_8 p m (i * nbar + j)

(** {2 Congruences modulo [q]} *)

let mod16 (p: params) (x: int) : Lemma ((x % pow2 16) % modq p == x % modq p)
  = ML.mod_pow2_16 x (logq p)

let add_cong (q: pos) (a a' b b': int)
  : Lemma (requires a % q == a' % q /\ b % q == b' % q) (ensures (a + b) % q == (a' + b') % q)
  = Math.modulo_distributivity a b q;
    Math.modulo_distributivity a' b' q

let sub_cong (q: pos) (a a' b b': int)
  : Lemma (requires a % q == a' % q /\ b % q == b' % q) (ensures (a - b) % q == (a' - b') % q)
  = Math.lemma_mod_sub_distr a b q;
    Math.lemma_mod_sub_distr a' b' q;
    Math.lemma_mod_plus_distr_l a (- (b % q)) q;
    Math.lemma_mod_plus_distr_l a' (- (b' % q)) q

let mul_cong (q: pos) (a a' z: int)
  : Lemma (requires a % q == a' % q) (ensures (z * a) % q == (z * a') % q)
  = Math.lemma_mod_mul_distr_r z a q;
    Math.lemma_mod_mul_distr_r z a' q

(** {2 The cancellation, one entry at a time}

    Fix an entry [(i, j)].  Both [S' (A S)] and [(S' A) S] are the double
    sum of [sp.(i,l) * a.(l,t) * st.(j,t)], once summed over [t] first
    ([g2]) and once over [l] first ([g1]). *)

let h2 (p: params) (a: M.matrix (n p) (n p)) (st sp: M.matrix nbar (n p)) (i j: nat)
       (l t: nat) : GTot int
  = ML.tterm (n p) (n p) nbar a st l j t * ML.vat nbar (n p) sp i l

let h1 (p: params) (a: M.matrix (n p) (n p)) (st sp: M.matrix nbar (n p)) (i j: nat)
       (l t: nat) : GTot int
  = ML.mterm nbar (n p) (n p) sp a i l t * ML.vat nbar (n p) st j l

let g2 (p: params) (a: M.matrix (n p) (n p)) (st sp: M.matrix nbar (n p)) (i j: nat)
       (l: nat) : GTot int
  = ML.isum (n p) (h2 p a st sp i j l)

let g1 (p: params) (a: M.matrix (n p) (n p)) (st sp: M.matrix nbar (n p)) (i j: nat)
       (l: nat) : GTot int
  = ML.isum (n p) (h1 p a st sp i j l)

let mul3 (x y z: int) : Lemma ((x * y) * z == (y * z) * x)
  = Math.paren_mul_right x y z;
    Math.swap_mul x (y * z)

let swap (p: params) (a: M.matrix (n p) (n p)) (st sp: M.matrix nbar (n p)) (i j: nat)
  : Lemma (ML.isum (n p) (g2 p a st sp i j) == ML.isum (n p) (g1 p a st sp i j))
  = introduce forall (x y: nat). h1 p a st sp i j y x == h2 p a st sp i j x y
    with mul3 (ML.vat nbar (n p) sp i x) (ML.vat (n p) (n p) a x y) (ML.vat nbar (n p) st j y);
    ML.sum_swap (n p) (n p) (h2 p a st sp i j) (h1 p a st sp i j)
      (g2 p a st sp i j) (g1 p a st sp i j)

(** The summand of [S' B], against that of [S' (A S) + S' E]. *)
let v_term_sum (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
               (e: M.matrix (n p) nbar) (sp: M.matrix nbar (n p))
               (i j: nat) (l: nat { l < n p })
  : Lemma (j < nbar ==>
           ML.mterm nbar (n p) nbar sp (unpacked_n p (n p) nbar (pke_b p a st e)) i j l % modq p ==
           (g2 p a st sp i j l + ML.mterm nbar (n p) nbar sp e i j l) % modq p)
  = if j < nbar then begin
      let q = modq p in
      let b = pke_b p a st e in
      let s = ML.isum (n p) (ML.tterm (n p) (n p) nbar a st l j) in
      let spl = ML.vat nbar (n p) sp i l in
      let el = ML.vat (n p) nbar e l j in
      unpacked_n_get p (n p) nbar b l j;
      ML.add_get (n p) nbar (M.mul_t (n p) (n p) nbar a st) e l j;
      ML.mul_t_get (n p) (n p) nbar a st l j;
      Math.lemma_mod_twice (ML.vat (n p) nbar b l j) q;
      mod16 p (ML.vat (n p) nbar b l j + 0);
      mod16 p (ML.vat (n p) nbar (M.mul_t (n p) (n p) nbar a st) l j + el);
      mod16 p s;
      add_cong q (ML.vat (n p) nbar (M.mul_t (n p) (n p) nbar a st) l j) s el el;
      mul_cong q (ML.vat (n p) nbar (unpacked_n p (n p) nbar b) l j) (s + el) spl;
      ML.sum_scale (n p) spl (ML.tterm (n p) (n p) nbar a st l j) (h2 p a st sp i j l);
      Math.distributivity_add_right spl s el;
      Math.swap_mul spl s
    end

(** The summand of [B' S], against that of [(S' A) S + E' S]. *)
let bp_term_sum (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
                (sp ep: M.matrix nbar (n p)) (i j: nat) (l: nat { l < n p })
  : Lemma (i < nbar ==>
           ML.tterm nbar (n p) nbar (unpacked_n p nbar (n p) (pke_bp p a sp ep)) st i j l % modq p ==
           (g1 p a st sp i j l + ML.tterm nbar (n p) nbar ep st i j l) % modq p)
  = if i < nbar then begin
      let q = modq p in
      let bp = pke_bp p a sp ep in
      let s = ML.isum (n p) (ML.mterm nbar (n p) (n p) sp a i l) in
      let stl = ML.vat nbar (n p) st j l in
      let epl = ML.vat nbar (n p) ep i l in
      unpacked_n_get p nbar (n p) bp i l;
      ML.add_get nbar (n p) (M.mul nbar (n p) (n p) sp a) ep i l;
      ML.mul_get nbar (n p) (n p) sp a i l;
      mod16 p (ML.vat nbar (n p) (M.mul nbar (n p) (n p) sp a) i l + epl);
      mod16 p s;
      add_cong q (ML.vat nbar (n p) (M.mul nbar (n p) (n p) sp a) i l) s epl epl;
      Math.lemma_mod_twice (ML.vat nbar (n p) bp i l) q;
      mul_cong q (ML.vat nbar (n p) (unpacked_n p nbar (n p) bp) i l) (s + epl) stl;
      Math.swap_mul stl (ML.vat nbar (n p) (unpacked_n p nbar (n p) bp) i l);
      Math.swap_mul stl (s + epl);
      ML.sum_scale (n p) stl (ML.mterm nbar (n p) (n p) sp a i l) (h1 p a st sp i j l);
      Math.distributivity_add_left s epl stl
    end

let a4 (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
       (e: M.matrix (n p) nbar) (sp: M.matrix nbar (n p)) (i j: nat) (l: nat) : GTot int
  = g2 p a st sp i j l + ML.mterm nbar (n p) nbar sp e i j l

let a5 (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
       (sp ep: M.matrix nbar (n p)) (i j: nat) (l: nat) : GTot int
  = g1 p a st sp i j l + ML.tterm nbar (n p) nbar ep st i j l

(** [S' B = S' (A S) + S' E], entry [(i, j)], modulo [q]. *)
let v_sum (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
          (e: M.matrix (n p) nbar) (sp: M.matrix nbar (n p)) (i: nat) (j: nat { j < nbar })
  : Lemma (ML.isum (n p) (ML.mterm nbar (n p) nbar sp (unpacked_n p (n p) nbar (pke_b p a st e)) i j)
             % modq p ==
           (ML.isum (n p) (g2 p a st sp i j) + ML.isum (n p) (ML.mterm nbar (n p) nbar sp e i j))
             % modq p)
  = introduce forall (l: nat). l < n p ==>
      ML.mterm nbar (n p) nbar sp (unpacked_n p (n p) nbar (pke_b p a st e)) i j l % modq p ==
      a4 p a st e sp i j l % modq p
    with introduce _ ==> _ with v_term_sum p a st e sp i j l;
    ML.sum_mod (n p) (modq p)
      (ML.mterm nbar (n p) nbar sp (unpacked_n p (n p) nbar (pke_b p a st e)) i j)
      (a4 p a st e sp i j);
    ML.sum_add (n p) (g2 p a st sp i j) (ML.mterm nbar (n p) nbar sp e i j) (a4 p a st e sp i j)

(** [B' S = (S' A) S + E' S], entry [(i, j)], modulo [q]. *)
let bp_sum (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
           (sp ep: M.matrix nbar (n p)) (i: nat { i < nbar }) (j: nat)
  : Lemma (ML.isum (n p) (ML.tterm nbar (n p) nbar (unpacked_n p nbar (n p) (pke_bp p a sp ep)) st i j)
             % modq p ==
           (ML.isum (n p) (g1 p a st sp i j) + ML.isum (n p) (ML.tterm nbar (n p) nbar ep st i j))
             % modq p)
  = introduce forall (l: nat). l < n p ==>
      ML.tterm nbar (n p) nbar (unpacked_n p nbar (n p) (pke_bp p a sp ep)) st i j l % modq p ==
      a5 p a st sp ep i j l % modq p
    with introduce _ ==> _ with bp_term_sum p a st sp ep i j l;
    ML.sum_mod (n p) (modq p)
      (ML.tterm nbar (n p) nbar (unpacked_n p nbar (n p) (pke_bp p a sp ep)) st i j)
      (a5 p a st sp ep i j);
    ML.sum_add (n p) (g1 p a st sp i j) (ML.tterm nbar (n p) nbar ep st i j) (a5 p a st sp ep i j)

(** The noise entry, modulo [q], as integer sums. *)
let noise_sum (p: params) (st: M.matrix nbar (n p)) (e: M.matrix (n p) nbar)
              (sp ep: M.matrix nbar (n p)) (epp: M.matrix nbar nbar)
              (i: nat { i < nbar }) (j: nat { j < nbar })
  : Lemma (ML.vat nbar nbar (noise p st e sp ep epp) i j % modq p ==
           (ML.isum (n p) (ML.mterm nbar (n p) nbar sp e i j) + ML.vat nbar nbar epp i j -
            ML.isum (n p) (ML.tterm nbar (n p) nbar ep st i j)) % modq p)
  = let q = modq p in
    let se = ML.isum (n p) (ML.mterm nbar (n p) nbar sp e i j) in
    let es = ML.isum (n p) (ML.tterm nbar (n p) nbar ep st i j) in
    let x = M.add nbar nbar (M.mul nbar (n p) nbar sp e) epp in
    let y = M.mul_t nbar (n p) nbar ep st in
    let ev = ML.vat nbar nbar epp i j in
    ML.sub_get nbar nbar x y i j;
    ML.add_get nbar nbar (M.mul nbar (n p) nbar sp e) epp i j;
    ML.mul_get nbar (n p) nbar sp e i j;
    ML.mul_t_get nbar (n p) nbar ep st i j;
    mod16 p (ML.vat nbar nbar x i j - ML.vat nbar nbar y i j);
    mod16 p (ML.vat nbar nbar (M.mul nbar (n p) nbar sp e) i j + ev);
    mod16 p se;
    mod16 p es;
    add_cong q (ML.vat nbar nbar (M.mul nbar (n p) nbar sp e) i j) se ev ev;
    sub_cong q (ML.vat nbar nbar x i j) (se + ev) (ML.vat nbar nbar y i j) es

(** The decrypted entry, modulo [q], as integer sums. *)
let m_sum (p: params) (bm: M.matrix (n p) nbar) (bpd: M.matrix nbar (n p))
          (st sp: M.matrix nbar (n p)) (epp: M.matrix nbar nbar)
          (mu: Seq.lseq S8.t (bytes_mu p)) (i: nat { i < nbar }) (j: nat { j < nbar })
  : Lemma (ML.vat nbar nbar (pke_m p bpd (unpacked_8 p (pke_v p bm sp epp mu)) st) i j % modq p ==
           (ML.isum (n p) (ML.mterm nbar (n p) nbar sp bm i j) + ML.vat nbar nbar epp i j +
            ML.vat nbar nbar (key_encode p mu) i j -
            ML.isum (n p) (ML.tterm nbar (n p) nbar bpd st i j)) % modq p)
  = let q = modq p in
    let v = pke_v p bm sp epp mu in
    let c = unpacked_8 p v in
    let sb = ML.isum (n p) (ML.mterm nbar (n p) nbar sp bm i j) in
    let bs = ML.isum (n p) (ML.tterm nbar (n p) nbar bpd st i j) in
    let r = M.mul nbar (n p) nbar sp bm in
    let x = M.add nbar nbar r epp in
    let y = M.mul_t nbar (n p) nbar bpd st in
    let ev = ML.vat nbar nbar epp i j in
    let kv = ML.vat nbar nbar (key_encode p mu) i j in
    ML.sub_get nbar nbar c y i j;
    unpacked_8_get p v i j;
    ML.add_get nbar nbar x (key_encode p mu) i j;
    ML.add_get nbar nbar r epp i j;
    ML.mul_get nbar (n p) nbar sp bm i j;
    ML.mul_t_get nbar (n p) nbar bpd st i j;
    mod16 p (ML.vat nbar nbar c i j - ML.vat nbar nbar y i j);
    mod16 p (ML.vat nbar nbar x i j + kv);
    mod16 p (ML.vat nbar nbar r i j + ev);
    mod16 p sb;
    mod16 p bs;
    Math.lemma_mod_twice (ML.vat nbar nbar v i j) q;
    add_cong q (ML.vat nbar nbar r i j) sb ev ev;
    add_cong q (ML.vat nbar nbar x i j) (sb + ev) kv kv;
    sub_cong q (ML.vat nbar nbar c i j) (sb + ev + kv) (ML.vat nbar nbar y i j) bs

(** Entry [(i, j)] of the decrypted matrix is the encoding plus the noise,
    modulo [q]. *)
let pke_entry (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
              (e: M.matrix (n p) nbar) (sp ep: M.matrix nbar (n p)) (epp: M.matrix nbar nbar)
              (mu: Seq.lseq S8.t (bytes_mu p)) (i: nat { i < nbar }) (j: nat { j < nbar })
  : Lemma (let bm = unpacked_n p (n p) nbar (pke_b p a st e) in
           let bpd = unpacked_n p nbar (n p) (pke_bp p a sp ep) in
           let m = pke_m p bpd (unpacked_8 p (pke_v p bm sp epp mu)) st in
           S16.v (M.get nbar nbar m i j) % modq p ==
           (S16.v (M.get nbar nbar (key_encode p mu) i j) +
            S16.v (M.get nbar nbar (noise p st e sp ep epp) i j)) % modq p)
  = let q = modq p in
    let bm = unpacked_n p (n p) nbar (pke_b p a st e) in
    let bpd = unpacked_n p nbar (n p) (pke_bp p a sp ep) in
    let sb = ML.isum (n p) (ML.mterm nbar (n p) nbar sp bm i j) in
    let bs = ML.isum (n p) (ML.tterm nbar (n p) nbar bpd st i j) in
    let gg2 = ML.isum (n p) (g2 p a st sp i j) in
    let gg1 = ML.isum (n p) (g1 p a st sp i j) in
    let se = ML.isum (n p) (ML.mterm nbar (n p) nbar sp e i j) in
    let es = ML.isum (n p) (ML.tterm nbar (n p) nbar ep st i j) in
    let ev = ML.vat nbar nbar epp i j in
    let kv = ML.vat nbar nbar (key_encode p mu) i j in
    let nv = ML.vat nbar nbar (noise p st e sp ep epp) i j in
    m_sum p bm bpd st sp epp mu i j;
    v_sum p a st e sp i j;
    bp_sum p a st sp ep i j;
    swap p a st sp i j;
    noise_sum p st e sp ep epp i j;
    add_cong q sb (gg2 + se) ev ev;
    add_cong q (sb + ev) (gg2 + se + ev) kv kv;
    sub_cong q (sb + ev + kv) (gg2 + se + ev + kv) bs (gg1 + es);
    add_cong q kv kv nv (se + ev - es)

(** {2 Correctness of the encryption scheme} *)

let pke_correct (p: params) (a: M.matrix (n p) (n p)) (st: M.matrix nbar (n p))
                (e: M.matrix (n p) nbar) (sp ep: M.matrix nbar (n p)) (epp: M.matrix nbar nbar)
                (mu: Seq.lseq S8.t (bytes_mu p))
  : Lemma (requires noise_ok p st e sp ep epp)
          (ensures (let bm = unpacked_n p (n p) nbar (pke_b p a st e) in
                    let bpd = unpacked_n p nbar (n p) (pke_bp p a sp ep) in
                    key_decode p (pke_m p bpd (unpacked_8 p (pke_v p bm sp epp mu)) st) == mu))
  = let bm = unpacked_n p (n p) nbar (pke_b p a st e) in
    let bpd = unpacked_n p nbar (n p) (pke_bp p a sp ep) in
    let m = pke_m p bpd (unpacked_8 p (pke_v p bm sp epp mu)) st in
    let nz = noise p st e sp ep epp in
    introduce forall (i k: nat). i < nbar /\ k < nbar ==>
                EL.small p (M.get nbar nbar nz i k) /\
                S16.v (M.get nbar nbar m i k) % pow2 (logq p) ==
                (S16.v (M.get nbar nbar (key_encode p mu) i k) +
                 S16.v (M.get nbar nbar nz i k)) % pow2 (logq p)
    with introduce _ ==> _ with pke_entry p a st e sp ep epp mu i k;
    EL.key_decode_noisy p mu m nz

(** {2 Re-encryption agrees modulo [q]} *)

let mod_pow2_unpacked_n (p: params) (r: nat) (c: pos) (m: M.matrix r c { r * c == n p * nbar })
  : Lemma (M.mod_pow2 r c p.logq (unpacked_n p r c m) == M.mod_pow2 r c p.logq m)
  = introduce forall (t: nat). t < r * c ==>
                Seq.index (M.mod_pow2 r c p.logq (unpacked_n p r c m)) t ==
                Seq.index (M.mod_pow2 r c p.logq m) t
    with introduce _ ==> _ with begin
      M.mod_pow2_index r c p.logq (unpacked_n p r c m) t;
      M.mod_pow2_index r c p.logq m t;
      S16.logand_mask_low (Seq.index (unpacked_n p r c m) t) p.logq;
      S16.logand_mask_low (Seq.index m t) p.logq;
      PL.unpack_pack_n p m t;
      Math.lemma_mod_twice (S16.v (Seq.index m t)) (modq p)
    end;
    Seq.lemma_eq_intro (M.mod_pow2 r c p.logq (unpacked_n p r c m)) (M.mod_pow2 r c p.logq m)

let mod_pow2_unpacked_8 (p: params) (m: M.matrix nbar nbar)
  : Lemma (M.mod_pow2 nbar nbar p.logq (unpacked_8 p m) == M.mod_pow2 nbar nbar p.logq m)
  = introduce forall (t: nat). t < nbar * nbar ==>
                Seq.index (M.mod_pow2 nbar nbar p.logq (unpacked_8 p m)) t ==
                Seq.index (M.mod_pow2 nbar nbar p.logq m) t
    with introduce _ ==> _ with begin
      M.mod_pow2_index nbar nbar p.logq (unpacked_8 p m) t;
      M.mod_pow2_index nbar nbar p.logq m t;
      S16.logand_mask_low (Seq.index (unpacked_8 p m) t) p.logq;
      S16.logand_mask_low (Seq.index m t) p.logq;
      PL.unpack_pack_8 p m t;
      Math.lemma_mod_twice (S16.v (Seq.index m t)) (modq p)
    end;
    Seq.lemma_eq_intro (M.mod_pow2 nbar nbar p.logq (unpacked_8 p m)) (M.mod_pow2 nbar nbar p.logq m)

(** {2 The randomness}

    Named, so that the hypothesis of [kem_correct] can refer to the
    matrices [keypair] and [enc] sample. *)

let kg_s (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
  : Seq.lseq S8.t (crypto_bytes p)
  = Seq.slice coins 0 (crypto_bytes p)

let kg_seed_a (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
  : Seq.lseq S8.t bytes_seed_a
  = shake p (Seq.slice coins (2 * crypto_bytes p) (2 * crypto_bytes p + bytes_seed_a)) bytes_seed_a

let kg_r (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
  : Seq.lseq S8.t (2 * secretmatrixbytes p)
  = shake p (Seq.cons (S8.classify 0x5fuy) (Seq.slice coins (crypto_bytes p) (2 * crypto_bytes p)))
          (2 * secretmatrixbytes p)

(** S, transposed, as key generation samples it. *)
let kg_st (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
  : GTot (M.matrix nbar (n p))
  = sample_matrix p nbar (n p) (Seq.slice (kg_r p coins) 0 (secretmatrixbytes p))

let kg_e (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
  : GTot (M.matrix (n p) nbar)
  = sample_matrix p (n p) nbar
      (Seq.slice (kg_r p coins) (secretmatrixbytes p) (2 * secretmatrixbytes p))

(** [seed_se || k], derived from the hash of the public key and mu. *)
let enc_sek (p: params) (mu: Seq.lseq S8.t (bytes_mu p))
            (pk: Seq.lseq S8.t (crypto_publickeybytes p))
  : Seq.lseq S8.t (2 * crypto_bytes p)
  = shake p (Seq.append (shake p pk (crypto_bytes p)) mu) (2 * crypto_bytes p)

let enc_seed (p: params) (mu: Seq.lseq S8.t (bytes_mu p))
             (pk: Seq.lseq S8.t (crypto_publickeybytes p))
  : Seq.lseq S8.t (crypto_bytes p)
  = Seq.slice (enc_sek p mu pk) 0 (crypto_bytes p)

let enc_r (p: params) (seed_se: Seq.lseq S8.t (crypto_bytes p))
  : Seq.lseq S8.t (2 * secretmatrixbytes p + 2 * (nbar * nbar))
  = shake p (Seq.cons (S8.classify 0x96uy) seed_se) (2 * secretmatrixbytes p + 2 * (nbar * nbar))

let enc_sp (p: params) (seed_se: Seq.lseq S8.t (crypto_bytes p)) : GTot (M.matrix nbar (n p)) =
  sample_matrix p nbar (n p) (Seq.slice (enc_r p seed_se) 0 (secretmatrixbytes p))

let enc_ep (p: params) (seed_se: Seq.lseq S8.t (crypto_bytes p)) : GTot (M.matrix nbar (n p)) =
  sample_matrix p nbar (n p)
    (Seq.slice (enc_r p seed_se) (secretmatrixbytes p) (2 * secretmatrixbytes p))

let enc_epp (p: params) (seed_se: Seq.lseq S8.t (crypto_bytes p)) : GTot (M.matrix nbar nbar) =
  sample_matrix p nbar nbar
    (Seq.slice (enc_r p seed_se) (2 * secretmatrixbytes p)
       (2 * secretmatrixbytes p + 2 * (nbar * nbar)))

(** The noise condition for one run of key generation and encapsulation. *)
let kem_noise_ok (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
                 (mu: Seq.lseq S8.t (bytes_mu p))
  : GTot prop
  = let seed = enc_seed p mu (fst (keypair p coins)) in
    noise_ok p (kg_st p coins) (kg_e p coins) (enc_sp p seed) (enc_ep p seed) (enc_epp p seed)

(** {2 Unfolding the three algorithms} *)

let kg_pk (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
  : GTot (Seq.lseq S8.t (crypto_publickeybytes p))
  = Seq.append (kg_seed_a p coins)
      (pack_n p (pke_b p (gen_matrix p (kg_seed_a p coins)) (kg_st p coins) (kg_e p coins)))

let sk_of (p: params) (s: Seq.lseq S8.t (crypto_bytes p))
          (pk: Seq.lseq S8.t (crypto_publickeybytes p)) (st: M.matrix nbar (n p))
  : GTot (Seq.lseq S8.t (crypto_secretkeybytes p))
  = Seq.append s (Seq.append pk (Seq.append (M.to_bytes nbar (n p) st)
                                            (shake p pk (crypto_bytes p))))

let keypair_eq (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
  : Lemma (fst (keypair p coins) == kg_pk p coins /\
           snd (keypair p coins) == sk_of p (kg_s p coins) (kg_pk p coins) (kg_st p coins))
  = ()

let sk_slices (p: params) (s: Seq.lseq S8.t (crypto_bytes p))
              (pk: Seq.lseq S8.t (crypto_publickeybytes p)) (st: M.matrix nbar (n p))
  : Lemma (let sk = sk_of p s pk st in
           let cb = crypto_bytes p in
           let pkb = crypto_publickeybytes p in
           let smb = secretmatrixbytes p in
           Seq.slice sk 0 cb == s /\
           Seq.slice sk cb (cb + pkb) == pk /\
           Seq.slice sk (cb + pkb) (cb + pkb + smb) == M.to_bytes nbar (n p) st /\
           Seq.slice sk (cb + pkb + smb) (crypto_secretkeybytes p) == shake p pk cb)
  = let sk = sk_of p s pk st in
    let cb = crypto_bytes p in
    let pkb = crypto_publickeybytes p in
    let smb = secretmatrixbytes p in
    Seq.lemma_eq_intro (Seq.slice sk 0 cb) s;
    Seq.lemma_eq_intro (Seq.slice sk cb (cb + pkb)) pk;
    Seq.lemma_eq_intro (Seq.slice sk (cb + pkb) (cb + pkb + smb)) (M.to_bytes nbar (n p) st);
    Seq.lemma_eq_intro (Seq.slice sk (cb + pkb + smb) (crypto_secretkeybytes p)) (shake p pk cb)

let pk_slices (p: params) (seed_a: Seq.lseq S8.t bytes_seed_a) (b: M.matrix (n p) nbar)
  : Lemma (let pk = Seq.append seed_a (pack_n p b) in
           Seq.slice pk 0 bytes_seed_a == seed_a /\
           Seq.slice pk bytes_seed_a (crypto_publickeybytes p) == pack_n p b)
  = let pk = Seq.append seed_a (pack_n p b) in
    Seq.lemma_eq_intro (Seq.slice pk 0 bytes_seed_a) seed_a;
    Seq.lemma_eq_intro (Seq.slice pk bytes_seed_a (crypto_publickeybytes p)) (pack_n p b)

let ct_slices (p: params) (c1: Seq.lseq S8.t (ct1bytes p)) (c2: Seq.lseq S8.t (ct2bytes p))
  : Lemma (let ct = Seq.append c1 c2 in
           Seq.slice ct 0 (ct1bytes p) == c1 /\
           Seq.slice ct (ct1bytes p) (crypto_ciphertextbytes p) == c2)
  = let ct = Seq.append c1 c2 in
    Seq.lemma_eq_intro (Seq.slice ct 0 (ct1bytes p)) c1;
    Seq.lemma_eq_intro (Seq.slice ct (ct1bytes p) (crypto_ciphertextbytes p)) c2

#push-options "--ifuel 1"

let enc_ct_eq (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) (seed_a: Seq.lseq S8.t bytes_seed_a)
              (b: M.matrix (n p) nbar) (seed: Seq.lseq S8.t (crypto_bytes p))
  : Lemma (let pk = Seq.append seed_a (pack_n p b) in
           let a = gen_matrix p seed_a in
           let bp = pke_bp p a (enc_sp p seed) (enc_ep p seed) in
           let v = pke_v p (unpacked_n p (n p) nbar b) (enc_sp p seed) (enc_epp p seed) mu in
           enc_ct p mu pk seed ==
           (Seq.append (pack_n p bp) (pack_8 p v),
            M.mod_pow2 nbar (n p) p.logq bp, M.mod_pow2 nbar nbar p.logq v))
  = pk_slices p seed_a b

let enc_eq (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) (pk: Seq.lseq S8.t (crypto_publickeybytes p))
  : Lemma (let ct, _, _ = enc_ct p mu pk (enc_seed p mu pk) in
           enc p mu pk ==
           (ct, shake p (Seq.append ct (Seq.slice (enc_sek p mu pk) (crypto_bytes p)
                                                  (2 * crypto_bytes p)))
                       (crypto_bytes p)))
  = ()

(** Decapsulation of an honest ciphertext under a secret key of the shape
    [keypair] produces, with the noise small. *)
let dec_honest (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) (s: Seq.lseq S8.t (crypto_bytes p))
               (seed_a: Seq.lseq S8.t bytes_seed_a) (st: M.matrix nbar (n p))
               (e: M.matrix (n p) nbar)
  : Lemma (requires (let pk = Seq.append seed_a (pack_n p (pke_b p (gen_matrix p seed_a) st e)) in
                     let seed = enc_seed p mu pk in
                     noise_ok p st e (enc_sp p seed) (enc_ep p seed) (enc_epp p seed)))
          (ensures (let pk = Seq.append seed_a (pack_n p (pke_b p (gen_matrix p seed_a) st e)) in
                    dec p (fst (enc p mu pk)) (sk_of p s pk st) == snd (enc p mu pk)))
  = let cb = crypto_bytes p in
    let a = gen_matrix p seed_a in
    let b = pke_b p a st e in
    let pk = Seq.append seed_a (pack_n p b) in
    let sek = enc_sek p mu pk in
    let seed = enc_seed p mu pk in
    let sp = enc_sp p seed in
    let ep = enc_ep p seed in
    let epp = enc_epp p seed in
    let bp = pke_bp p a sp ep in
    let v = pke_v p (unpacked_n p (n p) nbar b) sp epp mu in
    let ct = Seq.append (pack_n p bp) (pack_8 p v) in
    enc_ct_eq p mu seed_a b seed;
    enc_eq p mu pk;
    assert (fst (enc p mu pk) == ct);
    assert (snd (enc p mu pk) == shake p (Seq.append ct (Seq.slice sek cb (2 * cb))) cb);
    sk_slices p s pk st;
    ct_slices p (pack_n p bp) (pack_8 p v);
    M.from_to_bytes nbar (n p) st;
    pke_correct p a st e sp ep epp mu;
    mod_pow2_unpacked_n p nbar (n p) bp;
    mod_pow2_unpacked_8 p v;
    Seq.lemma_eq_refl (M.mod_pow2 nbar (n p) p.logq (unpacked_n p nbar (n p) bp))
                      (M.mod_pow2 nbar (n p) p.logq bp);
    Seq.lemma_eq_refl (M.mod_pow2 nbar nbar p.logq (unpacked_8 p v))
                      (M.mod_pow2 nbar nbar p.logq v)

(** {2 Correctness of the KEM} *)

let kem_correct (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
                (mu: Seq.lseq S8.t (bytes_mu p))
  : Lemma (requires kem_noise_ok p coins mu)
          (ensures (let pk, sk = keypair p coins in
                    let ct, ss = enc p mu pk in
                    dec p ct sk == ss))
  = keypair_eq p coins;
    dec_honest p mu (kg_s p coins) (kg_seed_a p coins) (kg_st p coins) (kg_e p coins)

#pop-options

#pop-options
