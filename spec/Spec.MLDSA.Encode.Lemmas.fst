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


(** Round trips for the ML-DSA encoders of {!Spec.MLDSA.Encode}: every
    decoder inverts its encoder on inputs in the encoder's range. *)
module Spec.MLDSA.Encode.Lemmas

open Spec.MLDSA.Zq
open Spec.MLDSA.Params
open Spec.MLDSA.Encode

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module KZ = Spec.MLKEM.Zq
module KE = Spec.MLKEM.Encode

#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"

(** {2 Bits of a byte} *)

let bit_t = x: nat { x < 2 }

let peel (c: bit_t) (y: nat) (k: pos)
  : Lemma ((c + 2 * y) / pow2 k == y / pow2 (k - 1))
  = Math.pow2_double_mult (k - 1);
    Math.division_multiplication_lemma (c + 2 * y) 2 (pow2 (k - 1))

let low (c: bit_t) (y: nat) : Lemma ((c + 2 * y) / pow2 0 % 2 == c)
  = assert_norm (pow2 0 == 1)

let sel8 (c0 c1 c2 c3 c4 c5 c6 c7: bit_t) (k: nat { k < 8 }) : bit_t
  = if k = 0 then c0 else if k = 1 then c1 else if k = 2 then c2 else if k = 3 then c3
    else if k = 4 then c4 else if k = 5 then c5 else if k = 6 then c6 else c7

#push-options "--ifuel 1"
let byte_bit (c0 c1 c2 c3 c4 c5 c6 c7: bit_t) (k: nat { k < 8 })
  : Lemma ((c0 * 1 + c1 * 2 + c2 * 4 + c3 * 8 + c4 * 16 + c5 * 32 + c6 * 64 + c7 * 128)
             / pow2 k % 2 == sel8 c0 c1 c2 c3 c4 c5 c6 c7 k)
  = let r7 = c7 in
    let r6 = c6 + 2 * r7 in
    let r5 = c5 + 2 * r6 in
    let r4 = c4 + 2 * r5 in
    let r3 = c3 + 2 * r4 in
    let r2 = c2 + 2 * r3 in
    let r1 = c1 + 2 * r2 in
    let r0 = c0 + 2 * r1 in
    assert (c0 * 1 + c1 * 2 + c2 * 4 + c3 * 8 + c4 * 16 + c5 * 32 + c6 * 64 + c7 * 128 == r0);
    match k with
    | 0 -> low c0 r1
    | 1 -> peel c0 r1 1; low c1 r2
    | 2 -> peel c0 r1 2; peel c1 r2 1; low c2 r3
    | 3 -> peel c0 r1 3; peel c1 r2 2; peel c2 r3 1; low c3 r4
    | 4 -> peel c0 r1 4; peel c1 r2 3; peel c2 r3 2; peel c3 r4 1; low c4 r5
    | 5 -> peel c0 r1 5; peel c1 r2 4; peel c2 r3 3; peel c3 r4 2; peel c4 r5 1; low c5 r6
    | 6 -> peel c0 r1 6; peel c1 r2 5; peel c2 r3 4; peel c3 r4 3; peel c4 r5 2; peel c5 r6 1;
          low c6 r7
    | _ -> peel c0 r1 7; peel c1 r2 6; peel c2 r3 5; peel c3 r4 4; peel c4 r5 3; peel c5 r6 2;
          peel c6 r7 1; low c7 0
#pop-options

(** {2 One polynomial} *)

let sel8_coeff (d: pos) (f: Seq.seq nat) (i: nat) (k: nat { k < 8 })
  : Lemma (sel8 (KE.coeff_bit d f (8 * i)) (KE.coeff_bit d f (8 * i + 1))
                (KE.coeff_bit d f (8 * i + 2)) (KE.coeff_bit d f (8 * i + 3))
                (KE.coeff_bit d f (8 * i + 4)) (KE.coeff_bit d f (8 * i + 5))
                (KE.coeff_bit d f (8 * i + 6)) (KE.coeff_bit d f (8 * i + 7)) k
           == KE.coeff_bit d f (8 * i + k))
  = if k = 0 then () else if k = 1 then () else if k = 2 then () else if k = 3 then ()
    else if k = 4 then () else if k = 5 then () else if k = 6 then ()
    else begin assert (k == 7); assert (8 * i + k == 8 * i + 7) end

(** Bit [p] of the packed bytes is bit [p] of the coefficient stream. *)
let stream_bit_pack (d: pos { d <= 20 }) (f: Seq.lseq nat n) (p: nat { p < 8 * (32 * d) })
  : Lemma (KE.stream_bit (simple_bit_pack d f) p == KE.coeff_bit d f p)
  = let i = p / 8 in
    let k = p % 8 in
    let b = simple_bit_pack d f in
    assert (S8.v (Seq.index b i) == KE.byte_val d f i);
    byte_bit (KE.coeff_bit d f (8 * i)) (KE.coeff_bit d f (8 * i + 1))
             (KE.coeff_bit d f (8 * i + 2)) (KE.coeff_bit d f (8 * i + 3))
             (KE.coeff_bit d f (8 * i + 4)) (KE.coeff_bit d f (8 * i + 5))
             (KE.coeff_bit d f (8 * i + 6)) (KE.coeff_bit d f (8 * i + 7)) k;
    assert (p == 8 * i + k);
    sel8_coeff d f i k

let coeff_bit_at (d: pos) (f: Seq.lseq nat n) (i: nat { i < n }) (j: nat { j < d })
  : Lemma (KE.coeff_bit d f (i * d + j) == Seq.index f i / pow2 j % 2)
  = Math.lemma_mult_le_right d (i + 1) n;
    Math.lemma_div_plus j i d;
    Math.small_div j d;
    Math.lemma_mod_plus j i d;
    Math.small_mod j d

let mod_pow2_split (y: nat) (m: pos)
  : Lemma (y % pow2 m == y % 2 + 2 * ((y / 2) % pow2 (m - 1)))
  = Math.pow2_double_mult (m - 1);
    Math.modulo_division_lemma y 2 (pow2 (m - 1));
    Math.modulo_modulo_lemma y 2 (pow2 (m - 1))

#push-options "--fuel 1"
let bits_val_zero (b: Seq.seq S8.t) (off: nat) : Lemma (KE.bits_val b off 0 == 0) = ()

let bits_val_unfold (b: Seq.seq S8.t) (off: nat) (m: pos)
  : Lemma (KE.bits_val b off m == KE.stream_bit b off + 2 * KE.bits_val b (off + 1) (m - 1))
  = ()
#pop-options

let rec bits_val_pack (d: pos { d <= 20 }) (f: Seq.lseq nat n) (i: nat { i < n })
                      (j: nat) (m: nat { j + m <= d })
  : Lemma (ensures KE.bits_val (simple_bit_pack d f) (i * d + j) m
                   == (Seq.index f i / pow2 j) % pow2 m)
          (decreases m)
  = let b = simple_bit_pack d f in
    let x = Seq.index f i in
    if m = 0 then begin
      assert_norm (pow2 0 == 1);
      bits_val_zero b (i * d + j)
    end else begin
      bits_val_unfold b (i * d + j) m;
      Math.lemma_mult_le_right d (i + 1) n;
      stream_bit_pack d f (i * d + j);
      coeff_bit_at d f i j;
      bits_val_pack d f i (j + 1) (m - 1);
      Math.pow2_double_mult j;
      Math.division_multiplication_lemma x (pow2 j) 2;
      mod_pow2_split (x / pow2 j) m
    end

let bits_val_pack_full (d: pos { d <= 20 }) (f: Seq.lseq nat n) (i: nat { i < n })
  : Lemma (requires Seq.index f i < pow2 d)
          (ensures KE.bits_val (simple_bit_pack d f) (i * d) d == Seq.index f i)
  = bits_val_pack d f i 0 d;
    assert_norm (pow2 0 == 1);
    Math.small_mod (Seq.index f i) (pow2 d)

let simple_bit_unpack_pack (d: pos { d <= 20 }) (f: Seq.lseq nat n)
  : Lemma (requires forall (i: nat). i < n ==> Seq.index f i < pow2 d)
          (ensures simple_bit_unpack d (simple_bit_pack d f) == f)
  = let g = simple_bit_unpack d (simple_bit_pack d f) in
    introduce forall (i: nat { i < n }). Seq.index g i == Seq.index f i
    with bits_val_pack_full d f i;
    Seq.lemma_eq_intro g f

let sub_sub (b x: zq) : Lemma (sub b (sub b x) == x)
  = if b >= x then begin
      Math.lemma_mod_plus (b - x) 1 q;
      Math.small_mod (b - x) q;
      Math.lemma_mod_plus x 1 q;
      Math.small_mod x q
    end else begin
      Math.small_mod (b + q - x) q;
      Math.small_mod x q
    end

let bit_unpack_pack (b: zq) (d: pos { d <= 20 }) (f: poly)
  : Lemma (requires forall (i: nat). i < n ==> sub b (Seq.index f i) < pow2 d)
          (ensures bit_unpack b d (bit_pack b d f) == f)
  = let g : Seq.lseq nat n = Seq.init n (fun i -> (sub b (Seq.index f i) <: nat)) in
    let r = bit_unpack b d (bit_pack b d f) in
    introduce forall (i: nat { i < n }). Seq.index r i == Seq.index f i
    with begin
      bits_val_pack_full d g i;
      sub_sub b (Seq.index f i)
    end;
    Seq.lemma_eq_intro r f

(** {2 Vectors} *)

(** A flat sequence is rebuilt from its blocks. *)
let flat_ext (#a: Type) (k: pos) (m: pos) (v: Seq.lseq a (k * m))
             (f: (i: nat { i < k }) -> GTot (Seq.lseq a m))
  : Lemma (requires forall (i: nat { i < k }). f i == KZ.flat_at k m v i)
          (ensures KZ.flat_of_fun_g k m f == v)
  = let w = KZ.flat_of_fun_g k m f in
    introduce forall (t: nat { t < k * m }). Seq.index w t == Seq.index v t
    with begin
      KZ.div_lt t k m;
      Math.euclidean_division_definition t m;
      Math.lemma_mult_le_right m (t / m + 1) k
    end;
    Seq.lemma_eq_intro w v

let flat_at_index (#a: Type) (k: pos) (m: pos) (v: Seq.lseq a (k * m)) (i: nat { i < k })
                  (j: nat { j < m })
  : Lemma (Math.lemma_mult_le_right m (i + 1) k;
           Seq.index (KZ.flat_at k m v i) j == Seq.index v (i * m + j))
  = Math.lemma_mult_le_right m (i + 1) k

let vec_simple_bit_unpack_pack (d: pos { d <= 20 }) (k: pos) (v: Seq.lseq nat (k * n))
  : Lemma (requires forall (i: nat). i < k * n ==> Seq.index v i < pow2 d)
          (ensures vec_simple_bit_unpack d k (vec_simple_bit_pack d k v) == v)
  = let pk = vec_simple_bit_pack d k v in
    let pf (i: nat { i < k }) : GTot (Seq.lseq S8.t (32 * d))
      = simple_bit_pack d (KZ.flat_at k n v i) in
    let uf (i: nat { i < k }) : GTot (Seq.lseq nat n)
      = simple_bit_unpack d (KZ.flat_at k (32 * d) pk i) in
    assert (pk == KZ.flat_of_fun_g k (32 * d) pf);
    introduce forall (i: nat { i < k }). uf i == KZ.flat_at k n v i
    with begin
      KZ.flat_at_of_fun_g k (32 * d) pf i;
      introduce forall (j: nat { j < n }). Seq.index (KZ.flat_at k n v i) j < pow2 d
      with flat_at_index k n v i j;
      simple_bit_unpack_pack d (KZ.flat_at k n v i)
    end;
    flat_ext k n v uf;
    assert (vec_simple_bit_unpack d k pk == KZ.flat_of_fun_g k n uf)

let vec_bit_unpack_pack (b: zq) (d: pos { d <= 20 }) (k: pos) (v: pvec k)
  : Lemma (requires forall (i: nat). i < k * n ==> sub b (Seq.index v i) < pow2 d)
          (ensures vec_bit_unpack b d k (vec_bit_pack b d k v) == v)
  = let pk = vec_bit_pack b d k v in
    let pf (i: nat { i < k }) : GTot (Seq.lseq S8.t (32 * d))
      = bit_pack b d (vec_at v i) in
    let uf (i: nat { i < k }) : GTot poly
      = bit_unpack b d (KZ.flat_at k (32 * d) pk i) in
    assert (pk == KZ.flat_of_fun_g k (32 * d) pf);
    introduce forall (i: nat { i < k }). uf i == KZ.flat_at k n v i
    with begin
      KZ.flat_at_of_fun_g k (32 * d) pf i;
      introduce forall (j: nat { j < n }). sub b (Seq.index (vec_at v i) j) < pow2 d
      with flat_at_index k n v i j;
      bit_unpack_pack b d (vec_at v i)
    end;
    flat_ext k n v uf;
    assert (vec_bit_unpack b d k pk == KZ.flat_of_fun_g k n uf)

(** {2 Slices of concatenations} *)

let slice_append_l (#a: Type) (s1 s2: Seq.seq a) (i: nat) (j: nat { i <= j /\ j <= Seq.length s1 })
  : Lemma (Seq.slice (Seq.append s1 s2) i j == Seq.slice s1 i j)
  = Seq.lemma_eq_intro (Seq.slice (Seq.append s1 s2) i j) (Seq.slice s1 i j)

let slice_append_r (#a: Type) (s1 s2: Seq.seq a) (i: nat)
                   (j: nat { Seq.length s1 <= i /\ i <= j /\ j <= Seq.length s1 + Seq.length s2 })
  : Lemma (Seq.slice (Seq.append s1 s2) i j
           == Seq.slice s2 (i - Seq.length s1) (j - Seq.length s1))
  = Seq.lemma_eq_intro (Seq.slice (Seq.append s1 s2) i j)
                       (Seq.slice s2 (i - Seq.length s1) (j - Seq.length s1))

let slice_full (#a: Type) (s: Seq.seq a) : Lemma (Seq.slice s 0 (Seq.length s) == s)
  = Seq.lemma_eq_intro (Seq.slice s 0 (Seq.length s)) s

(** {2 Coefficient ranges} *)

let sub_centre (b c: zq)
  : Lemma (requires 0 <= b - centre c /\ b - centre c < q)
          (ensures sub b c == b - centre c)
  = if c > half_q then begin
      Math.small_mod (b + q - c) q
    end else begin
      Math.lemma_mod_plus (b - c) 1 q;
      Math.small_mod (b - c) q
    end

let sub_norm_bound (b c: zq)
  : Lemma (requires norm c <= b /\ 2 * b < q) (ensures sub b c <= 2 * b)
  = sub_centre b c

(** {2 Keys and signatures} *)

let pk_decode_encode (p: params) (rho: Seq.lseq S8.t 32) (t1: Seq.lseq nat (p.k * n))
  : Lemma (requires forall (i: nat). i < p.k * n ==> Seq.index t1 i < pow2 10)
          (ensures pk_decode p (pk_encode p rho t1) == (rho, t1))
  = let x = vec_simple_bit_pack 10 p.k t1 in
    Seq.append_slices rho x;
    Seq.lemma_eq_elim rho (Seq.slice (Seq.append rho x) 0 32);
    Seq.lemma_eq_elim x (Seq.slice (Seq.append rho x) 32 (pk_len p));
    vec_simple_bit_unpack_pack 10 p.k t1

let eta_range (p: params) (s: zq)
  : Lemma (requires norm s <= p.eta)
          (ensures p.eta < q /\ sub p.eta s < pow2 (eta_bits p))
  = sub_norm_bound p.eta s;
    assert_norm (pow2 3 == 8);
    assert_norm (pow2 4 == 16)

let t0_range (t: zq)
  : Lemma (requires - 4096 < centre t /\ centre t <= 4096)
          (ensures pow2 12 < q /\ sub (pow2 12) t < pow2 13)
  = assert_norm (pow2 12 == 4096);
    assert_norm (pow2 13 == 8192);
    sub_centre 4096 t

let tr_of_sk (p: params) (rho key: Seq.lseq S8.t 32) (tr: Seq.lseq S8.t 64)
             (s1: pvec p.l) (s2: pvec p.k) (t0: pvec p.k)
  : Lemma (Seq.slice (sk_encode p rho key tr s1 s2 t0) 64 128 == tr)
  = assert_norm (pow2 12 == 4096);
    sk_layout p;
    let s1b = vec_bit_pack p.eta (eta_bits p) p.l s1 in
    let s2b = vec_bit_pack p.eta (eta_bits p) p.k s2 in
    let t0b = vec_bit_pack (pow2 12) 13 p.k t0 in
    let r3 = Seq.append s1b (Seq.append s2b t0b) in
    let r2 = Seq.append tr r3 in
    let r1 = Seq.append key r2 in
    let sk = Seq.append rho r1 in
    assert (sk == sk_encode p rho key tr s1 s2 t0);
    slice_append_r rho r1 64 128;
    slice_append_r key r2 32 96;
    slice_append_l tr r3 0 64;
    slice_full tr

#push-options "--z3rlimit 40"
let sk_decode_encode (p: params) (rho key: Seq.lseq S8.t 32) (tr: Seq.lseq S8.t 64)
                     (s1: pvec p.l) (s2: pvec p.k) (t0: pvec p.k)
  : Lemma (requires (forall (i: nat). i < p.l * n ==> norm (Seq.index s1 i) <= p.eta) /\
                    (forall (i: nat). i < p.k * n ==> norm (Seq.index s2 i) <= p.eta) /\
                    (forall (i: nat). i < p.k * n ==>
                       - 4096 < centre (Seq.index t0 i) /\ centre (Seq.index t0 i) <= 4096))
          (ensures (let sp = sk_decode p (sk_encode p rho key tr s1 s2 t0) in
                    sp.sk_rho == rho /\ sp.sk_key == key /\ sp.sk_tr == tr /\
                    sp.sk_s1 == s1 /\ sp.sk_s2 == s2 /\ sp.sk_t0 == t0))
  = assert_norm (pow2 12 == 4096);
    sk_layout p;
    let e = eta_bits p in
    Math.nat_times_nat_is_nat p.l (32 * e);
    Math.nat_times_nat_is_nat p.k (32 * e);
    let s1b = vec_bit_pack p.eta e p.l s1 in
    let s2b = vec_bit_pack p.eta e p.k s2 in
    let t0b = vec_bit_pack (pow2 12) 13 p.k t0 in
    let r4 = Seq.append s2b t0b in
    let r3 = Seq.append s1b r4 in
    let r2 = Seq.append tr r3 in
    let r1 = Seq.append key r2 in
    let sk = Seq.append rho r1 in
    assert (sk == sk_encode p rho key tr s1 s2 t0);
    let o2 = sk_s2_off p in
    let o3 = sk_t0_off p in
    let len = sk_len p in
    (* rho *)
    slice_append_l rho r1 0 32; slice_full rho;
    (* key *)
    slice_append_r rho r1 32 64; slice_append_l key r2 0 32; slice_full key;
    (* tr *)
    tr_of_sk p rho key tr s1 s2 t0;
    (* s1 *)
    slice_append_r rho r1 128 o2; slice_append_r key r2 96 (o2 - 32);
    slice_append_r tr r3 64 (o2 - 64); slice_append_l s1b r4 0 (o2 - 128); slice_full s1b;
    (* s2 *)
    slice_append_r rho r1 o2 o3; slice_append_r key r2 (o2 - 32) (o3 - 32);
    slice_append_r tr r3 (o2 - 64) (o3 - 64); slice_append_r s1b r4 (o2 - 128) (o3 - 128);
    slice_append_l s2b t0b 0 (o3 - o2); slice_full s2b;
    (* t0 *)
    slice_append_r rho r1 o3 len; slice_append_r key r2 (o3 - 32) (len - 32);
    slice_append_r tr r3 (o3 - 64) (len - 64); slice_append_r s1b r4 (o3 - 128) (len - 128);
    slice_append_r s2b t0b (o3 - o2) (len - o2); slice_full t0b;
    introduce forall (i: nat { i < p.l * n }). sub p.eta (Seq.index s1 i) < pow2 e
    with eta_range p (Seq.index s1 i);
    introduce forall (i: nat { i < p.k * n }). sub p.eta (Seq.index s2 i) < pow2 e
    with eta_range p (Seq.index s2 i);
    introduce forall (i: nat { i < p.k * n }). sub (pow2 12) (Seq.index t0 i) < pow2 13
    with t0_range (Seq.index t0 i);
    vec_bit_unpack_pack p.eta e p.l s1;
    vec_bit_unpack_pack p.eta e p.k s2;
    vec_bit_unpack_pack (pow2 12) 13 p.k t0
#pop-options

let z_range (p: params) (z: zq)
  : Lemma (requires norm z < gamma1 p)
          (ensures gamma1 p < q /\ sub (gamma1 p) z < pow2 (z_bits p))
  = Math.pow2_le_compat 19 p.gamma1_bits;
    assert_norm (pow2 19 < q / 2);
    Math.pow2_double_mult p.gamma1_bits;
    sub_centre (gamma1 p) z

let sig_decode_encode (p: params) (ct: Seq.lseq S8.t (ct_len p)) (z: pvec p.l)
                      (h: Seq.lseq bool (p.k * n))
  : Lemma (requires (forall (i: nat). i < p.l * n ==> norm (Seq.index z i) < gamma1 p) /\
                    hint_scatter p (hint_pack p h) == h)
          (ensures sig_decode p (sig_encode p ct z h) == (ct, z, Some h))
  = Math.pow2_lt_compat 20 p.gamma1_bits;
    assert_norm (pow2 20 < q);
    sig_layout p;
    let zb = vec_bit_pack (gamma1 p) (z_bits p) p.l z in
    let hb = hint_pack p h in
    let r = Seq.append zb hb in
    let sg = Seq.append ct r in
    assert (sg == sig_encode p ct z h);
    let oz = sig_z_off p in
    let oh = sig_h_off p in
    let len = sig_len p in
    slice_append_l ct r 0 oz; slice_full ct;
    slice_append_r ct r oz oh; slice_append_l zb hb 0 (oh - oz); slice_full zb;
    slice_append_r ct r oh len; slice_append_r zb hb (oh - oz) (len - oz); slice_full hb;
    introduce forall (i: nat { i < p.l * n }). sub (gamma1 p) (Seq.index z i) < pow2 (z_bits p)
    with z_range p (Seq.index z i);
    vec_bit_unpack_pack (gamma1 p) (z_bits p) p.l z;
    assert (hint_unpack p hb == Some h)

#pop-options
