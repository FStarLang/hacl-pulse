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

(** Serialisation, FIPS 204 algorithms 16 through 28.

    Bit order is ML-KEM's -- least significant first within a coefficient
    and within a byte -- so the bit-level readers of {!Spec.MLKEM.Encode}
    are used unchanged; only the widths differ, and ML-DSA's run up to
    twenty bits.

    [BitPack] stores a signed coefficient [c] in [[-a, b]] as the natural
    [b - c].  Coefficients here live in [Z_q] (see {!Spec.MLDSA.Zq}), so
    the packer computes [b - c] with {!Spec.MLDSA.Zq.sub}; for every [c] in
    range that is the integer [b - c], and the unpacker's [b - x] taken
    modulo [q] is the standard's [b - x] reduced into [Z_q], which is how
    every caller uses it. *)
module Spec.MLDSA.Encode

open Spec.MLDSA.Zq
open Spec.MLDSA.Params

module Seq = FStar.Seq
module U8 = FStar.UInt8
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module KZ = Spec.MLKEM.Zq
module KE = Spec.MLKEM.Encode

#push-options "--fuel 0 --ifuel 0"

(** {2 One polynomial} *)

(** [SimpleBitPack] at [d] bits per coefficient.  Values at or above [2^d]
    would lose their high bits; no caller produces one. *)
let simple_bit_pack (d: pos { d <= 20 }) (f: Seq.lseq nat n) : GTot (Seq.lseq S8.t (32 * d))
  = Seq.init_ghost (32 * d) (fun i -> S8.classify (U8.uint_to_t (KE.byte_val d f i)))

(** [SimpleBitUnpack]. *)
let simple_bit_unpack (d: pos { d <= 20 }) (b: Seq.lseq S8.t (32 * d)) : GTot (Seq.lseq nat n)
  = Seq.init_ghost n (fun i -> (KE.bits_val b (i * d) d <: nat))

(** [BitPack(w, a, b)] at [d = bitlen(a + b)] bits. *)
let bit_pack (b: zq) (d: pos { d <= 20 }) (f: poly) : GTot (Seq.lseq S8.t (32 * d))
  = simple_bit_pack d (Seq.init n (fun i -> (sub b (Seq.index f i) <: nat)))

let unpack_bound (d: pos { d <= 20 }) (x: nat { x < pow2 d }) : Lemma (x < q)
  = Math.pow2_le_compat 20 d;
    assert_norm (pow2 20 < q)

(** [BitUnpack(v, a, b)]: [b] minus each [d]-bit field. *)
let bit_unpack (b: zq) (d: pos { d <= 20 }) (v: Seq.lseq S8.t (32 * d)) : GTot poly
  = Seq.init_ghost n (fun i ->
      let x = KE.bits_val v (i * d) d in
      unpack_bound d x;
      sub b x)

(** {2 Vectors}

    [k] polynomials coded one after another. *)

let vec_simple_bit_pack (d: pos { d <= 20 }) (k: pos) (v: Seq.lseq nat (k * n))
  : GTot (Seq.lseq S8.t (k * (32 * d)))
  = KZ.flat_of_fun_g k (32 * d) (fun i -> simple_bit_pack d (KZ.flat_at k n v i))

let vec_simple_bit_unpack (d: pos { d <= 20 }) (k: pos) (b: Seq.lseq S8.t (k * (32 * d)))
  : GTot (Seq.lseq nat (k * n))
  = KZ.flat_of_fun_g k n (fun i -> simple_bit_unpack d (KZ.flat_at k (32 * d) b i))

let vec_bit_pack (b: zq) (d: pos { d <= 20 }) (k: pos) (v: pvec k)
  : GTot (Seq.lseq S8.t (k * (32 * d)))
  = KZ.flat_of_fun_g k (32 * d) (fun i -> bit_pack b d (vec_at v i))

let vec_bit_unpack (b: zq) (d: pos { d <= 20 }) (k: pos) (v: Seq.lseq S8.t (k * (32 * d)))
  : GTot (pvec k)
  = vec_of_fun_g k (fun i -> bit_unpack b d (KZ.flat_at k (32 * d) v i))

(** {2 The hint}

    Algorithm 20, [HintBitPack].  A hint is [k] polynomials of bits with
    at most [omega] ones in total, and it is sent as the positions of its
    ones, [omega] bytes padded with zeros, followed by [k] bytes giving the
    running count at the end of each polynomial.

    The specification is the standard's loop, flattened: one step per
    coefficient, in order.  The [idx < omega] guard is vacuous on a hint
    with at most [omega] ones -- the only kind the signer packs -- and
    makes the function total. *)

let hint_len (p: params) : pos = p.omega + p.k

let hint_state (p: params) = Seq.lseq U8.t (hint_len p) & nat

let hint_pack_step (p: params) (h: Seq.lseq bool (p.k * n)) (t: nat) (st: hint_state p)
  : hint_state p
  = if t >= p.k * n then st
    else begin
      let y, idx = st in
      assert_norm (pow2 8 == 256);
      KZ.div_lt t p.k n;
      let i = t / n in
      let j = t % n in
      let st' : hint_state p =
        if Seq.index h t && idx < p.omega
        then Seq.upd y idx (U8.uint_to_t j), idx + 1
        else y, idx in
      let y, idx = st' in
      if j = n - 1 && idx < 256 then Seq.upd y (p.omega + i) (U8.uint_to_t idx), idx
      else y, idx
    end

let hint_pack (p: params) (h: Seq.lseq bool (p.k * n)) : GTot (Seq.lseq S8.t (hint_len p))
  = let y, _ = Loops.repeati #(hint_state p) (p.k * n) (hint_pack_step p h) (Seq.create (hint_len p) 0uy, 0) in
    Seq.init_ghost (hint_len p) (fun i -> S8.classify (Seq.index y i))

(** Algorithm 21, [HintBitUnpack], specified by what it accepts.

    The standard's unpacker reads the positions belonging to polynomial
    [i] -- those between the running counts [y[omega + i - 1]] and
    [y[omega + i]] -- and rejects the encoding unless the counts are
    non-decreasing and at most [omega], the positions within each
    polynomial strictly increase, and the unused position bytes are zero.
    Those conditions say exactly that the bytes are what {!hint_pack}
    produces from the hint they describe: the packer emits each
    polynomial's positions in increasing order, never decreasing counts,
    and zeros after the last position, so an encoding meeting the
    conditions re-packs to itself; and anything {!hint_pack} produces
    meets them, so an encoding that re-packs to itself meets them too.

    So the decoder here scatters each polynomial's positions into a hint
    with no checks at all, and the encoding is accepted exactly when
    re-packing that hint gives the bytes back.  The scatter bounds each
    range by [omega] so that it is total, and on an accepted encoding the
    bound is never what stops it. *)

let hint_lo (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat { i < p.k }) : GTot nat
  = if i = 0 then 0 else S8.v (Seq.index y (p.omega + i - 1))

let hint_hi (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat { i < p.k }) : GTot nat
  = S8.v (Seq.index y (p.omega + i))

(** Position byte [idx] marks coefficient [y[idx]] of polynomial [i] if
    [idx] is in polynomial [i]'s range. *)
let hint_scatter_step (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat { i < p.k })
                      (idx: nat) (h: Seq.lseq bool (p.k * n))
  : GTot (Seq.lseq bool (p.k * n))
  = if idx < p.omega && hint_lo p y i <= idx && idx < hint_hi p y i then begin
      Math.lemma_mult_le_right n (i + 1) p.k;
      Seq.upd h (i * n + S8.v (Seq.index y idx)) true
    end else h

let hint_scatter_poly (p: params) (y: Seq.lseq S8.t (hint_len p)) (i: nat)
                      (h: Seq.lseq bool (p.k * n))
  : GTot (Seq.lseq bool (p.k * n))
  = if i < p.k then Loops.repeati_g p.omega (hint_scatter_step p y i) h else h

let hint_scatter (p: params) (y: Seq.lseq S8.t (hint_len p)) : GTot (Seq.lseq bool (p.k * n))
  = Loops.repeati_g p.k (hint_scatter_poly p y) (Seq.create (p.k * n) false)

let hint_unpack (p: params) (y: Seq.lseq S8.t (hint_len p))
  : GTot (option (Seq.lseq bool (p.k * n)))
  = let h = hint_scatter p y in
    if FStar.IndefiniteDescription.strong_excluded_middle (hint_pack p h == y)
    then Some h else None

(** {2 Keys and signatures} *)

(** Algorithm 22. *)
let pk_encode (p: params) (rho: Seq.lseq S8.t 32) (t1: Seq.lseq nat (p.k * n))
  : GTot (Seq.lseq S8.t (pk_len p))
  = Seq.append rho (vec_simple_bit_pack 10 p.k t1)

(** Algorithm 23. *)
let pk_decode (p: params) (pk: Seq.lseq S8.t (pk_len p))
  : GTot (Seq.lseq S8.t 32 & Seq.lseq nat (p.k * n))
  = Seq.slice pk 0 32, vec_simple_bit_unpack 10 p.k (Seq.slice pk 32 (pk_len p))

(** The offsets of the five variable-length fields of a private key. *)
let sk_s1_off (p: params) : nat = 128
let sk_s2_off (p: params) : nat = 128 + p.l * (32 * eta_bits p)
let sk_t0_off (p: params) : nat = 128 + (p.l + p.k) * (32 * eta_bits p)

let sk_layout (p: params)
  : Lemma (sk_t0_off p + p.k * (32 * 13) == sk_len p /\
           sk_s2_off p + p.k * (32 * eta_bits p) == sk_t0_off p)
  = ()

(** Algorithm 24.  The secret coefficients are in [[-eta, eta]] and [t0]'s
    in [[-2^12 + 1, 2^12]]. *)
let sk_encode (p: params) (rho: Seq.lseq S8.t 32) (key: Seq.lseq S8.t 32)
              (tr: Seq.lseq S8.t 64) (s1: pvec p.l) (s2: pvec p.k) (t0: pvec p.k)
  : GTot (Seq.lseq S8.t (sk_len p))
  = assert_norm (pow2 12 == 4096);
    Seq.append rho (Seq.append key (Seq.append tr
      (Seq.append (vec_bit_pack p.eta (eta_bits p) p.l s1)
        (Seq.append (vec_bit_pack p.eta (eta_bits p) p.k s2)
                    (vec_bit_pack (pow2 12) 13 p.k t0)))))

noeq
type sk_parts (p: params) = {
  sk_rho: Seq.lseq S8.t 32;
  sk_key: Seq.lseq S8.t 32;
  sk_tr: Seq.lseq S8.t 64;
  sk_s1: pvec p.l;
  sk_s2: pvec p.k;
  sk_t0: pvec p.k;
}

(** Algorithm 25. *)
let sk_decode (p: params) (sk: Seq.lseq S8.t (sk_len p)) : GTot (sk_parts p)
  = assert_norm (pow2 12 == 4096);
    sk_layout p;
    { sk_rho = Seq.slice sk 0 32;
      sk_key = Seq.slice sk 32 64;
      sk_tr = Seq.slice sk 64 128;
      sk_s1 = vec_bit_unpack p.eta (eta_bits p) p.l (Seq.slice sk (sk_s1_off p) (sk_s2_off p));
      sk_s2 = vec_bit_unpack p.eta (eta_bits p) p.k (Seq.slice sk (sk_s2_off p) (sk_t0_off p));
      sk_t0 = vec_bit_unpack (pow2 12) 13 p.k (Seq.slice sk (sk_t0_off p) (sk_len p)) }

let sig_z_off (p: params) : nat = ct_len p
let sig_h_off (p: params) : nat = ct_len p + p.l * (32 * z_bits p)

let sig_layout (p: params)
  : Lemma (sig_h_off p + hint_len p == sig_len p)
  = ()

(** Algorithm 26.  [z]'s coefficients are in [[-gamma1 + 1, gamma1]]. *)
let sig_encode (p: params) (ct: Seq.lseq S8.t (ct_len p)) (z: pvec p.l)
               (h: Seq.lseq bool (p.k * n))
  : GTot (Seq.lseq S8.t (sig_len p))
  = Math.pow2_lt_compat 20 p.gamma1_bits;
    assert_norm (pow2 20 < q);
    Seq.append ct (Seq.append (vec_bit_pack (gamma1 p) (z_bits p) p.l z) (hint_pack p h))

(** Algorithm 27.  The hint may fail to decode; the other two fields
    cannot. *)
let sig_decode (p: params) (sg: Seq.lseq S8.t (sig_len p))
  : GTot (Seq.lseq S8.t (ct_len p) & pvec p.l & option (Seq.lseq bool (p.k * n)))
  = Math.pow2_lt_compat 20 p.gamma1_bits;
    assert_norm (pow2 20 < q);
    sig_layout p;
    Seq.slice sg 0 (ct_len p),
    vec_bit_unpack (gamma1 p) (z_bits p) p.l (Seq.slice sg (sig_z_off p) (sig_h_off p)),
    hint_unpack p (Seq.slice sg (sig_h_off p) (sig_len p))

(** Algorithm 28. *)
let w1_encode (p: params) (w1: Seq.lseq nat (p.k * n))
  : GTot (Seq.lseq S8.t (p.k * (32 * w1_bits p)))
  = vec_simple_bit_pack (w1_bits p) p.k w1

#pop-options
