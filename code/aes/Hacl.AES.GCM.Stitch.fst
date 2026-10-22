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

(** AES-GCM encryption in one pass: counter mode and GHASH, stitched.

    Encryption used to be two passes over the message: [Hacl.AES.CTR] wrote
    the ciphertext, then [Hacl.AES.GHash] read it back.  Each pass on its own
    keeps one execution unit busy -- the first the AES unit, the second the
    carry-less multiplier -- and leaves the other idle.  The two are
    independent units, so a loop that issues both kinds of instruction side
    by side runs at close to the speed of the slower one rather than the sum
    of the two.

    Each turn of the loop below encrypts eight blocks and hashes the eight
    blocks of ciphertext the {i previous} turn wrote.  Between consecutive
    [AESENC] rounds it computes one of the eight Karatsuba triples of the
    aggregated GHASH product and adds it into three running sums; after the
    last round the sums are reduced once, by [Hacl.AES.GF128.NI.gmul8_fin].
    The order matters: measured as C, the same instructions with all of the
    GHASH work grouped before or after the rounds were a fifth slower than
    with it interleaved, because the compiler does not reschedule across
    that distance.  So the interleaving is written out here, round by round.

    The first eight blocks are only encrypted and the last eight only
    hashed; whatever is left after the last multiple of 128 bytes goes
    through the ordinary two-pass path.  The proof is the two existing ones
    side by side: [Hacl.AES.CTR]'s per-byte invariant and
    [Hacl.AES.GF128.NI.ghash_step8]'s eight-block Horner step. *)
module Hacl.AES.GCM.Stitch

#lang-pulse

open FStar.Attributes
open Pulse.Lib.Pervasives
open Spec.Byte
open Spec.AES
open Hacl.AES.Cipher
open Hacl.AES.Counter
open Hacl.AES.CTR

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Math = FStar.Math.Lemmas
module Classical = FStar.Classical
module Sub = Hacl.Impl.Sub
module Vec = Hacl.Vec128
module G = Spec.GF128
module Poly = Spec.GF128.Poly
module Alg = Spec.GF128.Algebra
module GCM = Spec.GCM
module NI = Hacl.AES.NI
module GN = Hacl.AES.GF128.NI
module CL = Spec.CLMUL

#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"

(** {2 The pure side} *)

(** Counter mode's loop invariant, as [Hacl.AES.CTR] states it: the first
    [j] bytes are encrypted and the rest untouched. *)
[@@"opaque_to_smt"]
let ctr_inv_k (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
              (m0 m: Seq.seq elem) (j: nat) : prop =
  Seq.length m == Seq.length m0 /\
  (forall (k: nat). k < Seq.length m0 ==>
     Seq.index m k ==
       (if k < j then Seq.index m0 k ^^ ctr_keystream v w b (Seq.length m0) k
        else Seq.index m0 k))

let ctr_inv (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
            (m0 m: Seq.seq elem) (j: nat) : prop =
  Seq.length m == Seq.length m0 /\ j <= Seq.length m0 /\ ctr_inv_k v w b m0 m j

let ctr_inv_def (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                (m0 m: Seq.seq elem) (j: nat)
  : Lemma (ctr_inv v w b m0 m j <==>
           (Seq.length m == Seq.length m0 /\ j <= Seq.length m0 /\
            (forall (k: nat). k < Seq.length m0 ==>
               Seq.index m k ==
                 (if k < j then Seq.index m0 k ^^ ctr_keystream v w b (Seq.length m0) k
                  else Seq.index m0 k))))
  = reveal_opaque (`%ctr_inv_k) (ctr_inv_k v w b m0 m j)

let ctr_inv_cong (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
                 (m0 m: Seq.seq elem) (j j': nat)
  : Lemma (requires ctr_inv v w b m0 m j /\ j == j')
          (ensures ctr_inv v w b m0 m j')
  = ()

(** The last round finishes one counter block's cipher. *)
let fin_eq (v: variant) (w: Seq.lseq elem (xkeylen v)) (u c e kl: block)
           (b: block) (k: nat)
  : Lemma (requires rounds v w u (nr v) == cipher v w c /\
                    kl == round_key v w (nr v) /\ c == counter_block b k /\
                    e == last_round kl u)
          (ensures e == cipher v w (counter_block b k))
  = rounds_last v w u

(** One block of keystream, exclusive-ored in at [j] by
    [Hacl.AES.NI.xor_at_ni], extends the invariant by a block. *)
let ctr1_step (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
              (m0 m m': Seq.seq elem) (j bi: nat) (ks: Seq.seq elem)
  : Lemma (requires
      ctr_inv v w b m0 m j /\ j == 16 * bi /\ j + blocklen <= Seq.length m0 /\
      Seq.length ks == blocklen /\ ks == cipher v w (counter_block b bi) /\
      Seq.length m' == Seq.length m /\
      (forall (k: nat). k < Seq.length m ==>
         Seq.index m' k ==
           (if j <= k && k < j + blocklen
            then Seq.index m k ^^ Seq.index ks (k - j)
            else Seq.index m k)))
    (ensures ctr_inv v w b m0 m' (j + blocklen))
  = ctr_inv_def v w b m0 m j;
    let aux (k: nat { k < Seq.length m0 })
      : Lemma (Seq.index m' k ==
                 (if k < j + blocklen
                  then Seq.index m0 k ^^ ctr_keystream v w b (Seq.length m0) k
                  else Seq.index m0 k))
      = if j <= k && k < j + blocklen
        then ks_index v w b (Seq.length m0) j bi (k - j)
        else ()
    in
    ctr_inv_def v w b m0 m' (j + blocklen);
    Classical.forall_intro aux

(** Everything below [j] is ciphertext. *)
let ctr_slice (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
              (m0 m: Seq.seq elem) (j lo hi: nat)
  : Lemma (requires ctr_inv v w b m0 m j /\ lo <= hi /\ hi <= j)
          (ensures Seq.length (ctr_encrypt v w b m0) == Seq.length m0 /\
                   Seq.slice m lo hi == Seq.slice (ctr_encrypt v w b m0) lo hi)
  = ctr_inv_def v w b m0 m j;
    Seq.lemma_eq_intro (Seq.slice m lo hi) (Seq.slice (ctr_encrypt v w b m0) lo hi)

let ctr_fin (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
            (m0 m: Seq.seq elem)
  : Lemma (requires ctr_inv v w b m0 m (Seq.length m0))
          (ensures m == ctr_encrypt v w b m0)
  = ctr_inv_def v w b m0 m (Seq.length m0);
    Seq.lemma_eq_intro m (ctr_encrypt v w b m0)

(** Counter mode over a message is counter mode over a whole number of
    blocks of it, then counter mode over the rest from where the counter
    got to. *)
let ctr_split (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block)
              (m: Seq.seq elem) (l: nat)
  : Lemma (requires l <= Seq.length m /\ l % 16 == 0)
          (ensures ctr_encrypt v w b m ==
                   Seq.append (ctr_encrypt v w b (Seq.slice m 0 l))
                              (ctr_encrypt v w (counter_block b (l / 16))
                                           (Seq.slice m l (Seq.length m))))
  = let n = Seq.length m in
    let c1 = ctr_encrypt v w b (Seq.slice m 0 l) in
    let c2 = ctr_encrypt v w (counter_block b (l / 16)) (Seq.slice m l n) in
    let aux (k: nat { k < n })
      : Lemma (Seq.index (ctr_encrypt v w b m) k == Seq.index (Seq.append c1 c2) k)
      = if k < l then Seq.lemma_index_app1 c1 c2 k
        else begin
          Seq.lemma_index_app2 c1 c2 k;
          counter_block_add b (l / 16) ((k - l) / 16);
          Math.euclidean_division_definition l 16;
          Math.lemma_div_plus (k - l) (l / 16) 16;
          Math.lemma_mod_plus (k - l) (l / 16) 16
        end
    in
    Classical.forall_intro aux;
    Seq.lemma_eq_intro (ctr_encrypt v w b m) (Seq.append c1 c2)

(** Padding a message that begins with whole blocks pads only its tail. *)
let pad_append (c1 c2: Seq.seq elem)
  : Lemma (requires Seq.length c1 % 16 == 0)
          (ensures GCM.pad (Seq.append c1 c2) == Seq.append c1 (GCM.pad c2))
  = let n1 = Seq.length c1 in
    let n2 = Seq.length c2 in
    Math.lemma_mod_add_distr n2 n1 16;
    assert (GCM.padlen (n1 + n2) == GCM.padlen n2);
    Seq.append_assoc c1 c2 (Seq.create (GCM.padlen n2) 0)

(** The GHASH of the first [l] bytes, when that is a whole number of
    blocks.  The test makes it a total function, so that an invariant can
    mention it without carrying the arithmetic that makes it well typed. *)
let gh_prefix (h acc: G.block) (c: Seq.seq elem) (l: nat) : G.block =
  if l <= Seq.length c && l % 16 = 0 then G.ghash_upd h acc (Seq.slice c 0 l)
  else acc

let gh_prefix_zero (h acc: G.block) (c: Seq.seq elem)
  : Lemma (gh_prefix h acc c 0 == acc)
  = GN.ghash_zero h acc (Seq.slice c 0 0)

(** Hashing a prefix and then the next stretch is hashing the longer
    prefix. *)
let gh_extend (h acc: G.block) (c: Seq.seq elem) (a b: nat)
  : Lemma (requires a <= b /\ b <= Seq.length c /\ a % 16 == 0 /\ b % 16 == 0 /\
                    (b - a) % 16 == 0)
          (ensures G.ghash_upd h (gh_prefix h acc c a) (Seq.slice c a b) ==
                   gh_prefix h acc c b)
  = Seq.lemma_eq_intro (Seq.append (Seq.slice c 0 a) (Seq.slice c a b))
                       (Seq.slice c 0 b);
    G.ghash_upd_append h acc (Seq.slice c 0 a) (Seq.slice c a b)

(** [ghash_step8] for a 128-byte window anywhere in a sequence. *)
let gh8_fold (hh acc h2 h3 h4 h5 h6 h7 h8: G.block) (d: Seq.seq elem) (i: nat)
  : Lemma (requires i + 128 <= Seq.length d /\
                    h2 == G.gmul hh hh /\ h3 == G.gmul h2 hh /\
                    h4 == G.gmul h3 hh /\ h5 == G.gmul h4 hh /\
                    h6 == G.gmul h5 hh /\ h7 == G.gmul h6 hh /\
                    h8 == G.gmul h7 hh)
          (ensures G.ghash_upd hh acc (Seq.slice d i (i + 128)) ==
                   Alg.sum8
                     (G.gmul (G.gadd acc (Seq.slice d i (i + 16))) h8)
                     (G.gmul (Seq.slice d (i + 16) (i + 32)) h7)
                     (G.gmul (Seq.slice d (i + 32) (i + 48)) h6)
                     (G.gmul (Seq.slice d (i + 48) (i + 64)) h5)
                     (G.gmul (Seq.slice d (i + 64) (i + 80)) h4)
                     (G.gmul (Seq.slice d (i + 80) (i + 96)) h3)
                     (G.gmul (Seq.slice d (i + 96) (i + 112)) h2)
                     (G.gmul (Seq.slice d (i + 112) (i + 128)) hh))
  = let dd = Seq.slice d i (i + 128) in
    GN.ghash_step8 hh acc h2 h3 h4 h5 h6 h7 h8 dd 128 0;
    Seq.lemma_eq_intro (Seq.slice dd 0 128) dd;
    GN.ghash_zero hh acc dd;
    Seq.slice_slice d i (i + 128) 0 16;
    Seq.slice_slice d i (i + 128) 16 32;
    Seq.slice_slice d i (i + 128) 32 48;
    Seq.slice_slice d i (i + 128) 48 64;
    Seq.slice_slice d i (i + 128) 64 80;
    Seq.slice_slice d i (i + 128) 80 96;
    Seq.slice_slice d i (i + 128) 96 112;
    Seq.slice_slice d i (i + 128) 112 128

(** One turn's GHASH, from what the turn computed to the invariant. *)
#push-options "--z3rlimit 200"
let gh_chunk (hv: Seq.seq elem) (a0: G.block) (cc m: Seq.seq elem) (j: nat)
             (a d0 d1 d2 d3 d4 d5 d6 d7 y y2 y3 y4 y5 y6 y7 y8 r: Vec.t)
  : Lemma
    (requires
       Alg.pows_ok hv /\
       Vec.bv y == Alg.hblk hv 0 /\ Vec.bv y2 == Alg.hblk hv 1 /\
       Vec.bv y3 == Alg.hblk hv 2 /\ Vec.bv y4 == Alg.hblk hv 3 /\
       Vec.bv y5 == Alg.hblk hv 4 /\ Vec.bv y6 == Alg.hblk hv 5 /\
       Vec.bv y7 == Alg.hblk hv 6 /\ Vec.bv y8 == Alg.hblk hv 7 /\
       128 <= j /\ j % 16 == 0 /\ j <= Seq.length cc /\ j <= Seq.length m /\
       Seq.slice m (j - 128) j == Seq.slice cc (j - 128) j /\
       Vec.bv d0 == Seq.slice m (j - 128) (j - 112) /\
       Vec.bv d1 == Seq.slice m (j - 112) (j - 96) /\
       Vec.bv d2 == Seq.slice m (j - 96) (j - 80) /\
       Vec.bv d3 == Seq.slice m (j - 80) (j - 64) /\
       Vec.bv d4 == Seq.slice m (j - 64) (j - 48) /\
       Vec.bv d5 == Seq.slice m (j - 48) (j - 32) /\
       Vec.bv d6 == Seq.slice m (j - 32) (j - 16) /\
       Vec.bv d7 == Seq.slice m (j - 16) j /\
       Vec.bv a == gh_prefix (Poly.xtimes (Alg.hblk hv 0)) a0 cc (j - 128) /\
       Vec.bv r ==
         Alg.sum8 (G.gmul (Vec.bv (Vec.vxor a d0)) (Poly.xtimes (Vec.bv y8)))
                  (G.gmul (Vec.bv d1) (Poly.xtimes (Vec.bv y7)))
                  (G.gmul (Vec.bv d2) (Poly.xtimes (Vec.bv y6)))
                  (G.gmul (Vec.bv d3) (Poly.xtimes (Vec.bv y5)))
                  (G.gmul (Vec.bv d4) (Poly.xtimes (Vec.bv y4)))
                  (G.gmul (Vec.bv d5) (Poly.xtimes (Vec.bv y3)))
                  (G.gmul (Vec.bv d6) (Poly.xtimes (Vec.bv y2)))
                  (G.gmul (Vec.bv d7) (Poly.xtimes (Vec.bv y))))
    (ensures Vec.bv r == gh_prefix (Poly.xtimes (Alg.hblk hv 0)) a0 cc j)
  = let s = j - 128 in
    Math.lemma_mod_sub j 16 8;
    GN.xor_block_bv a d0;
    let sl (x: Seq.seq elem) (t: nat { t < 8 /\ j <= Seq.length x })
      : Lemma (Seq.slice (Seq.slice x s j) (16 * t) (16 * t + 16) ==
               Seq.slice x (s + 16 * t) (s + 16 * t + 16))
      = Seq.slice_slice x s j (16 * t) (16 * t + 16)
    in
    sl m 0; sl m 1; sl m 2; sl m 3; sl m 4; sl m 5; sl m 6; sl m 7;
    sl cc 0; sl cc 1; sl cc 2; sl cc 3; sl cc 4; sl cc 5; sl cc 6; sl cc 7;
    let hh = Poly.xtimes (Alg.hblk hv 0) in
    gh8_fold hh (Vec.bv a)
             (Poly.xtimes (Vec.bv y2)) (Poly.xtimes (Vec.bv y3))
             (Poly.xtimes (Vec.bv y4)) (Poly.xtimes (Vec.bv y5))
             (Poly.xtimes (Vec.bv y6)) (Poly.xtimes (Vec.bv y7))
             (Poly.xtimes (Vec.bv y8)) cc s;
    gh_extend hh a0 cc s j
#pop-options

(** The last 128 bytes, hashed on their own once the loop is done. *)
let gh_last (hh a0: G.block) (cc: Seq.seq elem) (n: nat) (a r: G.block)
            (vd: Seq.seq elem)
  : Lemma (requires 128 <= n /\ n == Seq.length cc /\ n % 16 == 0 /\
                    vd == Seq.slice cc (n - 128) n /\
                    a == gh_prefix hh a0 cc (n - 128) /\
                    Seq.length (Seq.slice vd 0 128) % 16 == 0 /\
                    r == G.ghash_from hh a (Seq.slice vd 0 128) (128 / 16))
          (ensures Seq.length cc % 16 == 0 /\ r == G.ghash_upd hh a0 cc)
  = Math.lemma_mod_sub n 16 8;
    Seq.lemma_eq_intro (Seq.slice vd 0 128) vd;
    gh_extend hh a0 cc (n - 128) n;
    Seq.lemma_eq_intro (Seq.slice cc 0 n) cc

(** Index arithmetic, out of the Pulse context. *)
let j_facts (j: nat)
  : Lemma (requires j % 128 == 0)
          (ensures j % 16 == 0 /\ j == 16 * (j / 16) /\
                   (j + 128) % 128 == 0 /\ (j + 128) / 16 == j / 16 + 8)
  = let q = j / 128 in
    Math.euclidean_division_definition j 128;
    Math.multiple_modulo_lemma (8 * q) 16;
    Math.multiple_division_lemma (8 * q) 16;
    Math.multiple_division_lemma (8 * q + 8) 16;
    Math.lemma_mod_plus j 1 128

let step_bounds (j n: nat)
  : Lemma (requires j % 128 == 0 /\ n % 128 == 0 /\ j < n)
          (ensures j + 128 <= n)
  = Math.euclidean_division_definition j 128;
    Math.euclidean_division_definition n 128

let lim_facts (n: nat)
  : Lemma (requires 128 <= n)
          (ensures (let l = n - n % 128 in
                    128 <= l /\ l <= n /\ l % 128 == 0 /\ l % 16 == 0))
  = Math.euclidean_division_definition n 128;
    Math.multiple_modulo_lemma (n / 128) 128;
    Math.lemma_div_le 128 n 128;
    j_facts (n - n % 128)

let small_fits (x: nat)
  : Lemma (requires x <= 256) (ensures SZ.fits x)
  = assert_norm (pow2 16 == 65536);
    SZ.fits_at_least_16 x

(** Eight consecutive counter blocks, from the register arithmetic. *)
(** {2 The hash key's powers, prepared once}

    [GN.kp_ll], [GN.kp_hh] and [GN.kp_mf] reverse both operands and fold
    the second one's halves together every time.  The second operand is a
    power of the hash key, the same eight every turn, so the loop takes them
    already reversed and already folded: [kq_*] are the same three products
    from those.  The values agree as blocks, which is all
    [GN.gmul8_fin] asks about. *)

inline_for_extraction
let kmix (z: Vec.t) : Vec.t = Vec.vxor z (Vec.shift_right_bytes_8 z)

inline_for_extraction
let kq_ll (x yb: Vec.t) : Vec.t = Vec.clmul_ll (Vec.bswap x) yb

inline_for_extraction
let kq_hh (x yb: Vec.t) : Vec.t = Vec.clmul_hh (Vec.bswap x) yb

inline_for_extraction
let kq_mf (x ym: Vec.t) : Vec.t = Vec.clmul_ll (kmix (Vec.bswap x)) ym

(** All that [CLMUL]'s low-lane product sees of a folded operand. *)
let mix_ok (m b: block) : prop =
  CL.lane m false == Spec.CarryLess.padd (CL.lane b false) (CL.lane b true)

(** A power [y], reversed, and folded.  Opaque, so that a loop carrying
    eight of them carries eight atoms. *)
[@@"opaque_to_smt"]
let pw_ok (y yb ym: Vec.t) (h: block) : prop =
  Vec.bv y == h /\ Vec.bv yb == CL.bswap (Vec.bv y) /\
  mix_ok (Vec.bv ym) (CL.bswap (Vec.bv y))

let kmix_ok (z: Vec.t) : Lemma (mix_ok (Vec.bv (kmix z)) (Vec.bv z))
  = Classical.forall_intro (GN.xor_bits z (Vec.shift_right_bytes_8 z));
    CL.fold_lane (Vec.bv z) (Vec.bv (kmix z))

let pw_intro (y: Vec.t) (h: block)
  : Lemma (requires Vec.bv y == h)
          (ensures pw_ok y (Vec.bswap y) (kmix (Vec.bswap y)) h)
  = kmix_ok (Vec.bswap y);
    reveal_opaque (`%pw_ok) (pw_ok y (Vec.bswap y) (kmix (Vec.bswap y)) h)

let pw_y (y yb ym: Vec.t) (h: block)
  : Lemma (requires pw_ok y yb ym h) (ensures Vec.bv y == h)
  = reveal_opaque (`%pw_ok) (pw_ok y yb ym h)

#push-options "--z3rlimit 200"
let kq_ok (x y yb ym: Vec.t) (h: block)
  : Lemma (requires pw_ok y yb ym h)
          (ensures Vec.bv y == h /\
                   Vec.bv (kq_ll x yb) == Vec.bv (GN.kp_ll x y) /\
                   Vec.bv (kq_hh x yb) == Vec.bv (GN.kp_hh x y) /\
                   Vec.bv (kq_mf x ym) == Vec.bv (GN.kp_mf x y))
  = reveal_opaque (`%pw_ok) (pw_ok y yb ym h);
    let xa = Vec.bswap x in
    let ya = Vec.bswap y in
    let xf = kmix xa in
    let yf = kmix ya in
    kmix_ok ya;
    assert (GN.kp_ll x y == Vec.clmul_ll xa ya);
    assert (GN.kp_hh x y == Vec.clmul_hh xa ya);
    assert (GN.kp_mf x y == Vec.clmul_ll xf yf);
    assert (CL.lane (Vec.bv ym) false == CL.lane (Vec.bv yf) false);
    let r1 = kq_ll x yb in
    let r2 = GN.kp_ll x y in
    assert (forall (k: nat). k < 128 ==> CL.lebiti (Vec.bv r1) k == CL.lebiti (Vec.bv r2) k);
    CL.lebits_inj (Vec.bv r1) (Vec.bv r2);
    let r1 = kq_hh x yb in
    let r2 = GN.kp_hh x y in
    assert (forall (k: nat). k < 128 ==> CL.lebiti (Vec.bv r1) k == CL.lebiti (Vec.bv r2) k);
    CL.lebits_inj (Vec.bv r1) (Vec.bv r2);
    let r1 = kq_mf x ym in
    let r2 = GN.kp_mf x y in
    assert (forall (k: nat). k < 128 ==> CL.lebiti (Vec.bv r1) k == CL.lebiti (Vec.bv r2) k);
    CL.lebits_inj (Vec.bv r1) (Vec.bv r2)
#pop-options

(** Nine counter blocks, made the way [NI.inc32_vec] makes them but with
    the counter kept reversed in between, so each is reversed once. *)
let ctr8_sw (b: block) (bi: nat) (one: Vec.t)
            (c0 c1 c2 c3 c4 c5 c6 c7 c8 w0 w1 w2 w3 w4 w5 w6 w7 w8: Vec.t)
  : Lemma (requires Vec.bv c0 == counter_block b bi /\ one == Vec.lane_one () /\
                    w0 == Vec.bswap c0 /\
                    w1 == Vec.add32 w0 one /\ c1 == Vec.bswap w1 /\
                    w2 == Vec.add32 w1 one /\ c2 == Vec.bswap w2 /\
                    w3 == Vec.add32 w2 one /\ c3 == Vec.bswap w3 /\
                    w4 == Vec.add32 w3 one /\ c4 == Vec.bswap w4 /\
                    w5 == Vec.add32 w4 one /\ c5 == Vec.bswap w5 /\
                    w6 == Vec.add32 w5 one /\ c6 == Vec.bswap w6 /\
                    w7 == Vec.add32 w6 one /\ c7 == Vec.bswap w7 /\
                    w8 == Vec.add32 w7 one /\ c8 == Vec.bswap w8)
          (ensures Vec.bv c1 == counter_block b (bi + 1) /\
                   Vec.bv c2 == counter_block b (bi + 2) /\
                   Vec.bv c3 == counter_block b (bi + 3) /\
                   Vec.bv c4 == counter_block b (bi + 4) /\
                   Vec.bv c5 == counter_block b (bi + 5) /\
                   Vec.bv c6 == counter_block b (bi + 6) /\
                   Vec.bv c7 == counter_block b (bi + 7) /\
                   Vec.bv c8 == counter_block b (bi + 8))
  = NI.inc32_sw_ok c0 w0; NI.inc32_sw_ok c1 w1; NI.inc32_sw_ok c2 w2;
    NI.inc32_sw_ok c3 w3; NI.inc32_sw_ok c4 w4; NI.inc32_sw_ok c5 w5;
    NI.inc32_sw_ok c6 w6; NI.inc32_sw_ok c7 w7;
    counter_block_step b bi; counter_block_step b (bi + 1);
    counter_block_step b (bi + 2); counter_block_step b (bi + 3);
    counter_block_step b (bi + 4); counter_block_step b (bi + 5);
    counter_block_step b (bi + 6); counter_block_step b (bi + 7)

let ctr8_ok (b: block) (bi: nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8: Vec.t)
  : Lemma (requires Vec.bv c0 == counter_block b bi /\
                    c1 == NI.inc32_vec c0 /\ c2 == NI.inc32_vec c1 /\
                    c3 == NI.inc32_vec c2 /\ c4 == NI.inc32_vec c3 /\
                    c5 == NI.inc32_vec c4 /\ c6 == NI.inc32_vec c5 /\
                    c7 == NI.inc32_vec c6 /\ c8 == NI.inc32_vec c7)
          (ensures Vec.bv c1 == counter_block b (bi + 1) /\
                   Vec.bv c2 == counter_block b (bi + 2) /\
                   Vec.bv c3 == counter_block b (bi + 3) /\
                   Vec.bv c4 == counter_block b (bi + 4) /\
                   Vec.bv c5 == counter_block b (bi + 5) /\
                   Vec.bv c6 == counter_block b (bi + 6) /\
                   Vec.bv c7 == counter_block b (bi + 7) /\
                   Vec.bv c8 == counter_block b (bi + 8))
  = NI.inc32_vec_ok c0; NI.inc32_vec_ok c1; NI.inc32_vec_ok c2;
    NI.inc32_vec_ok c3; NI.inc32_vec_ok c4; NI.inc32_vec_ok c5;
    NI.inc32_vec_ok c6; NI.inc32_vec_ok c7;
    counter_block_step b bi; counter_block_step b (bi + 1);
    counter_block_step b (bi + 2); counter_block_step b (bi + 3);
    counter_block_step b (bi + 4); counter_block_step b (bi + 5);
    counter_block_step b (bi + 6); counter_block_step b (bi + 7)

let start_ok (v: variant) (w: Seq.lseq elem (xkeylen v)) (k c: Vec.t)
  : Lemma (requires Vec.bv k == round_key v w 0)
          (ensures rounds v w (Vec.bv (Vec.vxor c k)) 1 == cipher v w (Vec.bv c))
  = cipher_start v w (Vec.bv c)

(** The pieces of the result, put back together. *)
#push-options "--z3rlimit 200"
let assemble (v: variant) (w: Seq.lseq elem (xkeylen v)) (b: block) (h a0: G.block)
             (m0 mA mB mC m1: Seq.seq S8.t) (lim: nat)
  : Lemma (requires
      lim <= Seq.length m0 /\ lim % 16 == 0 /\
      Seq.length mA == lim /\ Seq.length mB == Seq.length m0 /\
      Seq.length mC == Seq.length m0 - lim /\ Seq.length m1 == Seq.length m0 /\
      vals mA == ctr_encrypt v w b (vals (Seq.slice m0 0 lim)) /\
      (forall (k: nat). k < Seq.length mB ==>
         Seq.index mB k == (if 0 <= k && k < lim then Seq.index mA (k - 0)
                            else Seq.index m0 k)) /\
      vals mC == ctr_encrypt v w (counter_block b (lim / 16))
                             (vals (Seq.slice mB lim (Seq.length m0))) /\
      (forall (k: nat). k < Seq.length m1 ==>
         Seq.index m1 k == (if lim <= k && k < Seq.length m0
                            then Seq.index mC (k - lim)
                            else Seq.index mB k)))
    (ensures Seq.length (vals mA) % 16 == 0 /\
             vals m1 == ctr_encrypt v w b (vals m0) /\
             G.ghash_upd h (G.ghash_upd h a0 (vals mA)) (GCM.pad (vals mC)) ==
               G.ghash_upd h a0 (GCM.pad (vals m1)))
  = let n = Seq.length m0 in
    vals_slice m0 0 lim;
    vals_slice mB lim n;
    vals_slice m0 lim n;
    Seq.lemma_eq_intro (Seq.slice (vals mB) lim n) (Seq.slice (vals m0) lim n);
    let c1 = vals mA in
    let c2 = vals mC in
    Seq.lemma_eq_intro (vals m1) (Seq.append c1 c2);
    ctr_split v w b (vals m0) lim;
    pad_append c1 c2;
    G.ghash_upd_append h a0 c1 (GCM.pad c2)
#pop-options


(** {2 Registers}

    Everything below is [inline_for_extraction]: the one C function that
    comes out of this module is {!ctr_ghash_ni}, with the whole turn of the
    loop in its body, and the eight cipher states and three GHASH sums are
    its local variables.  The helpers exist so that each is verified against
    a handful of hypotheses rather than everything the turn knows. *)

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
inline_for_extraction
fn load_rk ([@@@FStar.Attributes.monomorphize] p: params)
           (w: A.array S8.t) (i: SZ.t)
           (#vw: erased (Seq.seq S8.t))
requires A.pts_to w vw ** pure (Seq.length vw == xkeylen p.pv /\ SZ.v i <= nr p.pv)
returns k: Vec.t
ensures A.pts_to w vw ** pure (
  Seq.length vw == xkeylen p.pv /\ SZ.v i <= nr p.pv /\
  Vec.bv k == round_key p.pv (vals vw) (SZ.v i))
{
  A.pts_to_len w;
  small_fits (SZ.v i * 16);
  small_fits (SZ.v i * 16 + 16);
  let lo = SZ.mul i 16sz;
  let hi = SZ.add lo 16sz;
  round_key_slice p.pv (vals vw) (SZ.v i);
  vals_slice vw (SZ.v lo) (SZ.v hi);
  let kb = Sub.sub w lo hi;
  let k = Vec.load kb #(NI.as_blk (Seq.slice vw (SZ.v lo) (SZ.v hi)));
  Sub.unsub_id w (SZ.v lo) (SZ.v hi) kb;
  k
}

[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
inline_for_extraction
fn load16 (msg: A.array S8.t) (a: SZ.t) (#vm: erased (Seq.seq S8.t))
requires A.pts_to msg vm ** pure (SZ.v a + 16 <= Seq.length vm /\ SZ.fits (Seq.length vm))
returns r: Vec.t
ensures A.pts_to msg vm ** pure (
  SZ.v a + 16 <= Seq.length vm /\
  Vec.bv r == Seq.slice (vals vm) (SZ.v a) (SZ.v a + 16))
{
  A.pts_to_len msg;
  SZ.fits_lte (SZ.v a + 16) (Seq.length vm);
  let a2 = SZ.add a 16sz;
  let b = Sub.sub msg a a2;
  vals_slice vm (SZ.v a) (SZ.v a2);
  let r = Vec.load b #(NI.as_blk (Seq.slice vm (SZ.v a) (SZ.v a2)));
  Sub.unsub_id msg (SZ.v a) (SZ.v a2) b;
  r
}

(** One [AESENC] round on all eight states. *)
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
inline_for_extraction
fn round8 ([@@@FStar.Attributes.monomorphize] p: params)
          (w: A.array S8.t) (i: SZ.t)
          (r0 r1 r2 r3 r4 r5 r6 r7: ref Vec.t)
          (#vw: erased (Seq.seq S8.t))
          (#u0 #u1 #u2 #u3 #u4 #u5 #u6 #u7: erased Vec.t)
requires A.pts_to w vw **
         pts_to r0 u0 ** pts_to r1 u1 ** pts_to r2 u2 ** pts_to r3 u3 **
         pts_to r4 u4 ** pts_to r5 u5 ** pts_to r6 u6 ** pts_to r7 u7 **
         pure (Seq.length vw == xkeylen p.pv /\ 1 <= SZ.v i /\ SZ.v i < nr p.pv)
ensures exists* (n0 n1 n2 n3 n4 n5 n6 n7: Vec.t).
  A.pts_to w vw **
  pts_to r0 n0 ** pts_to r1 n1 ** pts_to r2 n2 ** pts_to r3 n3 **
  pts_to r4 n4 ** pts_to r5 n5 ** pts_to r6 n6 ** pts_to r7 n7 **
  pure (Seq.length vw == xkeylen p.pv /\ 1 <= SZ.v i /\ SZ.v i < nr p.pv /\
        rounds p.pv (vals vw) (Vec.bv u0) (SZ.v i) == rounds p.pv (vals vw) (Vec.bv n0) (SZ.v i + 1) /\
        rounds p.pv (vals vw) (Vec.bv u1) (SZ.v i) == rounds p.pv (vals vw) (Vec.bv n1) (SZ.v i + 1) /\
        rounds p.pv (vals vw) (Vec.bv u2) (SZ.v i) == rounds p.pv (vals vw) (Vec.bv n2) (SZ.v i + 1) /\
        rounds p.pv (vals vw) (Vec.bv u3) (SZ.v i) == rounds p.pv (vals vw) (Vec.bv n3) (SZ.v i + 1) /\
        rounds p.pv (vals vw) (Vec.bv u4) (SZ.v i) == rounds p.pv (vals vw) (Vec.bv n4) (SZ.v i + 1) /\
        rounds p.pv (vals vw) (Vec.bv u5) (SZ.v i) == rounds p.pv (vals vw) (Vec.bv n5) (SZ.v i + 1) /\
        rounds p.pv (vals vw) (Vec.bv u6) (SZ.v i) == rounds p.pv (vals vw) (Vec.bv n6) (SZ.v i + 1) /\
        rounds p.pv (vals vw) (Vec.bv u7) (SZ.v i) == rounds p.pv (vals vw) (Vec.bv n7) (SZ.v i + 1))
{
  let k = load_rk p w i;
  rounds_step p.pv (vals vw) (Vec.bv u0) (SZ.v i);
  rounds_step p.pv (vals vw) (Vec.bv u1) (SZ.v i);
  rounds_step p.pv (vals vw) (Vec.bv u2) (SZ.v i);
  rounds_step p.pv (vals vw) (Vec.bv u3) (SZ.v i);
  rounds_step p.pv (vals vw) (Vec.bv u4) (SZ.v i);
  rounds_step p.pv (vals vw) (Vec.bv u5) (SZ.v i);
  rounds_step p.pv (vals vw) (Vec.bv u6) (SZ.v i);
  rounds_step p.pv (vals vw) (Vec.bv u7) (SZ.v i);
  let v0 = !r0; r0 := Vec.aesenc v0 k;
  let v1 = !r1; r1 := Vec.aesenc v1 k;
  let v2 = !r2; r2 := Vec.aesenc v2 k;
  let v3 = !r3; r3 := Vec.aesenc v3 k;
  let v4 = !r4; r4 := Vec.aesenc v4 k;
  let v5 = !r5; r5 := Vec.aesenc v5 k;
  let v6 = !r6; r6 := Vec.aesenc v6 k;
  let v7 = !r7; r7 := Vec.aesenc v7 k;
}

(** One Karatsuba triple, added into the three running sums. *)
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
inline_for_extraction
fn gpart (rl rh rm: ref Vec.t) (x yb ym: Vec.t) (#l0 #h0 #m0: erased Vec.t)
requires pts_to rl l0 ** pts_to rh h0 ** pts_to rm m0
ensures pts_to rl (Vec.vxor l0 (kq_ll x yb)) **
        pts_to rh (Vec.vxor h0 (kq_hh x yb)) **
        pts_to rm (Vec.vxor m0 (kq_mf x ym))
{
  let l = !rl;
  let h = !rh;
  let m = !rm;
  rl := Vec.vxor l (kq_ll x yb);
  rh := Vec.vxor h (kq_hh x yb);
  rm := Vec.vxor m (kq_mf x ym);
}

(** The cipher's remaining rounds -- none for AES-128, four for AES-256 --
    then the last round, and the eight keystream blocks exclusive-ored into
    the message. *)
#push-options "--z3rlimit 400"
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
inline_for_extraction
fn aes_fin ([@@@FStar.Attributes.monomorphize] p: params)
           (msg: A.array S8.t) (j: SZ.t) (w: A.array S8.t)
           (r0 r1 r2 r3 r4 r5 r6 r7: ref Vec.t)
           (m0: erased (Seq.seq elem)) (b0: erased block) (bi: erased nat)
           (c0 c1 c2 c3 c4 c5 c6 c7: erased Vec.t)
           (#vm #vw: erased (Seq.seq S8.t))
           (#u0 #u1 #u2 #u3 #u4 #u5 #u6 #u7: erased Vec.t)
requires A.pts_to msg vm ** A.pts_to w vw **
         pts_to r0 u0 ** pts_to r1 u1 ** pts_to r2 u2 ** pts_to r3 u3 **
         pts_to r4 u4 ** pts_to r5 u5 ** pts_to r6 u6 ** pts_to r7 u7 **
  pure (Seq.length vw == xkeylen p.pv /\
        SZ.v j == 16 * bi /\ SZ.v j + 128 <= Seq.length m0 /\
        SZ.fits (Seq.length m0) /\
        ctr_inv p.pv (vals vw) b0 m0 (vals vm) (SZ.v j) /\
        Vec.bv c0 == counter_block b0 (bi + 0) /\
        Vec.bv c1 == counter_block b0 (bi + 1) /\
        Vec.bv c2 == counter_block b0 (bi + 2) /\
        Vec.bv c3 == counter_block b0 (bi + 3) /\
        Vec.bv c4 == counter_block b0 (bi + 4) /\
        Vec.bv c5 == counter_block b0 (bi + 5) /\
        Vec.bv c6 == counter_block b0 (bi + 6) /\
        Vec.bv c7 == counter_block b0 (bi + 7) /\
        rounds p.pv (vals vw) (Vec.bv u0) 10 == cipher p.pv (vals vw) (Vec.bv c0) /\
        rounds p.pv (vals vw) (Vec.bv u1) 10 == cipher p.pv (vals vw) (Vec.bv c1) /\
        rounds p.pv (vals vw) (Vec.bv u2) 10 == cipher p.pv (vals vw) (Vec.bv c2) /\
        rounds p.pv (vals vw) (Vec.bv u3) 10 == cipher p.pv (vals vw) (Vec.bv c3) /\
        rounds p.pv (vals vw) (Vec.bv u4) 10 == cipher p.pv (vals vw) (Vec.bv c4) /\
        rounds p.pv (vals vw) (Vec.bv u5) 10 == cipher p.pv (vals vw) (Vec.bv c5) /\
        rounds p.pv (vals vw) (Vec.bv u6) 10 == cipher p.pv (vals vw) (Vec.bv c6) /\
        rounds p.pv (vals vw) (Vec.bv u7) 10 == cipher p.pv (vals vw) (Vec.bv c7))
ensures exists* (vm': Seq.seq S8.t) (n0 n1 n2 n3 n4 n5 n6 n7: Vec.t).
  A.pts_to msg vm' ** A.pts_to w vw **
  pts_to r0 n0 ** pts_to r1 n1 ** pts_to r2 n2 ** pts_to r3 n3 **
  pts_to r4 n4 ** pts_to r5 n5 ** pts_to r6 n6 ** pts_to r7 n7 **
  pure (Seq.length vw == xkeylen p.pv /\
        ctr_inv p.pv (vals vw) b0 m0 (vals vm') (SZ.v j + 128))
{
  A.pts_to_len msg;
  let mut i = 10sz;
  while (let vi = !i; SZ.lt vi p.pnr)
  invariant exists* (vi: SZ.t) (v0 v1 v2 v3 v4 v5 v6 v7: Vec.t).
    pts_to i vi ** A.pts_to w vw **
    pts_to r0 v0 ** pts_to r1 v1 ** pts_to r2 v2 ** pts_to r3 v3 **
    pts_to r4 v4 ** pts_to r5 v5 ** pts_to r6 v6 ** pts_to r7 v7 **
    pure (10 <= SZ.v vi /\ SZ.v vi <= nr p.pv /\ Seq.length vw == xkeylen p.pv /\
          rounds p.pv (vals vw) (Vec.bv v0) (SZ.v vi) == cipher p.pv (vals vw) (Vec.bv c0) /\
          rounds p.pv (vals vw) (Vec.bv v1) (SZ.v vi) == cipher p.pv (vals vw) (Vec.bv c1) /\
          rounds p.pv (vals vw) (Vec.bv v2) (SZ.v vi) == cipher p.pv (vals vw) (Vec.bv c2) /\
          rounds p.pv (vals vw) (Vec.bv v3) (SZ.v vi) == cipher p.pv (vals vw) (Vec.bv c3) /\
          rounds p.pv (vals vw) (Vec.bv v4) (SZ.v vi) == cipher p.pv (vals vw) (Vec.bv c4) /\
          rounds p.pv (vals vw) (Vec.bv v5) (SZ.v vi) == cipher p.pv (vals vw) (Vec.bv c5) /\
          rounds p.pv (vals vw) (Vec.bv v6) (SZ.v vi) == cipher p.pv (vals vw) (Vec.bv c6) /\
          rounds p.pv (vals vw) (Vec.bv v7) (SZ.v vi) == cipher p.pv (vals vw) (Vec.bv c7))
  decreases (nr p.pv - SZ.v (!i))
  {
    let vi = !i;
    round8 p w vi r0 r1 r2 r3 r4 r5 r6 r7;
    i := SZ.add vi 1sz;
  };

  let kl = load_rk p w p.pnr;
  let v0 = !r0;
  let v1 = !r1;
  let v2 = !r2;
  let v3 = !r3;
  let v4 = !r4;
  let v5 = !r5;
  let v6 = !r6;
  let v7 = !r7;
  let e0 = Vec.aesenclast v0 kl;
  fin_eq p.pv (vals vw) (Vec.bv v0) (Vec.bv c0) (Vec.bv e0) (Vec.bv kl) b0 (bi + 0);
  let e1 = Vec.aesenclast v1 kl;
  fin_eq p.pv (vals vw) (Vec.bv v1) (Vec.bv c1) (Vec.bv e1) (Vec.bv kl) b0 (bi + 1);
  let e2 = Vec.aesenclast v2 kl;
  fin_eq p.pv (vals vw) (Vec.bv v2) (Vec.bv c2) (Vec.bv e2) (Vec.bv kl) b0 (bi + 2);
  let e3 = Vec.aesenclast v3 kl;
  fin_eq p.pv (vals vw) (Vec.bv v3) (Vec.bv c3) (Vec.bv e3) (Vec.bv kl) b0 (bi + 3);
  let e4 = Vec.aesenclast v4 kl;
  fin_eq p.pv (vals vw) (Vec.bv v4) (Vec.bv c4) (Vec.bv e4) (Vec.bv kl) b0 (bi + 4);
  let e5 = Vec.aesenclast v5 kl;
  fin_eq p.pv (vals vw) (Vec.bv v5) (Vec.bv c5) (Vec.bv e5) (Vec.bv kl) b0 (bi + 5);
  let e6 = Vec.aesenclast v6 kl;
  fin_eq p.pv (vals vw) (Vec.bv v6) (Vec.bv c6) (Vec.bv e6) (Vec.bv kl) b0 (bi + 6);
  let e7 = Vec.aesenclast v7 kl;
  fin_eq p.pv (vals vw) (Vec.bv v7) (Vec.bv c7) (Vec.bv e7) (Vec.bv kl) b0 (bi + 7);

  SZ.fits_lte (SZ.v j + 128) (Seq.length m0);
  let j1 = SZ.add j 16sz;
  let j2 = SZ.add j 32sz;
  let j3 = SZ.add j 48sz;
  let j4 = SZ.add j 64sz;
  let j5 = SZ.add j 80sz;
  let j6 = SZ.add j 96sz;
  let j7 = SZ.add j 112sz;
  assert (pure (SZ.v j == 16 * (bi + 0) /\
                SZ.v j1 == 16 * (bi + 1) /\ SZ.v j2 == 16 * (bi + 2) /\
                SZ.v j3 == 16 * (bi + 3) /\ SZ.v j4 == 16 * (bi + 4) /\
                SZ.v j5 == 16 * (bi + 5) /\ SZ.v j6 == 16 * (bi + 6) /\
                SZ.v j7 == 16 * (bi + 7)));

  NI.xor_at_ni msg j e0;
  with vmA. assert A.pts_to msg vmA;
  ctr1_step p.pv (vals vw) b0 m0 (vals vm) (vals vmA) (SZ.v j) (bi + 0) (Vec.bv e0);
  NI.xor_at_ni msg j1 e1;
  with vmB. assert A.pts_to msg vmB;
  ctr1_step p.pv (vals vw) b0 m0 (vals vmA) (vals vmB) (SZ.v j1) (bi + 1) (Vec.bv e1);
  NI.xor_at_ni msg j2 e2;
  with vmC. assert A.pts_to msg vmC;
  ctr1_step p.pv (vals vw) b0 m0 (vals vmB) (vals vmC) (SZ.v j2) (bi + 2) (Vec.bv e2);
  NI.xor_at_ni msg j3 e3;
  with vmD. assert A.pts_to msg vmD;
  ctr1_step p.pv (vals vw) b0 m0 (vals vmC) (vals vmD) (SZ.v j3) (bi + 3) (Vec.bv e3);
  NI.xor_at_ni msg j4 e4;
  with vmE. assert A.pts_to msg vmE;
  ctr1_step p.pv (vals vw) b0 m0 (vals vmD) (vals vmE) (SZ.v j4) (bi + 4) (Vec.bv e4);
  NI.xor_at_ni msg j5 e5;
  with vmF. assert A.pts_to msg vmF;
  ctr1_step p.pv (vals vw) b0 m0 (vals vmE) (vals vmF) (SZ.v j5) (bi + 5) (Vec.bv e5);
  NI.xor_at_ni msg j6 e6;
  with vmG. assert A.pts_to msg vmG;
  ctr1_step p.pv (vals vw) b0 m0 (vals vmF) (vals vmG) (SZ.v j6) (bi + 6) (Vec.bv e6);
  NI.xor_at_ni msg j7 e7;
  with vmH. assert A.pts_to msg vmH;
  ctr1_step p.pv (vals vw) b0 m0 (vals vmG) (vals vmH) (SZ.v j7) (bi + 7) (Vec.bv e7);
  ctr_inv_cong p.pv (vals vw) b0 m0 (vals vmH) (SZ.v j7 + 16) (SZ.v j + 128);
  ()
}
#pop-options


(** {2 One turn}

    Encrypt bytes [j] to [j + 128] and hash bytes [j - 128] to [j], the
    ciphertext the previous turn wrote.  The counter and the accumulator
    live in registers across turns. *)

#push-options "--z3rlimit 400"
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
inline_for_extraction
fn stitch8 ([@@@FStar.Attributes.monomorphize] p: params)
           (msg: A.array S8.t) (j: SZ.t) (w: A.array S8.t) (hk: A.array S8.t)
           (rc: ref Vec.t) (ra: ref Vec.t)
           (m0: erased (Seq.seq elem)) (b0: erased block) (a0: erased G.block)
           (y y2 y3 y4 y5 y6 y7 y8: erased Vec.t)
           (yb1 ym1 yb2 ym2 yb3 ym3 yb4 ym4 yb5 ym5 yb6 ym6 yb7 ym7 yb8 ym8: Vec.t)
           (#vm #vw #vh: erased (Seq.seq S8.t)) (#vc #va: erased Vec.t)
requires A.pts_to msg vm ** A.pts_to w vw ** A.pts_to hk vh **
         pts_to rc vc ** pts_to ra va ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\ Alg.pows_ok (vals vh) /\
  pw_ok y yb1 ym1 (Alg.hblk (vals vh) 0) /\ pw_ok y2 yb2 ym2 (Alg.hblk (vals vh) 1) /\
  pw_ok y3 yb3 ym3 (Alg.hblk (vals vh) 2) /\ pw_ok y4 yb4 ym4 (Alg.hblk (vals vh) 3) /\
  pw_ok y5 yb5 ym5 (Alg.hblk (vals vh) 4) /\ pw_ok y6 yb6 ym6 (Alg.hblk (vals vh) 5) /\
  pw_ok y7 yb7 ym7 (Alg.hblk (vals vh) 6) /\ pw_ok y8 yb8 ym8 (Alg.hblk (vals vh) 7) /\
  SZ.v j % 128 == 0 /\ 128 <= SZ.v j /\ SZ.v j + 128 <= Seq.length m0 /\
  SZ.fits (Seq.length m0) /\
  Vec.bv vc == counter_block b0 (SZ.v j / 16) /\
  ctr_inv p.pv (vals vw) b0 m0 (vals vm) (SZ.v j) /\
  Vec.bv va == gh_prefix (Poly.xtimes (Alg.hblk (vals vh) 0)) a0
                         (ctr_encrypt p.pv (vals vw) b0 m0) (SZ.v j - 128))
ensures exists* (vm': Seq.seq S8.t) (vc' va': Vec.t).
  A.pts_to msg vm' ** A.pts_to w vw ** A.pts_to hk vh **
  pts_to rc vc' ** pts_to ra va' ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\
  Vec.bv vc' == counter_block b0 ((SZ.v j + 128) / 16) /\
  ctr_inv p.pv (vals vw) b0 m0 (vals vm') (SZ.v j + 128) /\
  Vec.bv va' == gh_prefix (Poly.xtimes (Alg.hblk (vals vh) 0)) a0
                          (ctr_encrypt p.pv (vals vw) b0 m0) (SZ.v j))
{
  A.pts_to_len msg;
  A.pts_to_len w;
  A.pts_to_len hk;
  vals_len vh;
  j_facts (SZ.v j);
  assert (pure (SZ.v j / 16 >= 0 /\ (SZ.v j + 128) / 16 >= 0));

  (* The eight counter blocks, and the next one, in registers. *)
  let c0 = !rc;
  let one = Vec.lane_one ();
  let w0 = Vec.bswap c0;
  let w1 = Vec.add32 w0 one;
  let w2 = Vec.add32 w1 one;
  let w3 = Vec.add32 w2 one;
  let w4 = Vec.add32 w3 one;
  let w5 = Vec.add32 w4 one;
  let w6 = Vec.add32 w5 one;
  let w7 = Vec.add32 w6 one;
  let w8 = Vec.add32 w7 one;
  let c1 = Vec.bswap w1;
  let c2 = Vec.bswap w2;
  let c3 = Vec.bswap w3;
  let c4 = Vec.bswap w4;
  let c5 = Vec.bswap w5;
  let c6 = Vec.bswap w6;
  let c7 = Vec.bswap w7;
  let c8 = Vec.bswap w8;
  ctr8_sw b0 (SZ.v j / 16) one c0 c1 c2 c3 c4 c5 c6 c7 c8 w0 w1 w2 w3 w4 w5 w6 w7 w8;
  rc := c8;

  (* Round zero. *)
  let k0 = load_rk p w 0sz;
  start_ok p.pv (vals vw) k0 c0;
  start_ok p.pv (vals vw) k0 c1;
  start_ok p.pv (vals vw) k0 c2;
  start_ok p.pv (vals vw) k0 c3;
  start_ok p.pv (vals vw) k0 c4;
  start_ok p.pv (vals vw) k0 c5;
  start_ok p.pv (vals vw) k0 c6;
  start_ok p.pv (vals vw) k0 c7;
  let mut s0 = Vec.vxor c0 k0;
  let mut s1 = Vec.vxor c1 k0;
  let mut s2 = Vec.vxor c2 k0;
  let mut s3 = Vec.vxor c3 k0;
  let mut s4 = Vec.vxor c4 k0;
  let mut s5 = Vec.vxor c5 k0;
  let mut s6 = Vec.vxor c6 k0;
  let mut s7 = Vec.vxor c7 k0;

  (* Rounds one to eight, each followed by one block's GHASH product. *)
  round8 p w 1sz s0 s1 s2 s3 s4 s5 s6 s7;
  let a = !ra;
  let d0 = load16 msg (SZ.sub j 128sz);
  let x1 = Vec.vxor a d0;
  let mut ll = kq_ll x1 yb8;
  let mut hh = kq_hh x1 yb8;
  let mut mf = kq_mf x1 ym8;

  round8 p w 2sz s0 s1 s2 s3 s4 s5 s6 s7;
  let d1 = load16 msg (SZ.sub j 112sz);
  gpart ll hh mf d1 yb7 ym7;

  round8 p w 3sz s0 s1 s2 s3 s4 s5 s6 s7;
  let d2 = load16 msg (SZ.sub j 96sz);
  gpart ll hh mf d2 yb6 ym6;

  round8 p w 4sz s0 s1 s2 s3 s4 s5 s6 s7;
  let d3 = load16 msg (SZ.sub j 80sz);
  gpart ll hh mf d3 yb5 ym5;

  round8 p w 5sz s0 s1 s2 s3 s4 s5 s6 s7;
  let d4 = load16 msg (SZ.sub j 64sz);
  gpart ll hh mf d4 yb4 ym4;

  round8 p w 6sz s0 s1 s2 s3 s4 s5 s6 s7;
  let d5 = load16 msg (SZ.sub j 48sz);
  gpart ll hh mf d5 yb3 ym3;

  round8 p w 7sz s0 s1 s2 s3 s4 s5 s6 s7;
  let d6 = load16 msg (SZ.sub j 32sz);
  gpart ll hh mf d6 yb2 ym2;

  round8 p w 8sz s0 s1 s2 s3 s4 s5 s6 s7;
  let d7 = load16 msg (SZ.sub j 16sz);
  gpart ll hh mf d7 yb1 ym1;

  round8 p w 9sz s0 s1 s2 s3 s4 s5 s6 s7;

  (* The GHASH side's facts, gathered before the message changes. *)
  ctr_slice p.pv (vals vw) b0 m0 (vals vm) (SZ.v j) (SZ.v j - 128) (SZ.v j);

  aes_fin p msg j w s0 s1 s2 s3 s4 s5 s6 s7 m0 b0 (SZ.v j / 16)
          c0 c1 c2 c3 c4 c5 c6 c7;

  (* The reduction. *)
  let ls = !ll;
  let hs = !hh;
  let ms = !mf;
  GN.xor_left8 (kq_ll x1 yb8) (kq_ll d1 yb7) (kq_ll d2 yb6) (kq_ll d3 yb5)
               (kq_ll d4 yb4) (kq_ll d5 yb3) (kq_ll d6 yb2) (kq_ll d7 yb1);
  GN.xor_left8 (kq_hh x1 yb8) (kq_hh d1 yb7) (kq_hh d2 yb6) (kq_hh d3 yb5)
               (kq_hh d4 yb4) (kq_hh d5 yb3) (kq_hh d6 yb2) (kq_hh d7 yb1);
  GN.xor_left8 (kq_mf x1 ym8) (kq_mf d1 ym7) (kq_mf d2 ym6) (kq_mf d3 ym5)
               (kq_mf d4 ym4) (kq_mf d5 ym3) (kq_mf d6 ym2) (kq_mf d7 ym1);
  kq_ok x1 y8 yb8 ym8 (Alg.hblk (vals vh) 7);
  kq_ok d1 y7 yb7 ym7 (Alg.hblk (vals vh) 6);
  kq_ok d2 y6 yb6 ym6 (Alg.hblk (vals vh) 5);
  kq_ok d3 y5 yb5 ym5 (Alg.hblk (vals vh) 4);
  kq_ok d4 y4 yb4 ym4 (Alg.hblk (vals vh) 3);
  kq_ok d5 y3 yb3 ym3 (Alg.hblk (vals vh) 2);
  kq_ok d6 y2 yb2 ym2 (Alg.hblk (vals vh) 1);
  kq_ok d7 y yb1 ym1 (Alg.hblk (vals vh) 0);
  let r = GN.gmul8_fin x1 y8 d1 y7 d2 y6 d3 y5 d4 y4 d5 y3 d6 y2 d7 y ls hs ms;
  gh_chunk (vals vh) a0 (ctr_encrypt p.pv (vals vw) b0 m0) (vals vm) (SZ.v j)
           a d0 d1 d2 d3 d4 d5 d6 d7 y y2 y3 y4 y5 y6 y7 y8 r;
  ra := r;
}
#pop-options

(* The block index of byte offset [j], typed once here so that the loop
   invariant below need not re-prove [j / 16 >= 0] in a large context. *)
let jblk (j: nat) : nat = j / 16

let jblk_spec (j: nat) : Lemma (jblk j == j / 16) = ()

let jblk_128 () : Lemma (jblk 128 == 4 + 4) = assert_norm (jblk 128 == 4 + 4)


(** {2 The loop}

    [n] is a positive multiple of 128.  The ciphertext is written in place;
    [ctr] comes back advanced past it and [acc] with it hashed in. *)

#push-options "--z3rlimit 400"
[@@CPrologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_prologue "__attribute__((target(\"aes,pclmul,ssse3,sse4.1\")))";
  custard_c_closure_guard "defined(__x86_64__)"]
fn ctr_ghash_ni ([@@@FStar.Attributes.monomorphize] p: params)
                (msg: A.array S8.t) (n: SZ.t) (w: A.array S8.t) (hk: A.array S8.t)
                (ctr: A.array S8.t) (acc: A.array S8.t)
                (#vm0 #vw #vh #vc0 #va0: erased (Seq.seq S8.t))
requires A.pts_to msg vm0 ** A.pts_to w vw ** A.pts_to hk vh **
         A.pts_to ctr vc0 ** A.pts_to acc va0 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\ Alg.pows_ok (vals vh) /\
  Seq.length vc0 == blocklen /\ Seq.length va0 == blocklen /\
  SZ.v n == Seq.length vm0 /\ SZ.v n % 128 == 0 /\ 128 <= SZ.v n)
ensures exists* (vm1 vc1 va1: Seq.seq S8.t).
  A.pts_to msg vm1 ** A.pts_to w vw ** A.pts_to hk vh **
  A.pts_to ctr vc1 ** A.pts_to acc va1 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\
  Seq.length vc0 == blocklen /\ Seq.length va0 == blocklen /\
  Seq.length vc1 == blocklen /\ Seq.length va1 == blocklen /\
  Seq.length vm1 == Seq.length vm0 /\ Seq.length vm1 % 16 == 0 /\
  vals vm1 == ctr_encrypt p.pv (vals vw) (vals vc0) (vals vm0) /\
  vals vc1 == counter_block (vals vc0) (SZ.v n / 16) /\
  vals va1 == G.ghash_upd (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0) (vals vm1))
{
  A.pts_to_len msg;
  A.pts_to_len w;
  A.pts_to_len hk;
  A.pts_to_len ctr;
  A.pts_to_len acc;
  vals_len vh;
  j_facts (SZ.v n);
  assert (pure (SZ.v n / 16 >= 0));
  counter_block_zero (vals vc0);

  (* The first 128 bytes: counter mode only, there being nothing yet to
     hash. *)
  NI.ctr_block4_ni p msg 0sz w ctr;
  with vmA. assert A.pts_to msg vmA;
  ctr4_step p.pv (vals vw) (vals vc0) (vals vm0) (vals vm0) (vals vmA)
            (SZ.v n) 0 0 (vals vc0);
  with vcA. assert A.pts_to ctr vcA;
  NI.ctr_block4_ni p msg 64sz w ctr;
  with vmB. assert A.pts_to msg vmB;
  ctr4_step p.pv (vals vw) (vals vc0) (vals vm0) (vals vmA) (vals vmB)
            (SZ.v n) 64 4 (vals vcA);
  counter_block_add (vals vc0) 4 4;
  jblk_128 ();
  ctr_inv_def p.pv (vals vw) (vals vc0) (vals vm0) (vals vmB) 128;
  with vcB. assert A.pts_to ctr vcB;

  let cv = Vec.load ctr #(NI.as_blk vcB);
  let av = Vec.load acc #(NI.as_blk va0);
  gh_prefix_zero (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0)
                 (ctr_encrypt p.pv (vals vw) (vals vc0) (vals vm0));
  let y = GN.load_pow hk 0sz;
  let y2 = GN.load_pow hk 1sz;
  let y3 = GN.load_pow hk 2sz;
  let y4 = GN.load_pow hk 3sz;
  let y5 = GN.load_pow hk 4sz;
  let y6 = GN.load_pow hk 5sz;
  let y7 = GN.load_pow hk 6sz;
  let y8 = GN.load_pow hk 7sz;
  let yb1 = Vec.bswap y;  let ym1 = kmix yb1;
  let yb2 = Vec.bswap y2; let ym2 = kmix yb2;
  let yb3 = Vec.bswap y3; let ym3 = kmix yb3;
  let yb4 = Vec.bswap y4; let ym4 = kmix yb4;
  let yb5 = Vec.bswap y5; let ym5 = kmix yb5;
  let yb6 = Vec.bswap y6; let ym6 = kmix yb6;
  let yb7 = Vec.bswap y7; let ym7 = kmix yb7;
  let yb8 = Vec.bswap y8; let ym8 = kmix yb8;
  pw_intro y (Alg.hblk (vals vh) 0); pw_intro y2 (Alg.hblk (vals vh) 1);
  pw_intro y3 (Alg.hblk (vals vh) 2); pw_intro y4 (Alg.hblk (vals vh) 3);
  pw_intro y5 (Alg.hblk (vals vh) 4); pw_intro y6 (Alg.hblk (vals vh) 5);
  pw_intro y7 (Alg.hblk (vals vh) 6); pw_intro y8 (Alg.hblk (vals vh) 7);

  let mut rc = cv;
  let mut ra = av;
  let mut j = 128sz;

  while (let vj = !j; SZ.lt vj n)
  invariant exists* (vj: SZ.t) (vm: Seq.seq S8.t) (vc va: Vec.t).
    pts_to j vj ** A.pts_to msg vm ** A.pts_to w vw ** A.pts_to hk vh **
    A.pts_to ctr vcB ** A.pts_to acc va0 ** pts_to rc vc ** pts_to ra va **
    pure (128 <= SZ.v vj /\ SZ.v vj <= SZ.v n /\ SZ.v vj % 128 == 0 /\
          Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\
          Alg.pows_ok (vals vh) /\ Seq.length vcB == blocklen /\
          pw_ok y yb1 ym1 (Alg.hblk (vals vh) 0) /\ pw_ok y2 yb2 ym2 (Alg.hblk (vals vh) 1) /\
          pw_ok y3 yb3 ym3 (Alg.hblk (vals vh) 2) /\ pw_ok y4 yb4 ym4 (Alg.hblk (vals vh) 3) /\
          pw_ok y5 yb5 ym5 (Alg.hblk (vals vh) 4) /\ pw_ok y6 yb6 ym6 (Alg.hblk (vals vh) 5) /\
          pw_ok y7 yb7 ym7 (Alg.hblk (vals vh) 6) /\ pw_ok y8 yb8 ym8 (Alg.hblk (vals vh) 7) /\
          Seq.length va0 == blocklen /\ SZ.v n == Seq.length vm0 /\
          Vec.bv vc == counter_block (vals vc0) (jblk (SZ.v vj)) /\
          ctr_inv p.pv (vals vw) (vals vc0) (vals vm0) (vals vm) (SZ.v vj) /\
          Vec.bv va == gh_prefix (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0)
                                 (ctr_encrypt p.pv (vals vw) (vals vc0) (vals vm0))
                                 (SZ.v vj - 128))
  decreases (SZ.v n - SZ.v (!j))
  {
    let vj = !j;
    step_bounds (SZ.v vj) (SZ.v n);
    j_facts (SZ.v vj);
    jblk_spec (SZ.v vj);
    stitch8 p msg vj w hk rc ra (vals vm0) (vals vc0) (vals va0)
            y y2 y3 y4 y5 y6 y7 y8
            yb1 ym1 yb2 ym2 yb3 ym3 yb4 ym4 yb5 ym5 yb6 ym6 yb7 ym7 yb8 ym8;
    let nj = SZ.add vj 128sz;
    assert pure (SZ.v nj - 128 == SZ.v vj);
    jblk_spec (SZ.v nj);
    j := nj;
  };

  (* The last 128 bytes: GHASH only. *)
  jblk_spec (SZ.v n);
  with vm. assert A.pts_to msg vm;
  ctr_fin p.pv (vals vw) (vals vc0) (vals vm0) (vals vm);
  let vc = !rc;
  let va = !ra;
  Vec.store ctr vc #(NI.as_blk vcB);
  vals_len (Vec.vv vc);

  pw_y y yb1 ym1 (Alg.hblk (vals vh) 0); pw_y y2 yb2 ym2 (Alg.hblk (vals vh) 1);
  pw_y y3 yb3 ym3 (Alg.hblk (vals vh) 2); pw_y y4 yb4 ym4 (Alg.hblk (vals vh) 3);
  pw_y y5 yb5 ym5 (Alg.hblk (vals vh) 4); pw_y y6 yb6 ym6 (Alg.hblk (vals vh) 5);
  pw_y y7 yb7 ym7 (Alg.hblk (vals vh) 6); pw_y y8 yb8 ym8 (Alg.hblk (vals vh) 7);
  let nm = SZ.sub n 128sz;
  let db = Sub.sub msg nm n;
  vals_slice vm (SZ.v nm) (SZ.v n);
  let r = GN.ghash_loop8_ni va y y2 y3 y4 y5 y6 y7 y8 db 128sz 128sz;
  Sub.unsub_id msg (SZ.v nm) (SZ.v n) db;
  gh_last (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0) (vals vm) (SZ.v n)
          (Vec.bv va) (Vec.bv r) (vals (Seq.slice vm (SZ.v nm) (SZ.v n)));
  Vec.store acc r #(NI.as_blk va0);
  vals_len (Vec.vv r);
  ()
}
#pop-options


(** {2 Any length}

    The largest multiple of 128 bytes goes through the stitched loop; the
    rest, fewer than 128 bytes, through the two-pass path.  The accumulator
    comes back with the whole padded ciphertext hashed in, which is what
    [Hacl.AES.GCM] wants between the associated data and the length block. *)

#push-options "--z3rlimit 400"
[@@custard_c_closure_prologue "";
  custard_c_closure_guard "defined(__x86_64__)"]
fn ctr_ghash ([@@@FStar.Attributes.monomorphize] p: params)
             (msg: A.array S8.t) (n: SZ.t) (w: A.array S8.t) (hk: A.array S8.t)
             (ctr: A.array S8.t) (acc: A.array S8.t)
             (#vm0 #vw #vh #vc0 #va0: erased (Seq.seq S8.t))
requires A.pts_to msg vm0 ** A.pts_to w vw ** A.pts_to hk vh **
         A.pts_to ctr vc0 ** A.pts_to acc va0 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\ Alg.pows_ok (vals vh) /\
  Seq.length vc0 == blocklen /\ Seq.length va0 == blocklen /\
  SZ.v n == Seq.length vm0 /\ 128 <= SZ.v n /\ SZ.fits (SZ.v n + blocklen))
ensures exists* (vm1 vc1 va1: Seq.seq S8.t).
  A.pts_to msg vm1 ** A.pts_to w vw ** A.pts_to hk vh **
  A.pts_to ctr vc1 ** A.pts_to acc va1 ** pure (
  Seq.length vw == xkeylen p.pv /\ Seq.length vh == 128 /\
  Seq.length vc0 == blocklen /\ Seq.length va0 == blocklen /\
  Seq.length vc1 == blocklen /\ Seq.length va1 == blocklen /\
  Seq.length vm1 == Seq.length vm0 /\
  vals vm1 == ctr_encrypt p.pv (vals vw) (vals vc0) (vals vm0) /\
  vals va1 == G.ghash_upd (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0)
                          (GCM.pad (vals vm1)))
{
  A.pts_to_len msg;
  lim_facts (SZ.v n);
  let lim = SZ.sub n (SZ.rem n 128sz);

  let mb = Sub.sub msg 0sz lim;
  ctr_ghash_ni p mb lim w hk ctr acc;
  with vmA. assert A.pts_to mb vmA;
  with vaA. assert A.pts_to acc vaA;
  Sub.unsub msg 0 (SZ.v lim) mb;
  with vmB. assert A.pts_to msg vmB;

  let tl = SZ.sub n lim;
  let tb = Sub.sub msg lim n;
  ctr_encrypt_impl p tb tl w ctr;
  with vmC. assert A.pts_to tb vmC;
  Hacl.AES.GHash.ghash_upd_impl acc hk tb tl;
  Sub.unsub msg (SZ.v lim) (SZ.v n) tb;
  with vm1. assert A.pts_to msg vm1;
  assemble p.pv (vals vw) (vals vc0) (Poly.xtimes (Alg.hblk (vals vh) 0)) (vals va0)
           vm0 vmA vmB vmC vm1 (SZ.v lim);
  ()
}
#pop-options

#pop-options
