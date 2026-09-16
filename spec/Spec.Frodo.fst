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

(** FrodoKEM: the specification.

    Learning with errors over a plain lattice -- no ring, no module, no
    structure to exploit -- which is what makes FrodoKEM conservative and
    also what makes it large.  Everything below is matrix arithmetic modulo
    [2^16] and SHAKE.

    The construction, in one paragraph.  The public key is a seed for a big
    square matrix A together with B = A S + E, where S and E are small.  To
    encapsulate, draw S', E', E'' small, send B' = S' A + E' and
    C = S' B + E'' + encode(mu), and take the shared secret from mu.  To
    decapsulate, compute C - B' S, which is E'' + encode(mu) - E' S plus a
    small error, round it back to mu, then {i re-encrypt} with the same
    randomness mu determines and check that the result is the ciphertext
    received.  That last step is the Fujisaki-Okamoto transform, and it is
    why decapsulation costs as much as encapsulation.

    Three details that are easy to get wrong and that the known answer tests
    pin down:

    - A is expanded with **SHAKE-128 in every parameter set**, including the
      two whose other hashes are SHAKE-256.
    - The secret matrix S is stored and multiplied **transposed**, which is
      why [Spec.Frodo.Matrix.mul_t] exists.
    - The re-encryption check compares matrices reduced to [logq] bits,
      because the received ciphertext came through the packing and carries
      no more than that. *)
module Spec.Frodo

open Spec.Frodo.Params

module Seq = FStar.Seq
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module M = Spec.Frodo.Matrix
module B = Hacl.Spec.Bytes
module Math = FStar.Math.Lemmas
module Loops = Hacl.Spec.Loops
module G = FStar.Ghost
module SEM = FStar.IndefiniteDescription

(** {2 A, from its seed}

    Row [i] of A is SHAKE-128 applied to [i] as two little-endian bytes
    followed by the sixteen-byte seed.  SHAKE-128 and not the parameter
    set's hash: Frodo-976 and Frodo-1344 use SHAKE-256 everywhere else and
    SHAKE-128 here, and the known answer tests say so. *)

let index_bytes (i: nat { i < pow2 16 }) : Seq.lseq S8.t 2 =
  let x = S16.classify (U16.uint_to_t i) in
  Seq.init 2 (fun k -> (if k = 0 then S16.lo x else S16.hi x) <: S8.t)

let gen_row (p: params) (seed: Seq.lseq S8.t 16) (i: nat { i < n p })
  : Seq.lseq S8.t (2 * n p)
  = Spec.SHA3.shake128 (Seq.append (index_bytes i) seed) (2 * n p)

let gen_matrix (p: params) (seed: Seq.lseq S8.t 16) : M.matrix (n p) (n p) =
  M.init (n p) (n p) (fun i j ->
    let r = gen_row p seed i in
    S16.of_bytes_le (Seq.index r (2 * j)) (Seq.index r (2 * j + 1)))

(** {2 The error distribution}

    A sample is sixteen bits: the low one is the sign and the other fifteen
    are compared against a cumulative table.  The comparison count is the
    magnitude.  Written as a fold over the table so that the implementation,
    which accumulates the same count with [lt_mask] instead of a branch, has
    the same shape to prove against. *)

let cdf_at (p: params) (i: nat) : GTot nat =
  if i < cdf_len p then U16.v (Seq.index (G.reveal p.cdf) i) else 0

let sample_step (p: params) (t: nat) (i: nat) (acc: nat) : GTot nat =
  if i < cdf_len p - 1 && t > cdf_at p i then acc + 1 else acc

let sample_e (p: params) (t: nat) : GTot nat =
  Loops.repeati_g (cdf_len p - 1) (sample_step p t) 0

let rec sample_e_bound (p: params) (t: nat) (k: nat)
  : Lemma (ensures Loops.repeati_g k (sample_step p t) 0 <= k) (decreases k)
  = if k = 0 then () else sample_e_bound p t (k - 1)

let sample (p: params) (r: S16.t) : GTot S16.t =
  sample_e_bound p (S16.v r / 2) (cdf_len p - 1);
  let e = S16.classify (U16.uint_to_t (sample_e p (S16.v r / 2))) in
  if S16.v r % 2 = 0 then e else S16.sub_mod S16.zero e

(** Two little-endian bytes per sample, in row-major order. *)
let sample_matrix (p: params) (r: nat) (c: pos) (b: Seq.lseq S8.t (2 * (r * c)))
  : GTot (M.matrix r c)
  = let raw = M.from_bytes r c b in
    M.init_g r c (fun i j -> sample p (M.get r c raw i j))

(** {2 Packing}

    A packed matrix is the low [logq] bits of each entry, most significant
    bit first, concatenated into one bit string and cut into bytes.  Since
    [logq * 8] is a whole number of bytes, every group of eight entries
    occupies exactly [logq] bytes and the two views agree; stating it as a
    bit string rather than as groups of eight avoids a 128-bit intermediate
    that this library has no type for. *)

let pack_bit (d: pos) (m: Seq.seq S16.t) (pos: nat) : GTot (n: nat { n < 2 }) =
  if pos < d * Seq.length m then begin
    M.div_lt pos (Seq.length m) d;
    (S16.v (Seq.index m (pos / d)) / pow2 (d - 1 - pos % d)) % 2
  end else 0

let byte_val (d: pos) (m: Seq.seq S16.t) (i: nat) : GTot (n: nat { n < 256 }) =
    pack_bit d m (8 * i)     * 128 + pack_bit d m (8 * i + 1) * 64
  + pack_bit d m (8 * i + 2) * 32  + pack_bit d m (8 * i + 3) * 16
  + pack_bit d m (8 * i + 4) * 8   + pack_bit d m (8 * i + 5) * 4
  + pack_bit d m (8 * i + 6) * 2   + pack_bit d m (8 * i + 7)

let pack (d: pos { d <= 16 }) (len: nat { len % 8 == 0 }) (m: Seq.lseq S16.t len)
  : GTot (Seq.lseq S8.t (d * (len / 8)))
  = Seq.init_ghost (d * (len / 8)) (fun i -> S8.classify (U8.uint_to_t (byte_val d m i)))

(** The inverse: bit [pos] of the byte string, then [d] of them at a time. *)

let stream_bit (b: Seq.seq S8.t) (pos: nat) : GTot (n: nat { n < 2 }) =
  if pos / 8 < Seq.length b
  then (S8.v (Seq.index b (pos / 8)) / pow2 (7 - pos % 8)) % 2
  else 0

let rec unpack_val (b: Seq.seq S8.t) (off: nat) (k: nat)
  : GTot (x: nat { x < pow2 k }) (decreases k)
  = if k = 0 then 0
    else begin
      Math.pow2_double_mult (k - 1);
      2 * unpack_val b off (k - 1) + stream_bit b (off + k - 1)
    end

let unpack (d: pos { d <= 16 }) (len: nat { len % 8 == 0 })
           (b: Seq.lseq S8.t (d * (len / 8)))
  : GTot (Seq.lseq S16.t len)
  = Seq.init_ghost len (fun j ->
      Math.pow2_le_compat 16 d;
      S16.classify (U16.uint_to_t (unpack_val b (j * d) d)))

(** {2 Encoding the message}

    mu is cut into eight chunks of [bits] bytes; chunk [i] is read as a
    little-endian integer and its [bits]-bit fields, least significant
    first, become row [i] of an eight by eight matrix, each shifted up into
    the top of its [logq] bits. *)

let mu_chunk (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) (i: nat { i < nbar }) : GTot nat =
  Math.lemma_mult_le_right (bits p) (i + 1) nbar;
  Math.distributivity_add_left i 1 (bits p);
  B.le_nat (Seq.slice mu (i * bits p) (i * bits p + bits p))

let ec_val (p: params) (x: nat) (k: nat) : nat =
  ((x / pow2 (bits p * k)) % pow2 (bits p)) * pow2 (logq p - bits p)

let ec_bound (p: params) (x: nat) (k: nat) : Lemma (ec_val p x k < pow2 16) =
  Math.lemma_mult_le_right (pow2 (logq p - bits p))
    ((x / pow2 (bits p * k)) % pow2 (bits p)) (pow2 (bits p) - 1);
  Math.distributivity_sub_left (pow2 (bits p)) 1 (pow2 (logq p - bits p));
  Math.pow2_plus (bits p) (logq p - bits p);
  Math.pow2_le_compat 16 (logq p)

let key_encode (p: params) (mu: Seq.lseq S8.t (bytes_mu p)) : GTot (M.matrix nbar nbar) =
  M.init_g nbar nbar (fun i k ->
    ec_bound p (mu_chunk p mu i) k;
    S16.classify (U16.uint_to_t (ec_val p (mu_chunk p mu i) k)))

(** The inverse, which is a rounding: add half a step and truncate. *)

let dc (p: params) (c: S16.t) : GTot nat =
  (((S16.v c + pow2 (logq p - bits p - 1)) % pow2 16) / pow2 (logq p - bits p))
    % pow2 (bits p)

(** Row [i] of the matrix, read back as the integer whose [bits]-wide
    fields are the rounded entries, least significant first.  Written as a
    fold rather than as eight terms because the implementation accumulates
    it one entry at a time and needs a name for the partial sum. *)
let rec row_head (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar })
                 (k: nat { k <= nbar })
  : GTot nat (decreases k)
  = if k = 0 then 0
    else row_head p m i (k - 1)
         + dc p (M.get nbar nbar m i (k - 1)) * pow2 (bits p * (k - 1))

let rec row_head_bound (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar })
                       (k: nat { k <= nbar })
  : Lemma (ensures row_head p m i k < pow2 (bits p * k)) (decreases k)
  = if k = 0 then ()
    else begin
      row_head_bound p m i (k - 1);
      Math.lemma_mult_le_right (pow2 (bits p * (k - 1)))
        (dc p (M.get nbar nbar m i (k - 1))) (pow2 (bits p) - 1);
      Math.distributivity_sub_left (pow2 (bits p)) 1 (pow2 (bits p * (k - 1)));
      Math.pow2_plus (bits p) (bits p * (k - 1))
    end

let row_val (p: params) (m: M.matrix nbar nbar) (i: nat { i < nbar }) : GTot nat =
  row_head p m i nbar

let key_decode (p: params) (m: M.matrix nbar nbar) : GTot (Seq.lseq S8.t (bytes_mu p)) =
  Seq.init_ghost (bytes_mu p) (fun t ->
    M.div_lt t nbar (bits p);
    S8.classify (U8.uint_to_t ((row_val p m (t / bits p) / pow2 (8 * (t % bits p))) % 256)))

(** {2 The key encapsulation mechanism}

    Two coercions first: a flat sequence of the right length {i is} a
    matrix, and the packing above is stated over flat sequences so that a
    matrix and its transpose can share it. *)

let as_matrix (r c: nat) (m: Seq.seq S16.t { Seq.length m == r * c }) : M.matrix r c = m

let pack_n (p: params) (m: Seq.seq S16.t { Seq.length m == n p * nbar })
  : GTot (Seq.lseq S8.t (publicmatrixbytes p))
  = Math.multiple_division_lemma (n p) nbar;
    Math.multiple_modulo_lemma (n p) nbar;
    pack (logq p) (n p * nbar) m

let unpack_n (p: params) (b: Seq.lseq S8.t (publicmatrixbytes p))
  : GTot (Seq.lseq S16.t (n p * nbar))
  = Math.multiple_division_lemma (n p) nbar;
    Math.multiple_modulo_lemma (n p) nbar;
    unpack (logq p) (n p * nbar) b

let pack_8 (p: params) (m: M.matrix nbar nbar) : GTot (Seq.lseq S8.t (ct2bytes p)) =
  pack (logq p) (nbar * nbar) m

let unpack_8 (p: params) (b: Seq.lseq S8.t (ct2bytes p)) : GTot (M.matrix nbar nbar) =
  unpack (logq p) (nbar * nbar) b

(** Key generation.  The coins are s || seed_se || z; s is the value
    returned on an implicit rejection, seed_se seeds the secret and the
    error, and z seeds A.  S is sampled, and stored, transposed. *)

let keypair (p: params) (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
  : GTot (Seq.lseq S8.t (crypto_publickeybytes p) & Seq.lseq S8.t (crypto_secretkeybytes p))
  = let cb = crypto_bytes p in
    let smb = secretmatrixbytes p in
    let s = Seq.slice coins 0 cb in
    let seed_se = Seq.slice coins cb (2 * cb) in
    let z = Seq.slice coins (2 * cb) (2 * cb + bytes_seed_a) in
    let seed_a = shake p z bytes_seed_a in
    let a = gen_matrix p seed_a in
    let r = shake p (Seq.cons (S8.classify 0x5fuy) seed_se) (2 * smb) in
    let st = sample_matrix p nbar (n p) (Seq.slice r 0 smb) in
    let e = sample_matrix p (n p) nbar (Seq.slice r smb (2 * smb)) in
    let b = M.add (n p) nbar (M.mul_t (n p) (n p) nbar a st) e in
    let pk = Seq.append seed_a (pack_n p b) in
    let sk = Seq.append s
               (Seq.append pk
                  (Seq.append (M.to_bytes nbar (n p) st) (shake p pk cb))) in
    (pk, sk)

(** The public half of encapsulation, shared with the re-encryption check in
    decapsulation, which is why it also returns the two matrices reduced to
    [logq] bits: those, and not the unreduced ones, are what the received
    ciphertext determines. *)

let enc_ct (p: params) (mu: Seq.lseq S8.t (bytes_mu p))
           (pk: Seq.lseq S8.t (crypto_publickeybytes p))
           (seed_se: Seq.lseq S8.t (crypto_bytes p))
  : GTot (Seq.lseq S8.t (crypto_ciphertextbytes p) & M.matrix nbar (n p) & M.matrix nbar nbar)
  = let smb = secretmatrixbytes p in
    let seed_a = Seq.slice pk 0 bytes_seed_a in
    let b_bytes = Seq.slice pk bytes_seed_a (crypto_publickeybytes p) in
    let r = shake p (Seq.cons (S8.classify 0x96uy) seed_se) (2 * smb + 2 * (nbar * nbar)) in
    let sp = sample_matrix p nbar (n p) (Seq.slice r 0 smb) in
    let ep = sample_matrix p nbar (n p) (Seq.slice r smb (2 * smb)) in
    let epp = sample_matrix p nbar nbar (Seq.slice r (2 * smb) (2 * smb + 2 * (nbar * nbar))) in
    let a = gen_matrix p seed_a in
    let bp = M.add nbar (n p) (M.mul nbar (n p) (n p) sp a) ep in
    let bm = as_matrix (n p) nbar (unpack_n p b_bytes) in
    let v = M.add nbar nbar
              (M.add nbar nbar (M.mul nbar (n p) nbar sp bm) epp)
              (key_encode p mu) in
    let ct = Seq.append (pack_n p bp) (pack_8 p v) in
    (ct, M.mod_pow2 nbar (n p) p.logq bp, M.mod_pow2 nbar nbar p.logq v)

let enc (p: params) (mu: Seq.lseq S8.t (bytes_mu p))
        (pk: Seq.lseq S8.t (crypto_publickeybytes p))
  : GTot (Seq.lseq S8.t (crypto_ciphertextbytes p) & Seq.lseq S8.t (crypto_bytes p))
  = let cb = crypto_bytes p in
    let pkh = shake p pk cb in
    let sek = shake p (Seq.append pkh mu) (2 * cb) in
    let ct, _, _ = enc_ct p mu pk (Seq.slice sek 0 cb) in
    (ct, shake p (Seq.append ct (Seq.slice sek cb (2 * cb))) cb)

(** Decapsulation.  Recover mu, re-encrypt with the randomness mu itself
    determines, and return the real shared secret if the result matches the
    ciphertext and a pseudorandom one derived from s if it does not. *)

let dec (p: params) (ct: Seq.lseq S8.t (crypto_ciphertextbytes p))
        (sk: Seq.lseq S8.t (crypto_secretkeybytes p))
  : GTot (Seq.lseq S8.t (crypto_bytes p))
  = let cb = crypto_bytes p in
    let pkb = crypto_publickeybytes p in
    let smb = secretmatrixbytes p in
    let s = Seq.slice sk 0 cb in
    let pk = Seq.slice sk cb (cb + pkb) in
    let sbytes = Seq.slice sk (cb + pkb) (cb + pkb + smb) in
    let pkh = Seq.slice sk (cb + pkb + smb) (crypto_secretkeybytes p) in
    let bp = as_matrix nbar (n p) (unpack_n p (Seq.slice ct 0 (ct1bytes p))) in
    let c = unpack_8 p (Seq.slice ct (ct1bytes p) (crypto_ciphertextbytes p)) in
    let st = M.from_bytes nbar (n p) sbytes in
    let m = M.sub nbar nbar c (M.mul_t nbar (n p) nbar bp st) in
    let mu = key_decode p m in
    let sek = shake p (Seq.append pkh mu) (2 * cb) in
    let _, bpp, cp = enc_ct p mu pk (Seq.slice sek 0 cb) in
    let ok = SEM.strong_excluded_middle
               (Seq.equal (M.mod_pow2 nbar (n p) p.logq bp) bpp /\
                Seq.equal (M.mod_pow2 nbar nbar p.logq c) cp) in
    shake p (Seq.append ct (if ok then Seq.slice sek cb (2 * cb) else s)) cb
