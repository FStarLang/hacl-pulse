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

(** Ed25519, as RFC 8032 defines it.

    The field is the one [Spec.Curve25519] already sets up -- the integers
    modulo [2^255 - 19] -- and every field operation here is imported from
    there rather than restated, which is also what the implementation does:
    [Hacl.Curve25519.Field] serves both curves.

    The curve is the twisted Edwards curve [-x^2 + y^2 = 1 + d x^2 y^2],
    birationally equivalent to Curve25519 but with a complete addition law,
    which is why signatures use it and key exchange does not.  A point is
    kept in *extended* coordinates [(X, Y, Z, T)] standing for the affine
    [(X/Z, Y/Z)] with [T = XY/Z]: the redundant fourth coordinate is what
    makes the addition formulas free of inversions and free of special
    cases, so a scalar multiplication is one straight-line loop.

    There are two moduli in Ed25519 and it is worth keeping them apart.  The
    field modulus [prime] is used for coordinates; the group order [q] is
    used for scalars, and is where the [S] half of a signature lives.  A
    hash output is 512 bits and is reduced mod [q] before it is used as a
    scalar.

    Nothing here is constant time or fast; [point_mul] is bit-by-bit
    double-and-add and the selection is written as a function of the bit
    rather than as an [if] on points, so the implementation may compile it
    to a mask. *)
module Spec.Ed25519

open Hacl.Spec.Bytes
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances
open Spec.Curve25519

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S64 = Hacl.Secret.UInt64
module U8 = FStar.UInt8
module Loops = Hacl.Spec.Loops
module C = Spec.Curve25519

(** {2 Constants} *)

(** The order of the prime-order subgroup: [2^252 + 27742...93].  A scalar
    is a residue mod [q], and the cofactor is eight, so the group the curve
    provides is [8q] points and only the [q]-torsion part matters. *)
let q : pos = pow2 252 + 27742317777372353535851937790883648493

let q_lt_prime (_: unit) : Lemma (q < prime /\ q > 1) =
  assert_norm (pow2 252 + 27742317777372353535851937790883648493 < pow2 255 - 19);
  assert_norm (pow2 252 + 27742317777372353535851937790883648493 > 1)

(** The curve parameter [d = -121665/121666]. *)
let d : elem =
  assert_norm (37095705934669439343138083508754565189542113879843219016388785533085940283555 < prime);
  37095705934669439343138083508754565189542113879843219016388785533085940283555

(** [2d], which is what the addition formula actually multiplies by. *)
let d2 : elem = fadd d d

(** A square root of [-1], needed to decompress: the exponentiation
    [x^((p+3)/8)] gives a fourth root of [x^2], and multiplying by this
    fixes it up when it gives the wrong one. *)
let sqrt_m1 : elem =
  assert_norm (19681161376707505956807079304988542015446066515923890162744021073123829784752 < prime);
  19681161376707505956807079304988542015446066515923890162744021073123829784752

(** {2 Points}

    Extended coordinates: [(X, Y, Z, T)] is the affine point [(X/Z, Y/Z)],
    and the invariant that makes the formulas correct is [XY = ZT]. *)

type ext_point = elem & elem & elem & elem

let point_inv (p: ext_point) : prop =
  let (x, y, z, t) = p in fmul x y == fmul z t

let point_at_infinity : ext_point = (0, one, one, 0)

(** The base point, RFC 8032 section 5.1. *)
let g_x : elem =
  assert_norm (15112221349535400772501151409588531511454012693041857206046113283949847762202 < prime);
  15112221349535400772501151409588531511454012693041857206046113283949847762202

let g_y : elem =
  assert_norm (46316835694926478169428394003475163141307993866256225615783033603165251855960 < prime);
  46316835694926478169428394003475163141307993866256225615783033603165251855960

let g : ext_point = (g_x, g_y, one, fmul g_x g_y)

(** {3 The group law}

    The "add-2008-hwcd-3" formulas, which is what RFC 8032's reference code
    and every fast implementation use.  They are *complete* on the curve
    with [a = -1] and non-square [d]: no branch on equal or opposite
    inputs, which is the whole reason for the extended coordinate. *)
let point_add (p q: ext_point) : ext_point =
  let (x1, y1, z1, t1) = p in
  let (x2, y2, z2, t2) = q in
  let a = fmul (fsub y1 x1) (fsub y2 x2) in
  let b = fmul (fadd y1 x1) (fadd y2 x2) in
  let c = fmul (fmul d2 t1) t2 in
  let dd = fmul (fadd z1 z1) z2 in
  let e = fsub b a in
  let f = fsub dd c in
  let gg = fadd dd c in
  let h = fadd b a in
  (fmul e f, fmul gg h, fmul f gg, fmul e h)

(** "dbl-2008-hwcd", which saves the four multiplications the general
    formula spends on [t1 * t2] and on rebuilding the sums. *)
let point_double (p: ext_point) : ext_point =
  let (x1, y1, z1, _) = p in
  let a = fmul x1 x1 in
  let b = fmul y1 y1 in
  let c = fmul (fadd z1 z1) z1 in
  let h = fadd a b in
  let xy = fadd x1 y1 in
  let e = fsub h (fmul xy xy) in
  let gg = fsub a b in
  let f = fadd c gg in
  (fmul e f, fmul gg h, fmul f gg, fmul e h)

(** Negation is negation of [x], hence of [t]. *)
let point_negate (p: ext_point) : ext_point =
  let (x, y, z, t) = p in
  (fsub 0 x, y, z, fsub 0 t)

(** Projective equality: [(x1, z1)] and [(x2, z2)] denote the same affine
    coordinate iff [x1 z2 = x2 z1].  Doing it this way rather than by
    normalising costs two multiplications instead of an inversion, and is
    what verification needs. *)
let point_equal (p q: ext_point) : bool =
  let (x1, y1, z1, _) = p in
  let (x2, y2, z2, _) = q in
  fmul x1 z2 = fmul x2 z1 && fmul y1 z2 = fmul y2 z1

(** {3 Scalar multiplication}

    Double-and-add, most significant bit first, over all 256 bits.  The
    conditional addition is a [select] on the bit rather than an [if] on
    points, which is what an implementation compiles to a mask, and it is
    also why the loop body is one shape rather than two. *)
let point_select (b: nat { b < 2 }) (p q: ext_point) : ext_point =
  if b = 1 then q else p

let point_mul_step (k: Seq.lseq S8.t 32) (p: ext_point) (i: nat { i < 256 })
                   (acc: ext_point) : GTot ext_point =
  let acc = point_double acc in
  point_select (ith_bit k (255 - i)) acc (point_add acc p)

let point_mul_at (k: Seq.lseq S8.t 32) (p: ext_point) (i: nat) (acc: ext_point)
  : GTot ext_point
  = if i < 256 then point_mul_step k p i acc else acc

let point_mul (k: Seq.lseq S8.t 32) (p: ext_point) : GTot ext_point =
  Loops.repeati_g 256 (point_mul_at k p) point_at_infinity

let point_mul_g (k: Seq.lseq S8.t 32) : GTot ext_point = point_mul k g

(** {2 Encoding}

    A point is thirty-two bytes: the little-endian [y] coordinate, with the
    low bit of [x] in the top bit -- which is free, because [y < 2^255 - 19]
    leaves that bit clear. *)

let point_compress (p: ext_point) : Seq.lseq S8.t 32 =
  let (x, y, z, _) = p in
  let zinv = finv z in
  let x = fmul x zinv in
  let y = fmul y zinv in
  assert_norm (pow2 255 + pow2 255 == pow2 256);
  nat_to_le 32 (y + (x % 2) * pow2 255)

(** {3 Decompression}

    Recovering [x] from [y] means taking a square root of
    [(y^2 - 1)/(d y^2 + 1)].  Since [p = 5 mod 8], [x^((p+3)/8)] is a
    *fourth* root of [x^2]: it is the square root when one exists, or [i]
    times it when it does not, so both candidates have to be tried. *)

let modp_sqrt (a: elem) : elem =
  assert_norm ((prime + 3) / 8 >= 0);
  fexp a ((prime + 3) / 8)

(** [None] when [a] is not a square. *)
let sqrt_of (a: elem) : option elem =
  let x = modp_sqrt a in
  if fmul x x = a then Some x
  else
    let x = fmul x sqrt_m1 in
    if fmul x x = a then Some x else None

let recover_x (y: elem) (sign: nat { sign < 2 }) : option elem =
  let y2 = fmul y y in
  let u = fsub y2 one in
  let v = fadd (fmul d y2) one in
  if v = 0 then None
  else
    match sqrt_of (fmul u (finv v)) with
    | None -> None
    | Some x ->
      if x = 0 && sign = 1 then None
      else if x % 2 = sign then Some x else Some (fsub 0 x)

let point_decompress (s: Seq.lseq S8.t 32) : GTot (option ext_point) =
  let n = le_nat s in
  let sign = n / pow2 255 in
  let y = n % pow2 255 in
  assert_norm (pow2 255 == 2 * pow2 254);
  le_nat_bound s;
  assert_norm (pow2 (8 * 32) == 2 * pow2 255);
  Math.lemma_div_lt n 256 255;
  Math.lemma_mod_lt n (pow2 255);
  if y >= prime then None
  else
    match recover_x y sign with
    | None -> None
    | Some x -> Some (x, y, one, fmul x y)

(** {2 The hash}

    Ed25519 is SHA-512 throughout, and every use of it is "hash something,
    read the result as a little-endian integer, reduce mod [q]". *)

let sha512 (msg: Seq.seq S8.t { Seq.length msg < Spec.SHA2.max_input #S64.t })
  : GTot (Seq.lseq S8.t 64)
  = Spec.SHA2.hash Spec.SHA2.Constants.sha2_512 msg

let max_msg : (n: pos { n + 64 < Spec.SHA2.max_input #S64.t }) =
  assert_norm (pow2 32 + 64 < Spec.SHA2.max_input #S64.t);
  pow2 32

let msg_ok (msg: Seq.seq S8.t) : prop = Seq.length msg < max_msg

(** A 64-byte hash read as a scalar. *)
let sha512_mod_q (h: Seq.lseq S8.t 64) : GTot (n: nat { n < q }) =
  le_nat h % q

(** A scalar, as the thirty-two bytes the multiplication loop reads. *)
let scalar_bytes (n: nat { n < q }) : Seq.lseq S8.t 32 =
  q_lt_prime ();
  assert_norm (prime < pow2 (8 * 32));
  nat_to_le 32 n

(** {2 Keys}

    Expanding a seed: hash it, clamp the low half into a scalar, keep the
    high half as the per-message nonce prefix.  RFC 8032's clamp is
    Curve25519's, which is why [C.clamp] is reused here. *)

let expand_low (secret: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32) =
  assert_norm (32 < Spec.SHA2.max_input #S64.t);
  C.clamp (Seq.slice (sha512 secret) 0 32)

let expand_prefix (secret: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32) =
  assert_norm (32 < Spec.SHA2.max_input #S64.t);
  Seq.slice (sha512 secret) 32 64

let secret_to_public (secret: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 32) =
  point_compress (point_mul_g (expand_low secret))

(** The ninety-six byte expanded key: public key, scalar, prefix. *)
let expand_keys (secret: Seq.lseq S8.t 32) : GTot (Seq.lseq S8.t 96) =
  Seq.append (secret_to_public secret)
             (Seq.append (expand_low secret) (expand_prefix secret))

(** {2 Signing}

    The nonce is deterministic: [r = H(prefix || msg) mod q].  Then
    [R = [r]B], [k = H(R || A || msg) mod q] and [S = r + k s mod q]. *)

let sig_r (prefix: Seq.lseq S8.t 32) (msg: Seq.seq S8.t { msg_ok msg })
  : GTot (n: nat { n < q })
  = sha512_mod_q (sha512 (Seq.append prefix msg))

let sig_k (rr aa: Seq.lseq S8.t 32) (msg: Seq.seq S8.t { msg_ok msg })
  : GTot (n: nat { n < q })
  = sha512_mod_q (sha512 (Seq.append rr (Seq.append aa msg)))

let sign_expanded (pub s prefix: Seq.lseq S8.t 32) (msg: Seq.seq S8.t { msg_ok msg })
  : GTot (Seq.lseq S8.t 64)
  = let r = sig_r prefix msg in
    let rr = point_compress (point_mul_g (scalar_bytes r)) in
    let k = sig_k rr pub msg in
    q_lt_prime ();
    let ss = (r + k * (le_nat s % q)) % q in
    Seq.append rr (scalar_bytes ss)

let sign (secret: Seq.lseq S8.t 32) (msg: Seq.seq S8.t { msg_ok msg })
  : GTot (Seq.lseq S8.t 64)
  = sign_expanded (secret_to_public secret) (expand_low secret) (expand_prefix secret) msg

(** {2 Verification}

    [[S]B = R + [k]A].  The three ways to fail are an undecompressable
    public key, an undecompressable [R], and an [S] at or above the group
    order -- the last is what makes signatures non-malleable, and RFC 8032
    requires it. *)

let verify (pub: Seq.lseq S8.t 32) (msg: Seq.seq S8.t { msg_ok msg })
           (sg: Seq.lseq S8.t 64)
  : GTot bool
  = let rr : Seq.lseq S8.t 32 = Seq.slice sg 0 32 in
    let sb : Seq.lseq S8.t 32 = Seq.slice sg 32 64 in
    match point_decompress pub with
    | None -> false
    | Some aa ->
      match point_decompress rr with
      | None -> false
      | Some rp ->
        let s = le_nat sb in
        if s >= q then false
        else begin
          q_lt_prime ();
          let k = sig_k rr pub msg in
          let sb' = point_mul_g (scalar_bytes s) in
          let ka = point_mul (scalar_bytes k) aa in
          point_equal sb' (point_add rp ka)
        end
