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

(** NIST P-256 (secp256r1): ECDSA, ECDH, key validation and the SEC1 point
    encodings.

    Three things distinguish this curve from the two Edwards/Montgomery
    curves already in the library, and all three shape the code.

    {ul
    {- {b Everything is big-endian.}  Curve25519 and Ed25519 serialise
       little-endian; P-256, like the rest of the NIST and PKCS world, puts
       the most significant byte first.  [Hacl.Spec.Bytes.be_nat] and
       [nat_to_be] are the conversions.}
    {- {b The two moduli are equally important.}  The field prime and the
       group order are both 256-bit, both need inversion, and neither has a
       shape the other can borrow.  That is why arithmetic is stated over
       [Spec.ModArith] with the modulus as a parameter rather than open-coded
       twice.}
    {- {b The addition law is complete.}  Short Weierstrass curves normally
       need case analysis on [P = Q] and [P = -Q].  The Renes--Costello--Batina
       formulas for [a = -3] do not: they are correct for every pair of
       projective points including the point at infinity.  So scalar
       multiplication is one straight-line loop with no exceptional cases to
       prove absent, exactly as in Ed25519, and the curve needs no extended
       coordinate to get there -- only more multiplications.}}

    The curve is [y^2 = x^3 - 3x + b] over [F_p], with [p] and [b] below.
    Points are projective [(X : Y : Z)] denoting the affine [(X/Z, Y/Z)],
    with [Z = 0] the point at infinity.

    As in the rest of the library, nothing here is constant time and nothing
    here is fast; the specification exists to be matched, not run. *)
module Spec.P256

open Hacl.Spec.Bytes
open Spec.ModArith
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Loops = Hacl.Spec.Loops
module MA = Spec.ModArith

(** {2 The two moduli} *)

(** [p = 2^256 - 2^224 + 2^192 + 2^96 - 1], the Solinas prime.  Its shape is
    what makes a reduction cheap on 32-bit limbs; this library's limbs are
    sixteen bits and its reduction is Montgomery, so the shape buys nothing
    here and is recorded only for the record. *)
let prime : p: pos { 1 < p /\ p % 4 == 3 } =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1 > 1);
  assert_norm ((pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1) % 4 == 3);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 - 1

(** The order of the group, which is prime, so the cofactor is one: unlike
    Curve25519 there are no small-order points to screen out, and unlike
    Ed25519 there is no torsion to worry about.  Public-key validation is
    exactly "is on the curve". *)
let order : q: pos { 1 < q } =
  assert_norm (0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551 > 1);
  0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

(** {2 The field and the scalar field}

    Two instances of [Spec.ModArith].  [felem] is a coordinate, [qelem] is a
    scalar; they are different types and F* will not let one be used for the
    other by accident. *)

let felem = elem prime
let qelem = elem order

let fadd (x y: felem) : felem = add x y
let fsub (x y: felem) : felem = sub x y
let fmul (x y: felem) : felem = mul x y
let fneg (x: felem) : felem = neg x
let finv (x: felem) : felem = inv x
let fsqrt (x: felem) : option felem = sqrt x

let qadd (x y: qelem) : qelem = add x y
let qmul (x y: qelem) : qelem = mul x y
let qinv (x: qelem) : qelem = inv x

let fzero : felem = MA.zero
let fone : felem = MA.one
let qzero : qelem = MA.zero

(** {2 Curve parameters}

    [a = -3] is not named: it is folded into the formulas below, which is
    the only reason they are as short as they are. *)

let b_coeff : felem =
  assert_norm (0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b < prime);
  0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

let g_x : felem =
  assert_norm (0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296 < prime);
  0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296

let g_y : felem =
  assert_norm (0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5 < prime);
  0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

(** {2 Points} *)

type proj_point = felem & felem & felem

let point_at_infinity : proj_point = (fzero, fone, fzero)

let g : proj_point = (g_x, g_y, fone)

let is_point_at_infinity (p: proj_point) : bool =
  let (_, _, z) = p in z = fzero

(** The affine point a projective one denotes.  At infinity [finv 0] is
    zero, so this quietly returns [(0, 0)]; every caller checks
    [is_point_at_infinity] first, and the ones that do not are the ones for
    which [(0, 0)] is a rejecting answer anyway. *)
let to_aff_point (p: proj_point) : felem & felem =
  let (x, y, z) = p in
  let zi = finv z in
  (fmul x zi, fmul y zi)

let is_on_curve (x y: felem) : bool =
  let x3 = fmul (fmul x x) x in
  let three : felem = assert_norm (3 < prime); 3 in
  fmul y y = fadd (fsub x3 (fmul three x)) b_coeff

(** {3 The complete addition law}

    Renes--Costello--Batina 2016, Algorithm 4, specialised to [a = -3].
    Twelve multiplications, two multiplications by [b] and a pile of
    additions, and -- the point of it -- no case distinction whatever.  The
    intermediate names are the paper's, kept verbatim so that the listing
    can be checked line by line against it, which is worth more than
    readable names for a formula nobody reads for meaning. *)
[@@ "opaque_to_smt"]
let point_add (p q: proj_point) : proj_point =
  let (x1, y1, z1) = p in
  let (x2, y2, z2) = q in
  let t0 = fmul x1 x2 in
  let t1 = fmul y1 y2 in
  let t2 = fmul z1 z2 in
  let t3 = fadd x1 y1 in
  let t4 = fadd x2 y2 in
  let t3 = fmul t3 t4 in
  let t4 = fadd t0 t1 in
  let t3 = fsub t3 t4 in
  let t4 = fadd y1 z1 in
  let t5 = fadd y2 z2 in
  let t4 = fmul t4 t5 in
  let t5 = fadd t1 t2 in
  let t4 = fsub t4 t5 in
  let x3 = fadd x1 z1 in
  let y3 = fadd x2 z2 in
  let x3 = fmul x3 y3 in
  let y3 = fadd t0 t2 in
  let y3 = fsub x3 y3 in
  let z3 = fmul b_coeff t2 in
  let x3 = fsub y3 z3 in
  let z3 = fadd x3 x3 in
  let x3 = fadd x3 z3 in
  let z3 = fsub t1 x3 in
  let x3 = fadd t1 x3 in
  let y3 = fmul b_coeff y3 in
  let t1 = fadd t2 t2 in
  let t2 = fadd t1 t2 in
  let y3 = fsub y3 t2 in
  let y3 = fsub y3 t0 in
  let t1 = fadd y3 y3 in
  let y3 = fadd t1 y3 in
  let t1 = fadd t0 t0 in
  let t0 = fadd t1 t0 in
  let t0 = fsub t0 t2 in
  let t1 = fmul t4 y3 in
  let t2 = fmul t0 y3 in
  let y3 = fmul x3 z3 in
  let y3 = fadd y3 t2 in
  let x3 = fmul t3 x3 in
  let x3 = fsub x3 t1 in
  let z3 = fmul t4 z3 in
  let t1 = fmul t3 t0 in
  let z3 = fadd z3 t1 in
  (x3, y3, z3)

(** Algorithm 6 of the same paper: doubling, again for [a = -3].  Eight
    multiplications instead of fourteen, which is worth having because a
    double-and-add loop is 256 doublings and 256 additions. *)
[@@ "opaque_to_smt"]
let point_double (p: proj_point) : proj_point =
  let (x, y, z) = p in
  let t0 = fmul x x in
  let t1 = fmul y y in
  let t2 = fmul z z in
  let t3 = fmul x y in
  let t3 = fadd t3 t3 in
  let z3 = fmul x z in
  let z3 = fadd z3 z3 in
  let y3 = fmul b_coeff t2 in
  let y3 = fsub y3 z3 in
  let x3 = fadd y3 y3 in
  let y3 = fadd x3 y3 in
  let x3 = fsub t1 y3 in
  let y3 = fadd t1 y3 in
  let y3 = fmul x3 y3 in
  let x3 = fmul x3 t3 in
  let t3 = fadd t2 t2 in
  let t2 = fadd t2 t3 in
  let z3 = fmul b_coeff z3 in
  let z3 = fsub z3 t2 in
  let z3 = fsub z3 t0 in
  let t3 = fadd z3 z3 in
  let z3 = fadd z3 t3 in
  let t3 = fadd t0 t0 in
  let t0 = fadd t3 t0 in
  let t0 = fsub t0 t2 in
  let t0 = fmul t0 z3 in
  let y3 = fadd y3 t0 in
  let t0 = fmul y z in
  let t0 = fadd t0 t0 in
  let z3 = fmul t0 z3 in
  let x3 = fsub x3 z3 in
  let z3 = fmul t0 t1 in
  let z3 = fadd z3 z3 in
  let z3 = fadd z3 z3 in
  (x3, y3, z3)

let point_negate (p: proj_point) : proj_point =
  let (x, y, z) = p in (x, fneg y, z)

(** {3 Scalar multiplication}

    Double-and-add over the 256 bits of the scalar, most significant first.
    The scalar is a plain [nat] rather than a byte string: the implementation
    keeps it in limbs, and reading bit [i] of a number is a statement that
    survives any choice of radix, whereas reading bit [i] of a byte string is
    not. *)

let bit (k: nat) (i: nat) : n: nat { n < 2 } = (k / pow2 i) % 2

let point_select (b: nat { b < 2 }) (p q: proj_point) : proj_point =
  if b = 1 then q else p

let point_mul_step (k: nat) (p: proj_point) (i: nat { i < 256 })
                   (acc: proj_point) : proj_point =
  let acc = point_double acc in
  point_select (bit k (255 - i)) acc (point_add acc p)

let point_mul_at (k: nat) (p: proj_point) (i: nat) (acc: proj_point) : proj_point =
  if i < 256 then point_mul_step k p i acc else acc

let point_mul (k: nat) (p: proj_point) : GTot proj_point =
  Loops.repeati_g 256 (point_mul_at k p) point_at_infinity

let point_mul_g (k: nat) : GTot proj_point = point_mul k g

(** [u1 G + u2 Q], the combination verification needs.  Computing it as two
    independent multiplications wastes the shared doubling chain, but
    verification handles no secrets and there is no reason to complicate
    it. *)
let point_mul_double_g (u1 u2: nat) (q: proj_point) : GTot proj_point =
  point_add (point_mul u1 g) (point_mul u2 q)

(** {2 Byte encodings}

    A coordinate is thirty-two big-endian bytes; a raw public key is [x || y]
    and is sixty-four. *)

let load_felem (s: Seq.lseq S8.t 32) : GTot (option felem) =
  let x = be_nat s in
  if x < prime then Some x else None

let store_felem (x: felem) : Seq.lseq S8.t 32 = nat_to_be 32 x

(** A raw point is accepted exactly when it satisfies the curve equation.
    That already excludes [(0, 0)] -- the affine stand-in for infinity --
    because [b] is not zero, so no separate infinity check is needed. *)
let load_point (s: Seq.lseq S8.t 64) : GTot (option proj_point) =
  let xs = Seq.slice s 0 32 in
  let ys = Seq.slice s 32 64 in
  match load_felem xs, load_felem ys with
  | Some x, Some y -> if is_on_curve x y then Some (x, y, fone) else None
  | _ -> None

let store_point (p: proj_point) : Seq.lseq S8.t 64 =
  let (x, y) = to_aff_point p in
  Seq.append (store_felem x) (store_felem y)

(** {3 SEC1 compressed and uncompressed forms}

    These are pure byte shuffling apart from [compressed_to_raw], which has
    to take a square root.  Note what HACL* does and does not check, because
    the API has to match: [uncompressed_to_raw] validates only the [0x04]
    header and not the point, and [raw_to_*] validate nothing at all. *)

let raw_to_uncompressed (pk: Seq.lseq S8.t 64) : Seq.lseq S8.t 65 =
  Seq.append (Seq.create 1 (S8.classify 4uy)) pk

let raw_to_compressed (pk: Seq.lseq S8.t 64) : GTot (Seq.lseq S8.t 33) =
  let y = be_nat (Seq.slice pk 32 64) in
  let h = if y % 2 = 0 then S8.classify 2uy else S8.classify 3uy in
  Seq.append (Seq.create 1 h) (Seq.slice pk 0 32)

let uncompressed_to_raw (pk: Seq.lseq S8.t 65) : GTot (option (Seq.lseq S8.t 64)) =
  if S8.v (Seq.index pk 0) = 4 then Some (Seq.slice pk 1 65) else None

(** Recover [y] from [x] and the parity bit.  [p = 3 mod 4] means one
    exponentiation gives the root when there is one, so unlike Ed25519 there
    is no second candidate to try. *)
let compressed_to_raw (pk: Seq.lseq S8.t 33) : GTot (option (Seq.lseq S8.t 64)) =
  let h = S8.v (Seq.index pk 0) in
  let xs = Seq.slice pk 1 33 in
  if h <> 2 && h <> 3 then None
  else
    match load_felem xs with
    | None -> None
    | Some x ->
      let three : felem = assert_norm (3 < prime); 3 in
      let rhs = fadd (fsub (fmul (fmul x x) x) (fmul three x)) b_coeff in
      match fsqrt rhs with
      | None -> None
      | Some y ->
        let y = if y % 2 = h - 2 then y else fneg y in
        Some (Seq.append xs (store_felem y))

(** {2 Key validation} *)

let validate_private_key (s: Seq.lseq S8.t 32) : GTot bool =
  let k = be_nat s in 0 < k && k < order

let validate_public_key (s: Seq.lseq S8.t 64) : GTot bool =
  Some? (load_point s)

(** {2 ECDH}

    The shared secret is the whole point, [x || y], not just the
    x-coordinate.  That is HACL*'s API and changing it would silently break
    every caller, so it stands. *)

let dh_initiator (private_key: Seq.lseq S8.t 32) : GTot (option (Seq.lseq S8.t 64)) =
  let sk = be_nat private_key in
  if 0 < sk && sk < order then Some (store_point (point_mul_g sk)) else None

let dh_responder (their_pk: Seq.lseq S8.t 64) (private_key: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = let sk = be_nat private_key in
    match load_point their_pk with
    | None -> None
    | Some q ->
      if 0 < sk && sk < order then
        let r = point_mul sk q in
        if is_point_at_infinity r then None else Some (store_point r)
      else None

(** {2 ECDSA}

    The nonce is an input.  HACL* does not implement RFC 6979 deterministic
    nonces and neither does this; a caller who reuses a nonce loses the
    private key, and no amount of verification prevents that. *)

(** The message representative: the leading 32 bytes of the hash (or of the
    message itself, in the [without_hash] variants), read big-endian and
    reduced.  Note that this is a reduction and not the bit-length
    truncation FIPS 186 describes; for P-256 with a 256-bit hash the two
    coincide, and HACL* does it this way for the longer hashes too. *)
let msg_as_qelem (msg: Seq.seq S8.t { 32 <= Seq.length msg }) : GTot qelem =
  be_nat (Seq.slice msg 0 32) % order

let ecdsa_sign_msg_as_qelem (m: qelem) (private_key nonce: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = let sk = be_nat private_key in
    let k = be_nat nonce in
    if not (0 < sk && sk < order && 0 < k && k < order) then None
    else begin
      let (px, _) = to_aff_point (point_mul_g k) in
      let r : qelem = px % order in
      let s : qelem = qmul (qinv k) (qadd m (qmul r sk)) in
      if r = 0 || s = 0 then None
      else Some (Seq.append (nat_to_be 32 r) (nat_to_be 32 s))
    end

let ecdsa_verify_msg_as_qelem (m: qelem) (public_key: Seq.lseq S8.t 64)
                              (sig_r sig_s: Seq.lseq S8.t 32) : GTot bool
  = let r = be_nat sig_r in
    let s = be_nat sig_s in
    if not (0 < r && r < order && 0 < s && s < order) then false
    else
      match load_point public_key with
      | None -> false
      | Some q ->
        let sinv = qinv s in
        let u1 : qelem = qmul sinv m in
        let u2 : qelem = qmul sinv r in
        let res = point_mul_double_g u1 u2 q in
        if is_point_at_infinity res then false
        else (let (rx, _) = to_aff_point res in rx % order = r)

(** {3 The hashed front ends}

    Four of each: SHA2-256, SHA2-384, SHA2-512, and none.  The
    [without_hash] pair takes the message itself as the representative and
    therefore insists on at least thirty-two bytes -- HACL* declines to
    left-pad shorter inputs the way OpenSSL does, and so does this. *)

let msg_ok (msg: Seq.seq S8.t) : prop = Seq.length msg < pow2 61

(** [pow2 61] is the SHA2-256 length bound; the 512-bit variants allow far
    more, so one bound serves all three. *)
let msg_ok_hashable (msg: Seq.seq S8.t)
  : Lemma (requires msg_ok msg)
          (ensures Seq.length msg < Spec.SHA2.max_input #S32.t /\
                   Seq.length msg < Spec.SHA2.max_input #S64.t)
  = assert (Seq.length msg < pow2 61);
    assert_norm (Spec.SHA2.max_input #S32.t == pow2 61);
    assert_norm (pow2 61 <= pow2 125);
    assert_norm (Spec.SHA2.max_input #S64.t == pow2 125)

let digest_ge_32 (_: unit)
  : Lemma (Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_256 == 32 /\
           Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_384 == 48 /\
           Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_512 == 64)
  = assert_norm (Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_256 == 32);
    assert_norm (Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_384 == 48);
    assert_norm (Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_512 == 64)

let sha256_as_qelem (msg: Seq.seq S8.t { msg_ok msg }) : GTot qelem =
  msg_ok_hashable msg; digest_ge_32 ();
  msg_as_qelem (Spec.SHA2.hash Spec.SHA2.Constants.sha2_256 msg)

let sha384_as_qelem (msg: Seq.seq S8.t { msg_ok msg }) : GTot qelem =
  msg_ok_hashable msg; digest_ge_32 ();
  msg_as_qelem (Spec.SHA2.hash Spec.SHA2.Constants.sha2_384 msg)

let sha512_as_qelem (msg: Seq.seq S8.t { msg_ok msg }) : GTot qelem =
  msg_ok_hashable msg; digest_ge_32 ();
  msg_as_qelem (Spec.SHA2.hash Spec.SHA2.Constants.sha2_512 msg)

let sign_sha256 (msg: Seq.seq S8.t { msg_ok msg }) (private_key nonce: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = ecdsa_sign_msg_as_qelem (sha256_as_qelem msg) private_key nonce

let sign_sha384 (msg: Seq.seq S8.t { msg_ok msg }) (private_key nonce: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = ecdsa_sign_msg_as_qelem (sha384_as_qelem msg) private_key nonce

let sign_sha512 (msg: Seq.seq S8.t { msg_ok msg }) (private_key nonce: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = ecdsa_sign_msg_as_qelem (sha512_as_qelem msg) private_key nonce

let sign_without_hash (msg: Seq.seq S8.t { 32 <= Seq.length msg })
                      (private_key nonce: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = ecdsa_sign_msg_as_qelem (msg_as_qelem msg) private_key nonce

let verify_sha256 (msg: Seq.seq S8.t { msg_ok msg }) (public_key: Seq.lseq S8.t 64)
                  (sig_r sig_s: Seq.lseq S8.t 32) : GTot bool
  = ecdsa_verify_msg_as_qelem (sha256_as_qelem msg) public_key sig_r sig_s

let verify_sha384 (msg: Seq.seq S8.t { msg_ok msg }) (public_key: Seq.lseq S8.t 64)
                  (sig_r sig_s: Seq.lseq S8.t 32) : GTot bool
  = ecdsa_verify_msg_as_qelem (sha384_as_qelem msg) public_key sig_r sig_s

let verify_sha512 (msg: Seq.seq S8.t { msg_ok msg }) (public_key: Seq.lseq S8.t 64)
                  (sig_r sig_s: Seq.lseq S8.t 32) : GTot bool
  = ecdsa_verify_msg_as_qelem (sha512_as_qelem msg) public_key sig_r sig_s

let verify_without_hash (msg: Seq.seq S8.t { 32 <= Seq.length msg })
                        (public_key: Seq.lseq S8.t 64)
                        (sig_r sig_s: Seq.lseq S8.t 32) : GTot bool
  = ecdsa_verify_msg_as_qelem (msg_as_qelem msg) public_key sig_r sig_s
