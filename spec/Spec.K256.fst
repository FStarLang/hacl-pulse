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

(** secp256k1 (K-256): ECDSA, ECDH, key validation and the SEC1 point
    encodings.

    The curve is [y^2 = x^3 + 7] over [F_p] with
    [p = 2^256 - 2^32 - 977].  It is the same shape of object as
    {!Spec.P256} -- a short Weierstrass curve over a 256-bit prime field,
    with a prime group order and therefore cofactor one -- and this module is
    deliberately laid out the same way so that the two can be read side by
    side.  Three things differ, and only three.

    {ul
    {- {b [a] is zero, not [-3].}  Renes--Costello--Batina 2016 gives a
       second pair of complete formulas for that case, Algorithms 7 and 9,
       and they are cheaper than the [a = -3] pair: the doubling drops from
       fourteen field multiplications to eight.  Completeness is what
       matters more -- there is still no case analysis anywhere, and scalar
       multiplication is still one straight-line loop.}
    {- {b [b] is [7], so [3b] is [21].}  The formulas multiply by [3b] rather
       than by [b]; naming [b3] once is what keeps them short.}
    {- {b Signatures are canonically low-S.}  If [(r, s)] verifies then so
       does [(r, q - s)], which makes a signature malleable as a byte string.
       Bitcoin forbids the high half, so alongside the plain ECDSA pair there
       is a [secp256k1_] pair that normalises on signing and insists on
       normal form when verifying.  See {!section:lows}.}}

    As in the rest of the library, nothing here is constant time and nothing
    here is fast; the specification exists to be matched, not run. *)
module Spec.K256

open Hacl.Spec.Bytes
open Spec.ModArith
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module Math = FStar.Math.Lemmas
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module Loops = Hacl.Spec.Loops
module MA = Spec.ModArith

(** {2 The two moduli} *)

(** [p = 2^256 - 2^32 - 977].  Like P-256's prime this is a Solinas shape
    whose cheap reduction this library does not use -- the arithmetic here is
    Montgomery over sixteen-bit limbs, which does not care.  [p % 4 == 3] is
    what makes point decompression a single exponentiation. *)
let prime : p: pos { 1 < p /\ p % 4 == 3 } =
  assert_norm (pow2 256 - pow2 32 - 977 > 1);
  assert_norm ((pow2 256 - pow2 32 - 977) % 4 == 3);
  pow2 256 - pow2 32 - 977

(** The group order, which is prime; the cofactor is one, so validating a
    public key is exactly "is on the curve". *)
let order : q: pos { 1 < q } =
  assert_norm (0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 > 1);
  0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

(** {2 The field and the scalar field} *)

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
let qneg (x: qelem) : qelem = neg x
let qinv (x: qelem) : qelem = inv x

let fzero : felem = MA.zero
let fone : felem = MA.one
let qzero : qelem = MA.zero

(** {2 Curve parameters}

    [a = 0] is not named, for the same reason P-256 does not name [-3]: it
    has been folded into the formulas.  [b3 = 3b = 21] is named, because the
    formulas use it and nothing else. *)

let b_coeff : felem = assert_norm (7 < prime); 7

let b3 : felem = assert_norm (21 < prime); 21

let g_x : felem =
  assert_norm (0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798 < prime);
  0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798

let g_y : felem =
  assert_norm (0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8 < prime);
  0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

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
  fmul y y = fadd (fmul (fmul x x) x) b_coeff

(** {3 The complete addition law}

    Renes--Costello--Batina 2016, Algorithm 7, for [a = 0].  Twelve
    multiplications, two by [b3], and no case distinction whatever: it is
    correct for every pair of projective points, including when they are
    equal, when one is the other's negation, and when either is the point at
    infinity.  The intermediate names are the paper's, kept verbatim so the
    listing can be checked line by line against it. *)
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
  let x3 = fadd y2 z2 in
  let t4 = fmul t4 x3 in
  let x3 = fadd t1 t2 in
  let t4 = fsub t4 x3 in
  let x3 = fadd x1 z1 in
  let y3 = fadd x2 z2 in
  let x3 = fmul x3 y3 in
  let y3 = fadd t0 t2 in
  let y3 = fsub x3 y3 in
  let x3 = fadd t0 t0 in
  let t0 = fadd x3 t0 in
  let t2 = fmul b3 t2 in
  let z3 = fadd t1 t2 in
  let t1 = fsub t1 t2 in
  let y3 = fmul b3 y3 in
  let x3 = fmul t4 y3 in
  let t2 = fmul t3 t1 in
  let x3 = fsub t2 x3 in
  let y3 = fmul y3 t0 in
  let t1 = fmul t1 z3 in
  let y3 = fadd t1 y3 in
  let t0 = fmul t0 t3 in
  let z3 = fmul z3 t4 in
  let z3 = fadd z3 t0 in
  (x3, y3, z3)

(** Algorithm 9 of the same paper: doubling for [a = 0].  Six
    multiplications, two squarings and one by [b3], against the fourteen
    multiplications P-256's [a = -3] doubling needs -- worth having, because
    a double-and-add loop is 256 doublings. *)
[@@ "opaque_to_smt"]
let point_double (p: proj_point) : proj_point =
  let (x, y, z) = p in
  let t0 = fmul y y in
  let z3 = fadd t0 t0 in
  let z3 = fadd z3 z3 in
  let z3 = fadd z3 z3 in
  let t1 = fmul y z in
  let t2 = fmul z z in
  let t2 = fmul b3 t2 in
  let x3 = fmul t2 z3 in
  let y3 = fadd t0 t2 in
  let z3 = fmul t1 z3 in
  let t1 = fadd t2 t2 in
  let t2 = fadd t1 t2 in
  let t0 = fsub t0 t2 in
  let y3 = fmul t0 y3 in
  let y3 = fadd x3 y3 in
  let t1 = fmul x y in
  let x3 = fmul t0 t1 in
  let x3 = fadd x3 x3 in
  (x3, y3, z3)

let point_negate (p: proj_point) : proj_point =
  let (x, y, z) = p in (x, fneg y, z)

(** {3 Scalar multiplication}

    Double-and-add over the 256 bits of the scalar, most significant first.
    The scalar is a plain [nat] rather than a byte string, for the reason
    {!Spec.P256} gives: reading bit [i] of a number survives any choice of
    radix, reading bit [i] of a byte string does not. *)

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

let point_mul_double_g (u1 u2: nat) (q: proj_point) : GTot proj_point =
  point_add (point_mul u1 g) (point_mul u2 q)

(** {2 Byte encodings}

    A coordinate is thirty-two big-endian bytes; a raw public key is [x || y]
    and is sixty-four. *)

let load_felem (s: Seq.lseq S8.t 32) : GTot (option felem) =
  let x = be_nat s in
  if x < prime then Some x else None

let store_felem (x: felem) : Seq.lseq S8.t 32 = nat_to_be 32 x

(** A raw point is accepted exactly when it satisfies the curve equation,
    which already excludes [(0, 0)] -- the affine stand-in for infinity --
    because [b] is not zero. *)
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

    Byte shuffling apart from [compressed_to_raw], which takes a square root.
    As with P-256 these match HACL* exactly in what they do and do not check:
    [uncompressed_to_raw] validates only the [0x04] header and not the point,
    and the [raw_to_*] pair validate nothing at all. *)

let raw_to_uncompressed (pk: Seq.lseq S8.t 64) : Seq.lseq S8.t 65 =
  Seq.append (Seq.create 1 (S8.classify 4uy)) pk

let raw_to_compressed (pk: Seq.lseq S8.t 64) : GTot (Seq.lseq S8.t 33) =
  let y = be_nat (Seq.slice pk 32 64) in
  let h = if y % 2 = 0 then S8.classify 2uy else S8.classify 3uy in
  Seq.append (Seq.create 1 h) (Seq.slice pk 0 32)

let uncompressed_to_raw (pk: Seq.lseq S8.t 65) : GTot (option (Seq.lseq S8.t 64)) =
  if S8.v (Seq.index pk 0) = 4 then Some (Seq.slice pk 1 65) else None

(** Recover [y] from [x] and the parity bit.  [p = 3 mod 4], so one
    exponentiation gives the root when there is one. *)
let compressed_to_raw (pk: Seq.lseq S8.t 33) : GTot (option (Seq.lseq S8.t 64)) =
  let h = S8.v (Seq.index pk 0) in
  let xs = Seq.slice pk 1 33 in
  if h <> 2 && h <> 3 then None
  else
    match load_felem xs with
    | None -> None
    | Some x ->
      let rhs = fadd (fmul (fmul x x) x) b_coeff in
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

    The shared secret is the whole point, [x || y], as HACL*'s K-256 API
    returns it. *)

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

    The nonce is an input; HACL* does not implement RFC 6979 and neither does
    this. *)

(** The message representative.  K-256's API takes a thirty-two byte hash and
    nothing else, so unlike P-256 there is no truncation question: the whole
    input is read big-endian and reduced. *)
let msg_as_qelem (msg: Seq.lseq S8.t 32) : GTot qelem = be_nat msg % order

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

(** {2:lows Low-S}

    [(r, s)] and [(r, q - s)] verify against the same key and message, so a
    signature is malleable as a byte string even though it is not forgeable.
    Bitcoin's consensus rules forbid the upper half, and HACL* exposes that
    policy as a second family of entry points rather than as a flag.

    The boundary is [q / 2] rounded down, and it belongs to the low half:
    [q] is odd, so [s] and [q - s] are never both equal to it. *)

let q_half : nat = order / 2

let is_normalized (s: Seq.lseq S8.t 32) : GTot bool =
  let sv = be_nat s in 0 < sv && sv <= q_half

let is_signature_normalized (signature: Seq.lseq S8.t 64) : GTot bool =
  is_normalized (Seq.slice signature 32 64)

(** [None] when [s] is not a scalar at all; otherwise the signature with [s]
    replaced by [min s (q - s)]. *)
let signature_normalize (signature: Seq.lseq S8.t 64)
  : GTot (option (Seq.lseq S8.t 64))
  = let sv = be_nat (Seq.slice signature 32 64) in
    if not (0 < sv && sv < order) then None
    else
      let sv' = if sv > q_half then order - sv else sv in
      Some (Seq.append (Seq.slice signature 0 32) (nat_to_be 32 sv'))

let secp256k1_ecdsa_sign_msg_as_qelem (m: qelem) (private_key nonce: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = match ecdsa_sign_msg_as_qelem m private_key nonce with
    | None -> None
    | Some sg -> signature_normalize sg

let secp256k1_ecdsa_verify_msg_as_qelem (m: qelem) (public_key: Seq.lseq S8.t 64)
                                        (sig_r sig_s: Seq.lseq S8.t 32) : GTot bool
  = is_normalized sig_s && ecdsa_verify_msg_as_qelem m public_key sig_r sig_s

(** {2 The hashed front ends}

    K-256 hashes with SHA2-256 and with nothing else, which is the whole of
    what HACL* offers for it. *)

let msg_ok (msg: Seq.seq S8.t) : prop = Seq.length msg < pow2 61

let msg_ok_hashable (msg: Seq.seq S8.t)
  : Lemma (requires msg_ok msg)
          (ensures Seq.length msg < Spec.SHA2.max_input #S32.t)
  = assert_norm (Spec.SHA2.max_input #S32.t == pow2 61)

(** The digest is thirty-two bytes, which is what [msg_as_qelem] wants. *)
let digest_is_32 (_: unit)
  : Lemma (Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_256 == 32)
  = assert_norm (Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_256 == 32)

let sha256_as_qelem (msg: Seq.seq S8.t { msg_ok msg }) : GTot qelem =
  msg_ok_hashable msg;
  digest_is_32 ();
  msg_as_qelem (Spec.SHA2.hash Spec.SHA2.Constants.sha2_256 msg)

let sign_sha256 (msg: Seq.seq S8.t { msg_ok msg }) (private_key nonce: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = ecdsa_sign_msg_as_qelem (sha256_as_qelem msg) private_key nonce

let verify_sha256 (msg: Seq.seq S8.t { msg_ok msg }) (public_key: Seq.lseq S8.t 64)
                  (sig_r sig_s: Seq.lseq S8.t 32) : GTot bool
  = ecdsa_verify_msg_as_qelem (sha256_as_qelem msg) public_key sig_r sig_s

let secp256k1_sign_sha256 (msg: Seq.seq S8.t { msg_ok msg })
                          (private_key nonce: Seq.lseq S8.t 32)
  : GTot (option (Seq.lseq S8.t 64))
  = secp256k1_ecdsa_sign_msg_as_qelem (sha256_as_qelem msg) private_key nonce

let secp256k1_verify_sha256 (msg: Seq.seq S8.t { msg_ok msg })
                            (public_key: Seq.lseq S8.t 64)
                            (sig_r sig_s: Seq.lseq S8.t 32) : GTot bool
  = secp256k1_ecdsa_verify_msg_as_qelem (sha256_as_qelem msg) public_key sig_r sig_s
