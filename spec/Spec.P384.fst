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

(** NIST P-384 (secp384r1): ECDSA and ECDH.

    The curve is [y^2 = x^3 - 3x + b] over [F_p], exactly the shape of
    P-256 with bigger numbers, so everything [Spec.P256] says about the
    representation carries over: big-endian bytes, projective points
    [(X : Y : Z)] with [Z = 0] at infinity, and the complete
    Renes--Costello--Batina addition law for [a = -3], which needs no case
    analysis on equal or opposite points.

    The API is that of [Spec.P256] at the larger size: raw [x || y] public
    keys, raw [r || s] signatures, a caller-supplied nonce, and an ECDH
    shared secret that is the whole point rather than its x-coordinate.

    As in the rest of the library, nothing here is constant time and nothing
    here is fast; the specification exists to be matched, not run. *)
module Spec.P384

open Hacl.Spec.Bytes
open Spec.ModArith
open Hacl.Secret.Word
open Hacl.Secret.Word.Instances

module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module S32 = Hacl.Secret.UInt32
module S64 = Hacl.Secret.UInt64
module Loops = Hacl.Spec.Loops
module MA = Spec.ModArith

(** {2 The two moduli} *)

(** [p = 2^384 - 2^128 - 2^96 + 2^32 - 1]. *)
let prime : p: pos { 1 < p /\ p % 4 == 3 } =
  assert_norm (pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 > 1);
  assert_norm ((pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1) % 4 == 3);
  pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1

(** The order of the group, which is prime: the cofactor is one and
    public-key validation is exactly "is on the curve". *)
let order : q: pos { 1 < q } =
  assert_norm (0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973 > 1);
  0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973

(** {2 The field and the scalar field} *)

let felem = elem prime
let qelem = elem order

let fadd (x y: felem) : felem = add x y
let fsub (x y: felem) : felem = sub x y
let fmul (x y: felem) : felem = mul x y
let fneg (x: felem) : felem = neg x
let finv (x: felem) : felem = inv x

let qadd (x y: qelem) : qelem = add x y
let qmul (x y: qelem) : qelem = mul x y
let qinv (x: qelem) : qelem = inv x

let fzero : felem = MA.zero
let fone : felem = MA.one

(** {2 Curve parameters} *)

let b_coeff : felem =
  assert_norm (0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef < prime);
  0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef

let g_x : felem =
  assert_norm (0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7 < prime);
  0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7

let g_y : felem =
  assert_norm (0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f < prime);
  0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f

(** {2 Points} *)

type proj_point = felem & felem & felem

let point_at_infinity : proj_point = (fzero, fone, fzero)

let g : proj_point = (g_x, g_y, fone)

let is_point_at_infinity (p: proj_point) : bool =
  let (_, _, z) = p in z = fzero

let to_aff_point (p: proj_point) : felem & felem =
  let (x, y, z) = p in
  let zi = finv z in
  (fmul x zi, fmul y zi)

let is_on_curve (x y: felem) : bool =
  let x3 = fmul (fmul x x) x in
  let three : felem = assert_norm (3 < prime); 3 in
  fmul y y = fadd (fsub x3 (fmul three x)) b_coeff

(** {3 The complete addition law}

    Renes--Costello--Batina 2016, Algorithm 4 for [a = -3], verbatim from
    [Spec.P256]; only [b] differs. *)
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

(** Algorithm 6 of the same paper: doubling for [a = -3]. *)
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

    Double-and-add over the 384 bits of the scalar, most significant
    first.  The implementation runs exactly this loop, so no group law is
    needed to connect the two. *)

let bit (k: nat) (i: nat) : n: nat { n < 2 } = (k / pow2 i) % 2

let point_select (b: nat { b < 2 }) (p q: proj_point) : proj_point =
  if b = 1 then q else p

let point_mul_step (k: nat) (p: proj_point) (i: nat { i < 384 })
                   (acc: proj_point) : proj_point =
  let acc = point_double acc in
  point_select (bit k (383 - i)) acc (point_add acc p)

let point_mul_at (k: nat) (p: proj_point) (i: nat) (acc: proj_point) : proj_point =
  if i < 384 then point_mul_step k p i acc else acc

let point_mul (k: nat) (p: proj_point) : GTot proj_point =
  Loops.repeati_g 384 (point_mul_at k p) point_at_infinity

let point_mul_g (k: nat) : GTot proj_point = point_mul k g

(** [u1 G + u2 Q], the combination verification needs. *)
let point_mul_double_g (u1 u2: nat) (q: proj_point) : GTot proj_point =
  point_add (point_mul u1 g) (point_mul u2 q)

(** {2 Byte encodings}

    A coordinate is forty-eight big-endian bytes; a raw public key is
    [x || y] and is ninety-six. *)

let load_felem (s: Seq.lseq S8.t 48) : GTot (option felem) =
  let x = be_nat s in
  if x < prime then Some x else None

let store_felem (x: felem) : Seq.lseq S8.t 48 = nat_to_be 48 x

(** A raw point is accepted exactly when it satisfies the curve equation.
    That already excludes [(0, 0)] because [b] is not zero. *)
let load_point (s: Seq.lseq S8.t 96) : GTot (option proj_point) =
  let xs = Seq.slice s 0 48 in
  let ys = Seq.slice s 48 96 in
  match load_felem xs, load_felem ys with
  | Some x, Some y -> if is_on_curve x y then Some (x, y, fone) else None
  | _ -> None

let store_point (p: proj_point) : Seq.lseq S8.t 96 =
  let (x, y) = to_aff_point p in
  Seq.append (store_felem x) (store_felem y)

(** {2 Key validation} *)

let validate_private_key (s: Seq.lseq S8.t 48) : GTot bool =
  let k = be_nat s in 0 < k && k < order

let validate_public_key (s: Seq.lseq S8.t 96) : GTot bool =
  Some? (load_point s)

(** {2 ECDH}

    [dh_initiator] is also key generation: it maps a private key to its
    public key. *)

let dh_initiator (private_key: Seq.lseq S8.t 48) : GTot (option (Seq.lseq S8.t 96)) =
  let sk = be_nat private_key in
  if 0 < sk && sk < order then Some (store_point (point_mul_g sk)) else None

let dh_responder (their_pk: Seq.lseq S8.t 96) (private_key: Seq.lseq S8.t 48)
  : GTot (option (Seq.lseq S8.t 96))
  = let sk = be_nat private_key in
    match load_point their_pk with
    | None -> None
    | Some q ->
      if 0 < sk && sk < order then
        let r = point_mul sk q in
        if is_point_at_infinity r then None else Some (store_point r)
      else None

(** {2 ECDSA} *)

(** The message representative: the leading 48 bytes, read big-endian and
    reduced.  With a 384-bit hash and a 384-bit order this coincides with
    the bit-length truncation of FIPS 186. *)
let msg_as_qelem (msg: Seq.seq S8.t { 48 <= Seq.length msg }) : GTot qelem =
  be_nat (Seq.slice msg 0 48) % order

(** The nonce is an input, as in [Spec.P256]; reusing one reveals the
    private key.  The signature is raw [r || s], ninety-six bytes. *)
let ecdsa_sign_msg_as_qelem (m: qelem) (private_key nonce: Seq.lseq S8.t 48)
  : GTot (option (Seq.lseq S8.t 96))
  = let sk = be_nat private_key in
    let k = be_nat nonce in
    if not (0 < sk && sk < order && 0 < k && k < order) then None
    else begin
      let (px, _) = to_aff_point (point_mul_g k) in
      let r : qelem = px % order in
      let s : qelem = qmul (qinv k) (qadd m (qmul r sk)) in
      if r = 0 || s = 0 then None
      else Some (Seq.append (nat_to_be 48 r) (nat_to_be 48 s))
    end

let ecdsa_verify_msg_as_qelem (m: qelem) (public_key: Seq.lseq S8.t 96)
                              (signature: Seq.lseq S8.t 96) : GTot bool
  = let r = be_nat (Seq.slice signature 0 48) in
    let s = be_nat (Seq.slice signature 48 96) in
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

let msg_ok (msg: Seq.seq S8.t) : prop = Seq.length msg < pow2 61

let sha384_ok (msg: Seq.seq S8.t)
  : Lemma (requires msg_ok msg)
          (ensures Seq.length msg < Spec.SHA2.max_input #S64.t /\
                   Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_384 == 48)
  = assert_norm (pow2 61 <= pow2 125);
    assert_norm (Spec.SHA2.max_input #S64.t == pow2 125);
    assert_norm (Spec.SHA2.hash_bytes Spec.SHA2.Constants.sha2_384 == 48)

let sha384_as_qelem (msg: Seq.seq S8.t { msg_ok msg }) : GTot qelem =
  sha384_ok msg;
  msg_as_qelem (Spec.SHA2.hash Spec.SHA2.Constants.sha2_384 msg)

let sign_sha384 (msg: Seq.seq S8.t { msg_ok msg }) (private_key nonce: Seq.lseq S8.t 48)
  : GTot (option (Seq.lseq S8.t 96))
  = ecdsa_sign_msg_as_qelem (sha384_as_qelem msg) private_key nonce

let verify_sha384 (msg: Seq.seq S8.t { msg_ok msg }) (public_key: Seq.lseq S8.t 96)
                  (signature: Seq.lseq S8.t 96) : GTot bool
  = ecdsa_verify_msg_as_qelem (sha384_as_qelem msg) public_key signature
