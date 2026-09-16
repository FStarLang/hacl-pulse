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

(** FrodoKEM's parameter sets.

    Which FrodoKEM?  The one HACL\* implements, and therefore the one this
    implements, is the variant that was later renamed **eFrodoKEM**: the
    ephemeral one, with no salt in the ciphertext.  The 2021 revision of the
    submission added a salt to the long-term variant and kept the unsalted
    construction under the [e] prefix; the byte sizes below, and the known
    answer tests in [tests/test_frodo.c], are eFrodoKEM's.

    As everywhere else in this library an algorithm is a record rather than
    an index.  The four members differ in six numbers and a hash choice, and
    Custard monomorphizes the record away, so [Hacl_Frodo640_crypto_kem_enc]
    and [Hacl_Frodo1344_crypto_kem_enc] are separate C functions with their
    dimensions as literals.

    [nbar], the width of the small matrices, is 8 in every parameter set that
    has ever been proposed, and is a constant here rather than a field.  That
    is worth doing: it makes [publicmatrixbytes] equal to [logq * n] instead
    of [logq * n * nbar / 8], and a division that is always exact is a
    division the solver still has to reason about. *)
module Spec.Frodo.Params


module Seq = FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module SZ = FStar.SizeT
module G = FStar.Ghost

(** The width of S, S', E, E' and E''.  Eight, always. *)
let nbar = 8

(** The seed for A, and hence the first sixteen bytes of every public key. *)
let bytes_seed_a = 16

noeq
type params = {
  (** The lattice dimension: 64 for the toy set, then 640, 976, 1344. *)
  nn: n: SZ.t { SZ.v n % 8 == 0 /\ 8 <= SZ.v n /\ SZ.v n <= 1344 };

  (** [log2 q].  Fifteen or sixteen; arithmetic is done modulo [2^16] and
      reduced to [logq] bits where the specification says so. *)
  logq: q: U32.t { 0 < U32.v q /\ U32.v q <= 16 };

  (** How many bits of the shared secret each matrix entry carries. *)
  bits: b: U32.t { 0 < U32.v b /\ U32.v b < U32.v logq /\ U32.v b <= 8 };

  (** The shared-secret length, which is also the seed and hash length. *)
  cbytes: c: SZ.t { 0 < SZ.v c /\ SZ.v c <= 32 };

  (** The error distribution, as the cumulative table the sampler compares
      against.  Read only by specifications: the implementation keeps its own
      static array and proves it equal, as the SHA-2 round constants do. *)
  ncdf: k: SZ.t { 2 <= SZ.v k /\ SZ.v k <= 16 };
  cdf: G.erased (Seq.lseq U16.t (SZ.v ncdf));

  (** SHAKE-256 rather than SHAKE-128.  A [bool] and not a function, so that
      the record stays first order and Custard can specialize on it. *)
  wide: bool;
}

(** {2 The dimensions, as [nat]s} *)

unfold let n (p: params) : k: pos { k % 8 == 0 /\ k <= 1344 } = SZ.v p.nn
unfold let logq (p: params) : k: pos { k <= 16 } = U32.v p.logq
unfold let bits (p: params) : k: pos { k < logq p /\ k <= 8 } = U32.v p.bits
unfold let crypto_bytes (p: params) : k: pos { k <= 32 } = SZ.v p.cbytes
unfold let cdf_len (p: params) : k: nat { 2 <= k /\ k <= 16 } = SZ.v p.ncdf

(** {2 Derived byte counts}

    Each is [logq] or two bytes per matrix entry, and every division in
    FrodoKEM's own presentation of these has been carried out. *)

(** B, packed: [n * nbar] entries of [logq] bits. *)
unfold let publicmatrixbytes (p: params) : pos = logq p * n p

(** S, serialized as two bytes per entry. *)
unfold let secretmatrixbytes (p: params) : pos = 16 * n p

(** c1 has the same shape as B; c2 is [nbar * nbar]. *)
unfold let ct1bytes (p: params) : pos = logq p * n p
unfold let ct2bytes (p: params) : pos = logq p * nbar

(** mu, the message: [nbar * nbar] entries of [bits] bits. *)
unfold let bytes_mu (p: params) : pos = bits p * nbar

unfold let crypto_publickeybytes (p: params) : pos =
  bytes_seed_a + publicmatrixbytes p

unfold let crypto_secretkeybytes (p: params) : pos =
  crypto_bytes p + crypto_publickeybytes p + secretmatrixbytes p + crypto_bytes p

unfold let crypto_ciphertextbytes (p: params) : pos = ct1bytes p + ct2bytes p

(** {2 The four parameter sets} *)

let cdf_640 : Seq.lseq U16.t 13 =
  Seq.seq_of_list [ 4643us; 13363us; 20579us; 25843us; 29227us; 31145us;
                    32103us; 32525us; 32689us; 32745us; 32762us; 32766us;
                    32767us ]

let cdf_976 : Seq.lseq U16.t 11 =
  Seq.seq_of_list [ 5638us; 15915us; 23689us; 28571us; 31116us; 32217us;
                    32613us; 32731us; 32760us; 32766us; 32767us ]

let cdf_1344 : Seq.lseq U16.t 7 =
  Seq.seq_of_list [ 9142us; 23462us; 30338us; 32361us; 32725us; 32765us;
                    32767us ]

(** A toy set, for testing only: 64 is nowhere near a security level.  HACL\*
    ships it in the public distribution and so does this, under a name that
    says what it is. *)
let frodo64 : params = {
  nn = 64sz; logq = 15ul; bits = 2ul; cbytes = 16sz;
  ncdf = 13sz; cdf = G.hide cdf_640; wide = false;
}

let frodo640 : params = {
  nn = 640sz; logq = 15ul; bits = 2ul; cbytes = 16sz;
  ncdf = 13sz; cdf = G.hide cdf_640; wide = false;
}

let frodo976 : params = {
  nn = 976sz; logq = 16ul; bits = 3ul; cbytes = 24sz;
  ncdf = 11sz; cdf = G.hide cdf_976; wide = true;
}

let frodo1344 : params = {
  nn = 1344sz; logq = 16ul; bits = 4ul; cbytes = 32sz;
  ncdf = 7sz; cdf = G.hide cdf_1344; wide = true;
}

(** The published byte counts, as a check that the arithmetic above agrees
    with the specification document. *)
let _ = assert_norm (crypto_publickeybytes frodo640 == 9616)
let _ = assert_norm (crypto_secretkeybytes frodo640 == 19888)
let _ = assert_norm (crypto_ciphertextbytes frodo640 == 9720)
let _ = assert_norm (crypto_publickeybytes frodo976 == 15632)
let _ = assert_norm (crypto_secretkeybytes frodo976 == 31296)
let _ = assert_norm (crypto_ciphertextbytes frodo976 == 15744)
let _ = assert_norm (crypto_publickeybytes frodo1344 == 21520)
let _ = assert_norm (crypto_secretkeybytes frodo1344 == 43088)
let _ = assert_norm (crypto_ciphertextbytes frodo1344 == 21632)
let _ = assert_norm (crypto_publickeybytes frodo64 == 976)
let _ = assert_norm (crypto_secretkeybytes frodo64 == 2032)
let _ = assert_norm (crypto_ciphertextbytes frodo64 == 1080)

(** {2 The hash}

    SHAKE with a variable output length, everywhere: to expand the seed for
    A, to expand the seeds for the error matrices, to hash the public key,
    and to derive the shared secret. *)

let shake (p: params) (msg: Seq.seq Hacl.Secret.UInt8.t) (outlen: nat)
  : Seq.lseq Hacl.Secret.UInt8.t outlen
  = if p.wide then Spec.SHA3.shake256 msg outlen else Spec.SHA3.shake128 msg outlen
