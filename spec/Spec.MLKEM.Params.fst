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

(** The three ML-KEM parameter sets, FIPS 203 table 2.

    Only five numbers change between them, and [q], [n] and the hash
    functions do not change at all -- which is why this library has one
    implementation and three thin wrappers rather than three
    implementations.  Every field carries the refinement the algorithms
    need, so a caller that builds its own parameter record cannot produce
    one the implementation will reject at run time. *)
module Spec.MLKEM.Params

open Spec.MLKEM.Zq

noeq
type params = {
  (** The module rank: the secret is a [k]-vector and [A-hat] is [k x k]. *)
  k: r: pos { r == 2 \/ r == 3 \/ r == 4 };
  (** The noise width for the secret and the first error, and for the
      second.  They differ only for ML-KEM-512. *)
  eta1: e: pos { e <= 3 };
  eta2: e: pos { e <= 3 };
  (** How many bits survive compression of the two ciphertext components. *)
  du: d: pos { d <= 11 };
  dv: d: pos { d <= 11 };
}

let mlkem512  : params = { k = 2; eta1 = 3; eta2 = 2; du = 10; dv = 4 }
let mlkem768  : params = { k = 3; eta1 = 2; eta2 = 2; du = 10; dv = 4 }
let mlkem1024 : params = { k = 4; eta1 = 2; eta2 = 2; du = 11; dv = 5 }

(** {2 Derived sizes}

    All in bytes.  A polynomial costs [32 d] bytes at [d] bits per
    coefficient, so an uncompressed one costs 384. *)

(** The K-PKE encryption key: [k] polynomials of [t-hat] and the 32-byte
    [rho] that regenerates [A-hat].  This is also the ML-KEM encapsulation
    key. *)
let ek_len (p: params) : pos = 384 * p.k + 32

(** The K-PKE decryption key: [k] polynomials of [s-hat]. *)
let dk_pke_len (p: params) : pos = 384 * p.k

(** The ML-KEM decapsulation key: [dk_pke], the encapsulation key, its
    hash, and the 32-byte implicit-rejection secret [z]. *)
let dk_len (p: params) : pos = 768 * p.k + 96

(** The ciphertext: [k] polynomials at [du] bits and one at [dv]. *)
let ct_len (p: params) : pos = 32 * (p.du * p.k + p.dv)

(** The shared secret, and the seeds, all 32 bytes. *)
let ss_len : pos = 32

let ek_len_eq (p: params) : Lemma (ek_len p == p.k * (32 * 12) + 32) = ()

let dk_len_eq (p: params) : Lemma (dk_len p == dk_pke_len p + ek_len p + 32 + 32) = ()

let ct_len_eq (p: params) : Lemma (ct_len p == p.k * (32 * p.du) + 32 * p.dv) = ()
