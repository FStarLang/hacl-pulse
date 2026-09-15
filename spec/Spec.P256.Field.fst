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

(** P-256's field prime and group order as two instances of
    {!Spec.Field256}.

    [mu] is [-m^-1 mod 2^16] and [ri] is [R^-1 mod m]; both are checked by
    normalisation, which is the only place in the module where the moduli
    appear as numbers at all.  The field prime's [mu] is [1], a small gift
    from its Solinas shape -- the only one this representation collects. *)
module Spec.P256.Field

include Spec.Field256

open Spec.Bignum256
open Spec.Montgomery256

module P = Spec.P256

#push-options "--fuel 1 --ifuel 1 --z3rlimit 50"

let fmod : modulus =
  assert_norm (P.prime < pow2 256);
  mk P.prime 1
     0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000

let fmod_ok (_: unit) : Lemma (modulus_ok fmod) =
  assert_norm (P.prime < pow2 256);
  assert_norm (1 < P.prime);
  assert_norm (1 < pow2 rad);
  assert_norm (((P.prime % pow2 rad) * 1 + 1) % pow2 rad == 0);
  assert_norm (pow2 256 *
    0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000
    % P.prime == 1);
  mk_ok P.prime 1
    0xfffffffe00000003fffffffd0000000200000001fffffffe0000000300000000

let qmod : modulus =
  assert_norm (P.order < pow2 256);
  mk P.order 48207
     0x60d066334905c1e907f8b6041e607725badef3e243566fafce1bc8f79c197c79

let qmod_ok (_: unit) : Lemma (modulus_ok qmod) =
  assert_norm (P.order < pow2 256);
  assert_norm (1 < P.order);
  assert_norm (48207 < pow2 rad);
  assert_norm (((P.order % pow2 rad) * 48207 + 1) % pow2 rad == 0);
  assert_norm (pow2 256 *
    0x60d066334905c1e907f8b6041e607725badef3e243566fafce1bc8f79c197c79
    % P.order == 1);
  mk_ok P.order 48207
    0x60d066334905c1e907f8b6041e607725badef3e243566fafce1bc8f79c197c79

#pop-options
