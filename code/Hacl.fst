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

(** The root of the extracted library.

    Custard extracts a whole program: you hand it one module and a list of
    entry points, and it emits everything those entry points reach.  The
    library used to be extracted as sixteen such programs, one per algorithm
    family, which meant sixteen copies of the secret-integer layer, three
    copies of SHA-2 (HMAC, HKDF and the DRBG each reach it), and no way to link
    any two of them into the same binary.

    This module exists so that there is one program instead.  It names every
    entry module, so that every entry point is in scope of a single Custard
    invocation; the invocation then emits one [Hacl.c] in which everything
    shared is shared.  The [--custard_entry] list lives in the Makefile, next
    to the rest of the build, since it is a statement about what the library
    exports rather than about what F* proves.

    The modules named here are the implementations themselves: there is no
    wrapper layer, so a C name is the F* name with the dots turned into
    underscores. *)
module Hacl

module Hash_MD5 = Hacl.Hash.MD5
module Streaming_MD5 = Hacl.Streaming.MD5
module Hash_SHA1 = Hacl.Hash.SHA1
module Streaming_SHA1 = Hacl.Streaming.SHA1
module HMAC_SHA1 = Hacl.HMAC.SHA1
module Hash_SHA2 = Hacl.Hash.SHA2
module Streaming_SHA2 = Hacl.Streaming.SHA2
module Hash_SHA3 = Hacl.Hash.SHA3
module Streaming_SHA3 = Hacl.Streaming.SHA3
module Hash_Blake2 = Hacl.Hash.Blake2.Named
module Streaming_Blake2 = Hacl.Streaming.Blake2
module Chacha20 = Hacl.Chacha20
module Poly1305 = Hacl.Poly1305
module Chacha20Poly1305 = Hacl.Chacha20Poly1305
module Salsa20 = Hacl.Salsa20
module NaCl = Hacl.NaCl
module HMAC = Hacl.HMAC
module Streaming_HMAC = Hacl.Streaming.HMAC
module HKDF = Hacl.HKDF
module Curve25519 = Hacl.Curve25519
module Ed25519 = Hacl.Ed25519
module P256 = Hacl.P256
module P256_Key = Hacl.P256.Key
module P256_Key_Public = Hacl.P256.Key.Public
module P256_Sec1 = Hacl.P256.Sec1
module P256_Ecdh = Hacl.P256.Ecdh
module K256 = Hacl.K256
module K256_Key = Hacl.K256.Key
module K256_Key_Public = Hacl.K256.Key.Public
module K256_LowS = Hacl.K256.LowS
module K256_Sec1 = Hacl.K256.Sec1
module K256_Ecdh = Hacl.K256.Ecdh
module DRBG = Hacl.HMAC.DRBG
module AES_GCM = Hacl.AES.GCM
module Bignum = Hacl.Bignum.Base
module Bignum_Convert = Hacl.Bignum.Convert
module Bignum_Montgomery = Hacl.Bignum.Montgomery
module Bignum_Exponentiation = Hacl.Bignum.Exponentiation
module FFDHE = Hacl.FFDHE
module RSAPSS = Hacl.RSAPSS
module Frodo64 = Hacl.Frodo64
module Frodo640 = Hacl.Frodo640
module Frodo976 = Hacl.Frodo976
module Frodo1344 = Hacl.Frodo1344
module HPKE = Hacl.HPKE.Suites
