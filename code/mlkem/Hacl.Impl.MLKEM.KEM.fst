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


(** ML-KEM: key generation, encapsulation, decapsulation.

    FIPS 203 Algorithms 16 to 18, the Fujisaki-Okamoto transform over the
    K-PKE of {!Hacl.Impl.MLKEM.KPKE}.  One implementation covers the three
    parameter sets, in the same shape as K-PKE: the five parameters are
    ordinary arguments and the record they belong to is erased.

    All three entry points take their randomness as an argument.  The
    exposed API draws it instead, and lives in the wrappers.

    Decapsulation never branches on whether the ciphertext was well
    formed.  It re-encrypts, compares the result with what it received
    into a mask, and selects between the real key stream and [J(z || c)]
    with that mask; see {!Hacl.Impl.Select}. *)
module Hacl.Impl.MLKEM.KEM

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.MLKEM
open Spec.MLKEM.Params
open Hacl.Impl.MLKEM.KPKELemmas
open Hacl.Impl.MLKEM.KEMLemmas
open Hacl.Impl.MLKEM.KPKE

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module HSZ = Hacl.SizeT
module Seq = FStar.Seq
module S8 = Hacl.Secret.UInt8
module Copy = Hacl.Impl.Copy
module Sel = Hacl.Impl.Select
module Hash = Hacl.Impl.MLKEM.Hash

#push-options "--fuel 0 --ifuel 0 --z3rlimit 200"

(** Algorithm 16.  [d] seeds K-PKE, [z] is the implicit-rejection key. *)
fn keygen_impl (ek dk dseed zseed: A.array S8.t) (p: erased params) ([@@@FStar.Attributes.monomorphize] k: SZ.t) ([@@@FStar.Attributes.monomorphize] eta1: SZ.t)
               (#vek0 #vdk0: erased (Seq.seq S8.t))
               (#pd: perm) (#vd: erased (Seq.lseq S8.t 32))
               (#pz: perm) (#vz: erased (Seq.lseq S8.t 32))
requires A.pts_to ek vek0 ** A.pts_to dk vdk0 ** A.pts_to dseed #pd vd **
         A.pts_to zseed #pz vz **
         pure (SZ.v k == (reveal p).k /\ SZ.v eta1 == (reveal p).eta1 /\
               Seq.length vek0 == ek_len p /\ Seq.length vdk0 == dk_len p)
ensures exists* vek vdk.
  A.pts_to ek vek ** A.pts_to dk vdk ** A.pts_to dseed #pd vd **
  A.pts_to zseed #pz vz **
  pure (Seq.length vek == ek_len p /\ Seq.length vdk == dk_len p /\
        vek == fst (keygen p vd vz) /\ vdk == snd (keygen p vd vz))
{
  A.pts_to_len ek;
  A.pts_to_len dk;
  A.pts_to_len dseed;
  A.pts_to_len zseed;
  HSZ.fits32 ();
  assert_norm (4 * 384 + 96 < pow2 32);
  let k384 = SZ.mul k 384sz;
  let eklen = SZ.add k384 32sz;

  let mut dkp = [| (S8.zero <: S8.t); k384 |];
  kpke_keygen_impl ek dkp dseed p k eta1;
  with vek. assert (A.pts_to ek vek);
  with vdkp. assert (A.pts_to dkp vdkp);

  let mut hek = [| (S8.zero <: S8.t); 32sz |];
  Hash.hash_h_impl hek ek eklen;
  with vhek. assert (A.pts_to hek vhek);

  Copy.copy_prefix dk dkp k384;
  Copy.copy_at dk k384 ek eklen;
  Copy.copy_at dk (SZ.add k384 eklen) hek 32sz;
  Copy.copy_at dk (SZ.add (SZ.add k384 eklen) 32sz) zseed 32sz;
  with vdk. assert (A.pts_to dk vdk);
  append4_eq vdkp vek vhek vz vdk;
  kem_keygen_eq p vd vz vek vdk;
  assert (pure (vek == fst (keygen p vd vz) /\ vdk == snd (keygen p vd vz)));
}

(** Algorithm 17.  [m] is the 32-byte message; the shared secret and the
    encryption randomness are the two halves of [G(m || H(ek))]. *)
fn encaps_impl (ss ct ekey msg: A.array S8.t) (p: erased params)
               ([@@@FStar.Attributes.monomorphize] k: SZ.t) ([@@@FStar.Attributes.monomorphize] eta1: SZ.t)
               ([@@@FStar.Attributes.monomorphize] eta2: SZ.t) ([@@@FStar.Attributes.monomorphize] du: SZ.t)
               ([@@@FStar.Attributes.monomorphize] dv: SZ.t)
               (#vss0 #vct0: erased (Seq.seq S8.t))
               (#pe: perm) (#vek: erased (Seq.lseq S8.t (ek_len p)))
               (#pm: perm) (#vm: erased (Seq.lseq S8.t 32))
requires A.pts_to ss vss0 ** A.pts_to ct vct0 ** A.pts_to ekey #pe vek **
         A.pts_to msg #pm vm **
         pure (SZ.v k == (reveal p).k /\ SZ.v eta1 == (reveal p).eta1 /\
               SZ.v eta2 == (reveal p).eta2 /\ SZ.v du == (reveal p).du /\
               SZ.v dv == (reveal p).dv /\
               Seq.length vss0 == 32 /\ Seq.length vct0 == ct_len p)
ensures exists* vss vct.
  A.pts_to ss vss ** A.pts_to ct vct ** A.pts_to ekey #pe vek **
  A.pts_to msg #pm vm **
  pure (Seq.length vss == 32 /\ Seq.length vct == ct_len p /\
        vss == fst (encaps p vek vm) /\ vct == snd (encaps p vek vm))
{
  A.pts_to_len ss;
  A.pts_to_len ct;
  A.pts_to_len ekey;
  A.pts_to_len msg;
  HSZ.fits32 ();
  assert_norm (4 * 384 + 96 < pow2 32);
  let eklen = SZ.add (SZ.mul k 384sz) 32sz;

  let mut hek = [| (S8.zero <: S8.t); 32sz |];
  Hash.hash_h_impl hek ekey eklen;
  with vhek. assert (A.pts_to hek vhek);

  let mut gin = [| (S8.zero <: S8.t); 64sz |];
  Copy.copy_prefix gin msg 32sz;
  Copy.copy_at gin 32sz hek 32sz;
  with vgin. assert (A.pts_to gin vgin);
  append2_eq vm vhek vgin;

  let mut g = [| (S8.zero <: S8.t); 64sz |];
  Hash.hash_g_impl g gin 64sz;
  with vg. assert (A.pts_to g vg);
  assert (pure (vg == hash_g (Seq.append vm (hash_h vek))));

  Copy.copy_prefix ss g 32sz;
  with vss. assert (A.pts_to ss vss);
  slice_eq vg 0 vss;

  let mut r = [| (S8.zero <: S8.t); 32sz |];
  Copy.copy_range r 0sz g 32sz 32sz;
  with vr. assert (A.pts_to r vr);
  slice_eq vg 32 vr;

  kpke_encrypt_impl ct ekey msg r p k eta1 eta2 du dv;
  with vct. assert (A.pts_to ct vct);
  encaps_eq p vek vm vss vct;
  assert (pure (vss == fst (encaps p vek vm) /\ vct == snd (encaps p vek vm)));
}

(** Algorithm 18.  Decapsulation always returns a key: on a ciphertext
    that does not re-encrypt to itself it returns [J(z || c)], which is
    indistinguishable from a real one to anyone without [z]. *)
fn decaps_impl (ss dkey ct: A.array S8.t) (p: erased params)
               ([@@@FStar.Attributes.monomorphize] k: SZ.t) ([@@@FStar.Attributes.monomorphize] eta1: SZ.t)
               ([@@@FStar.Attributes.monomorphize] eta2: SZ.t) ([@@@FStar.Attributes.monomorphize] du: SZ.t)
               ([@@@FStar.Attributes.monomorphize] dv: SZ.t)
               (#vss0: erased (Seq.seq S8.t))
               (#pd: perm) (#vdk: erased (Seq.lseq S8.t (dk_len p)))
               (#pc: perm) (#vc: erased (Seq.lseq S8.t (ct_len p)))
requires A.pts_to ss vss0 ** A.pts_to dkey #pd vdk ** A.pts_to ct #pc vc **
         pure (SZ.v k == (reveal p).k /\ SZ.v eta1 == (reveal p).eta1 /\
               SZ.v eta2 == (reveal p).eta2 /\ SZ.v du == (reveal p).du /\
               SZ.v dv == (reveal p).dv /\ Seq.length vss0 == 32)
ensures exists* vss.
  A.pts_to ss vss ** A.pts_to dkey #pd vdk ** A.pts_to ct #pc vc **
  pure (Seq.length vss == 32 /\ vss == decaps p vdk vc)
{
  A.pts_to_len ss;
  A.pts_to_len dkey;
  A.pts_to_len ct;
  HSZ.fits32 ();
  assert_norm (4 * 384 + 96 < pow2 32);
  assert_norm (4 * (32 * 11) + 32 * 11 + 32 < pow2 32);
  SZ.fits_u32_implies_fits (32 * SZ.v du);
  SZ.fits_u32_implies_fits (SZ.v k * (32 * SZ.v du));
  SZ.fits_u32_implies_fits (32 * SZ.v dv);
  SZ.fits_u32_implies_fits (SZ.v k * (32 * SZ.v du) + 32 * SZ.v dv);
  let k384 = SZ.mul k 384sz;
  let eklen = SZ.add k384 32sz;
  let ctlen = SZ.add (SZ.mul k (SZ.mul 32sz du)) (SZ.mul 32sz dv);
  assert (pure (SZ.v ctlen == ct_len p /\ SZ.v eklen == ek_len p /\
                SZ.v k384 == dk_pke_len p));
  SZ.fits_u32_implies_fits (32 + SZ.v ctlen);

  (* the four pieces of the decapsulation key *)
  let mut dkp = [| (S8.zero <: S8.t); k384 |];
  Copy.copy_prefix dkp dkey k384;
  with vdkp. assert (A.pts_to dkp vdkp);
  slice_eq vdk 0 vdkp;
  let mut ekey = [| (S8.zero <: S8.t); eklen |];
  Copy.copy_range ekey 0sz dkey k384 eklen;
  with vekey. assert (A.pts_to ekey vekey);
  slice_eq vdk (dk_pke_len p) vekey;
  let mut h = [| (S8.zero <: S8.t); 32sz |];
  Copy.copy_range h 0sz dkey (SZ.add k384 eklen) 32sz;
  with vh. assert (A.pts_to h vh);
  slice_eq vdk (dk_pke_len p + ek_len p) vh;
  let mut z = [| (S8.zero <: S8.t); 32sz |];
  Copy.copy_range z 0sz dkey (SZ.add (SZ.add k384 eklen) 32sz) 32sz;
  with vz. assert (A.pts_to z vz);
  slice_eq vdk (dk_pke_len p + ek_len p + 32) vz;
  dk_len_eq p;
  assert (pure (vz == Seq.slice vdk (dk_pke_len p + ek_len p + 32) (dk_len p)));

  (* decrypt, then re-derive the key stream and the randomness *)
  let mut m = [| (S8.zero <: S8.t); 32sz |];
  kpke_decrypt_impl m dkp ct p k du dv;
  with vm. assert (A.pts_to m vm);
  let mut gin = [| (S8.zero <: S8.t); 64sz |];
  Copy.copy_prefix gin m 32sz;
  Copy.copy_at gin 32sz h 32sz;
  with vgin. assert (A.pts_to gin vgin);
  append2_eq vm vh vgin;
  let mut g = [| (S8.zero <: S8.t); 64sz |];
  Hash.hash_g_impl g gin 64sz;
  with vg. assert (A.pts_to g vg);
  let mut kk = [| (S8.zero <: S8.t); 32sz |];
  Copy.copy_prefix kk g 32sz;
  with vkk. assert (A.pts_to kk vkk);
  slice_eq vg 0 vkk;
  let mut r = [| (S8.zero <: S8.t); 32sz |];
  Copy.copy_range r 0sz g 32sz 32sz;
  with vr. assert (A.pts_to r vr);
  slice_eq vg 32 vr;

  (* re-encrypt and compare *)
  let mut c2 = [| (S8.zero <: S8.t); ctlen |];
  kpke_encrypt_impl c2 ekey m r p k eta1 eta2 du dv;
  with vc2. assert (A.pts_to c2 vc2);
  let mask = Sel.eq_mask_bytes ct c2 ctlen;

  (* the rejection value *)
  let mut jin = [| (S8.zero <: S8.t); SZ.add 32sz ctlen |];
  Copy.copy_prefix jin z 32sz;
  Copy.copy_at jin 32sz ct ctlen;
  with vjin. assert (A.pts_to jin vjin);
  append2_eq vz vc vjin;
  let mut jj = [| (S8.zero <: S8.t); 32sz |];
  Hash.hash_j_impl jj jin (SZ.add 32sz ctlen);
  with vjj. assert (A.pts_to jj vjj);
  assert (pure (vjj == hash_j (Seq.append (Seq.slice vdk (dk_pke_len p + ek_len p + 32) (dk_len p)) vc)));

  Sel.select_copy ss 0sz kk jj 32sz mask;
  with vss. assert (A.pts_to ss vss);
  decaps_eq p vdk vc mask vkk vjj vss vc2;
  assert (pure (vss == decaps p vdk vc));
}
