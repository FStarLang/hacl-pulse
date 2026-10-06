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

(** FrodoKEM: key generation, encapsulation, decapsulation.

    One implementation, four parameter sets.  The parameter record is an
    ordinary argument and every buffer is allocated at a size computed from
    it, so there is no per-set duplication; the wrappers in
    [Hacl.Frodo640] and friends are a dozen lines each.

    All three entry points here take their randomness as an argument.  The
    exposed API draws it instead, and lives in the wrappers.

    A note on stack.  A is streamed (see [Hacl.Frodo.Gen]) but the error
    matrices are not: key generation holds S, E, B and the SHAKE output
    that seeds the first two, which is about a hundred and thirty kilobytes
    at Frodo-1344.  That is inherent to the scheme -- the matrices are the
    key -- and is what the reference implementation does too. *)
module Hacl.Frodo.KEM

#lang-pulse

open Pulse.Lib.Pervasives
open Spec.Frodo.Params

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module S8 = Hacl.Secret.UInt8
module S16 = Hacl.Secret.UInt16
module M = Spec.Frodo.Matrix
module F = Spec.Frodo
module Math = FStar.Math.Lemmas
module G = FStar.Ghost
module Copy = Hacl.Impl.Copy
module Pack = Hacl.Frodo.Pack
module Mat = Hacl.Frodo.Matrix
module Sample = Hacl.Frodo.Sample
module Encode = Hacl.Frodo.Encode
module Decode = Hacl.Frodo.Decode
module Gen = Hacl.Frodo.Gen
module Cast = Hacl.Secret.Cast
module SEM = FStar.IndefiniteDescription

(** {2 Reading a concatenation back}

    Every buffer below is filled a piece at a time, and the specification
    says what it is with [Seq.append] and [Seq.slice].  These four turn one
    into the other; they are all [lemma_eq_intro] once the indexing lemmas
    of [FStar.Seq] have fired. *)

let slice_eq (v: Seq.seq S8.t) (base: nat) (r: Seq.seq S8.t)
  : Lemma (requires base + Seq.length r <= Seq.length v /\
                    (forall (k: nat). k < Seq.length r ==>
                       Seq.index r k == Seq.index v (base + k)))
          (ensures r == Seq.slice v base (base + Seq.length r))
  = Seq.lemma_eq_intro r (Seq.slice v base (base + Seq.length r))

let append2_eq (a b res: Seq.seq S8.t)
  : Lemma (requires Seq.length res == Seq.length a + Seq.length b /\
                    (forall (k: nat). k < Seq.length a ==> Seq.index res k == Seq.index a k) /\
                    (forall (k: nat). k < Seq.length b ==>
                       Seq.index res (Seq.length a + k) == Seq.index b k))
          (ensures res == Seq.append a b)
  = Seq.lemma_eq_intro res (Seq.append a b)

#push-options "--z3rlimit 100"
let append4_eq (a b c d res: Seq.seq S8.t)
  : Lemma (requires Seq.length res == Seq.length a + Seq.length b + Seq.length c + Seq.length d /\
                    (forall (k: nat). k < Seq.length a ==> Seq.index res k == Seq.index a k) /\
                    (forall (k: nat). k < Seq.length b ==>
                       Seq.index res (Seq.length a + k) == Seq.index b k) /\
                    (forall (k: nat). k < Seq.length c ==>
                       Seq.index res (Seq.length a + Seq.length b + k) == Seq.index c k) /\
                    (forall (k: nat). k < Seq.length d ==>
                       Seq.index res (Seq.length a + Seq.length b + Seq.length c + k) ==
                         Seq.index d k))
          (ensures res == Seq.append a (Seq.append b (Seq.append c d)))
  = (* The three nested lengths, which the pointwise step below needs and
       which the solver no longer derives on its own. *)
    Seq.lemma_len_append c d;
    Seq.lemma_len_append b (Seq.append c d);
    Seq.lemma_len_append a (Seq.append b (Seq.append c d));
    Seq.lemma_eq_intro res (Seq.append a (Seq.append b (Seq.append c d)))
#pop-options

(** A one-byte domain separator in front of a seed. *)
let cons_eq (x: S8.t) (s res: Seq.seq S8.t)
  : Lemma (requires Seq.length res == 1 + Seq.length s /\ Seq.index res 0 == x /\
                    (forall (k: nat). k < Seq.length s ==> Seq.index res (1 + k) == Seq.index s k))
          (ensures res == Seq.cons x s)
  = Seq.lemma_eq_intro res (Seq.cons x s)

(** Key generation, spelled out.  The Pulse function below establishes
    these equations one buffer at a time; unfolding [Spec.Frodo.keypair]
    against them is a single pure query, which is the only way it fits in
    an rlimit. *)
let keypair_eq (p: params)
               (coins: Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a))
               (vpk: Seq.lseq S8.t (crypto_publickeybytes p))
               (vsk: Seq.lseq S8.t (crypto_secretkeybytes p))
  : Lemma
      (requires
        (let cb = crypto_bytes p in
         let smb = secretmatrixbytes p in
         let seed_a = shake p (Seq.slice coins (2 * cb) (2 * cb + 16)) 16 in
         let r = shake p (Seq.cons (S8.classify 0x5fuy) (Seq.slice coins cb (2 * cb)))
                       (2 * smb) in
         let st = F.sample_matrix p nbar (n p) (Seq.slice r 0 smb) in
         let e = F.sample_matrix p (n p) nbar (Seq.slice r smb (2 * smb)) in
         let b = M.add (n p) nbar
                   (M.mul_t (n p) (n p) nbar (F.gen_matrix p seed_a) st) e in
         vpk == Seq.append seed_a (F.pack_n p b) /\
         vsk == Seq.append (Seq.slice coins 0 cb)
                  (Seq.append vpk
                     (Seq.append (M.to_bytes nbar (n p) st) (shake p vpk cb)))))
      (ensures vpk == fst (F.keypair p coins) /\ vsk == snd (F.keypair p coins))
  = ()

#push-options "--z3rlimit 400 --fuel 0 --ifuel 0"

(** The parameter set's extendable output function: SHAKE-256 for the two
    wide sets, SHAKE-128 for the others.  Note that this is {i not} what
    expands A, which is SHAKE-128 always. *)
fn shake_p ([@@@FStar.Attributes.monomorphize] p: params)
           (out: A.array S8.t) (out_len: SZ.t) (msg: A.array S8.t) (msg_len: SZ.t)
           (#vout0: erased (Seq.seq S8.t)) (#pm: perm) (#vm: erased (Seq.seq S8.t))
requires A.pts_to out vout0 ** A.pts_to msg #pm vm **
         pure (SZ.v msg_len == Seq.length vm /\ SZ.v out_len == Seq.length vout0)
ensures exists* vout. A.pts_to out vout ** A.pts_to msg #pm vm **
        pure (vout == shake p vm (Seq.length vout0))
{
  if p.wide { Hacl.Hash.SHA3.shake256 out out_len msg msg_len }
  else { Hacl.Hash.SHA3.shake128 out out_len msg msg_len }
}

(** Key generation from explicit coins [s || seed_se || z]. *)
fn keypair_coins ([@@@FStar.Attributes.monomorphize] p: params)
                 (cdf: A.array U16.t) (pk: A.array S8.t) (sk: A.array S8.t)
                 (coins: A.array S8.t)
                 (#pcd: perm) (#pc: perm)
                 (#vcdf: erased (Seq.lseq U16.t (cdf_len p)))
                 (#vpk0: erased (Seq.lseq S8.t (crypto_publickeybytes p)))
                 (#vsk0: erased (Seq.lseq S8.t (crypto_secretkeybytes p)))
                 (#vcoins: erased (Seq.lseq S8.t (2 * crypto_bytes p + bytes_seed_a)))
requires A.pts_to cdf #pcd vcdf ** A.pts_to pk vpk0 ** A.pts_to sk vsk0 **
         A.pts_to coins #pc vcoins ** pure (reveal vcdf == reveal p.cdf)
ensures exists* vpk vsk.
        A.pts_to cdf #pcd vcdf ** A.pts_to pk vpk ** A.pts_to sk vsk **
        A.pts_to coins #pc vcoins **
        pure (vpk == fst (F.keypair p vcoins) /\ vsk == snd (F.keypair p vcoins))
{
  A.pts_to_len cdf;
  A.pts_to_len pk;
  A.pts_to_len sk;
  A.pts_to_len coins;
  Hacl.SizeT.fits32 ();
  let cb = p.cbytes;
  let nn = p.nn;
  let d = SZ.uint32_to_sizet p.logq;
  let ents = SZ.mul 8sz nn;
  let smb = SZ.mul 2sz ents;
  let pmb = SZ.mul d nn;
  let pkb = SZ.add 16sz pmb;
  let two_smb = SZ.mul 2sz smb;
  assert_norm (16 * 1344 < pow2 32);
  SZ.fits_u32_implies_fits (2 * SZ.v ents);
  assert (pure (SZ.v ents == nbar * n p /\ SZ.v smb == secretmatrixbytes p /\
                SZ.v smb == 2 * SZ.v ents /\
                SZ.v pmb == publicmatrixbytes p /\
                SZ.v pkb == crypto_publickeybytes p /\
                SZ.fits (2 * SZ.v ents)));

  let mut z = [| (S8.zero <: S8.t); 16sz |];
  Copy.copy_range z 0sz coins (SZ.mul 2sz cb) 16sz;
  with vz. assert (A.pts_to z vz);
  slice_eq vcoins (2 * crypto_bytes p) vz;

  let mut sa = [| (S8.zero <: S8.t); 16sz |];
  shake_p p sa 16sz z 16sz;
  with vsa. assert (A.pts_to sa vsa);
  assert (pure (vsa == shake p (Seq.slice vcoins (2 * crypto_bytes p)
                                              (2 * crypto_bytes p + 16)) 16));

  let mut mb = [| (S8.zero <: S8.t); SZ.add 1sz cb |];
  A.((mb.(0sz) <- S8.classify 0x5fuy));
  Copy.copy_range mb 1sz coins cb cb;
  with vmb. assert (A.pts_to mb vmb);
  slice_eq vcoins (crypto_bytes p) (Seq.slice vcoins (crypto_bytes p) (2 * crypto_bytes p));
  cons_eq (S8.classify 0x5fuy)
          (Seq.slice vcoins (crypto_bytes p) (2 * crypto_bytes p)) vmb;

  let mut r = [| (S8.zero <: S8.t); two_smb |];
  shake_p p r two_smb mb (SZ.add 1sz cb);

  let mut st = [| (S16.zero <: S16.t); ents |];
  let mut e = [| (S16.zero <: S16.t); ents |];
  with vr. assert (A.pts_to r vr);
  slice_eq vr 0 (Seq.slice vr 0 (secretmatrixbytes p));
  slice_eq vr (secretmatrixbytes p)
           (Seq.slice vr (secretmatrixbytes p) (2 * secretmatrixbytes p));
  assert (pure (vr == shake p (Seq.cons (S8.classify 0x5fuy)
                                 (Seq.slice vcoins (crypto_bytes p) (2 * crypto_bytes p)))
                              (2 * secretmatrixbytes p)));
  Sample.sample_matrix p cdf st r 8sz nn two_smb 0sz;
  Sample.sample_matrix p cdf e r nn 8sz two_smb smb;
  with vst. assert (A.pts_to st vst);
  with ve. assert (A.pts_to e ve);
  assert (pure (vst == F.sample_matrix p nbar (n p)
                         (Seq.slice vr 0 (secretmatrixbytes p))));
  assert (pure (ve == F.sample_matrix p (n p) nbar
                        (Seq.slice vr (secretmatrixbytes p) (2 * secretmatrixbytes p))));

  let mut b = [| (S16.zero <: S16.t); ents |];
  Gen.mul_t_as p sa st b;
  Mat.add b e ents #(n p) #nbar;
  with vb. assert (A.pts_to b vb);
  assert (pure (vb == M.add (n p) nbar
                        (M.mul_t (n p) (n p) nbar (F.gen_matrix p vsa) vst) ve));

  let mut pb = [| (S8.zero <: S8.t); pmb |];
  Pack.pack pb b d ents;
  Copy.copy_at pk 0sz sa 16sz;
  Copy.copy_at pk 16sz pb pmb;
  with vpk. assert (A.pts_to pk vpk);
  append2_eq vsa (F.pack_n p vb) vpk;
  assert (pure (vpk == Seq.append vsa (F.pack_n p vb)));

  let mut stb = [| (S8.zero <: S8.t); smb |];
  Mat.to_bytes stb st ents #nbar #(n p);
  let mut pkh = [| (S8.zero <: S8.t); cb |];
  shake_p p pkh cb pk pkb;
  with vstb. assert (A.pts_to stb vstb);
  with vpkh. assert (A.pts_to pkh vpkh);
  assert (pure (vstb == M.to_bytes nbar (n p) vst));
  assert (pure (vpkh == shake p vpk (crypto_bytes p)));
  Copy.copy_range sk 0sz coins 0sz cb;
  Copy.copy_at sk cb pk pkb;
  Copy.copy_at sk (SZ.add cb pkb) stb smb;
  Copy.copy_at sk (SZ.add (SZ.add cb pkb) smb) pkh cb;
  with vsk. assert (A.pts_to sk vsk);
  slice_eq vcoins 0 (Seq.slice vcoins 0 (crypto_bytes p));
  append4_eq (Seq.slice vcoins 0 (crypto_bytes p)) vpk vstb vpkh vsk;
  assert (pure (vsk == Seq.append (Seq.slice vcoins 0 (crypto_bytes p))
                         (Seq.append vpk (Seq.append vstb vpkh))));
  keypair_eq p vcoins vpk vsk;
  assert (pure (vpk == fst (F.keypair p vcoins) /\ vsk == snd (F.keypair p vcoins)));
}


(** Encapsulation's public half, spelled out.  Unlike [keypair_eq] this
    one names every intermediate, because the Pulse function proves them
    one at a time and asking the solver to fold them back into a single
    nested term is what runs out of rlimit. *)
let enc_ct_eq (p: params)
              (mu: Seq.lseq S8.t (bytes_mu p))
              (pk: Seq.lseq S8.t (crypto_publickeybytes p))
              (seed_se: Seq.lseq S8.t (crypto_bytes p))
              (vct: Seq.lseq S8.t (crypto_ciphertextbytes p))
              (vbp: M.matrix nbar (n p)) (vv: M.matrix nbar nbar)
              (seed_a: Seq.lseq S8.t bytes_seed_a)
              (r: Seq.lseq S8.t (2 * secretmatrixbytes p + 2 * (nbar * nbar)))
              (sp: M.matrix nbar (n p)) (ep: M.matrix nbar (n p))
              (epp: M.matrix nbar nbar) (bm: M.matrix (n p) nbar)
              (bpu: M.matrix nbar (n p)) (vu: M.matrix nbar nbar)
  : Lemma
      (requires
        (let smb = secretmatrixbytes p in
         seed_a == Seq.slice pk 0 bytes_seed_a /\
         r == shake p (Seq.cons (S8.classify 0x96uy) seed_se)
                    (2 * smb + 2 * (nbar * nbar)) /\
         sp == F.sample_matrix p nbar (n p) (Seq.slice r 0 smb) /\
         ep == F.sample_matrix p nbar (n p) (Seq.slice r smb (2 * smb)) /\
         epp == F.sample_matrix p nbar nbar
                  (Seq.slice r (2 * smb) (2 * smb + 2 * (nbar * nbar))) /\
         bm == F.unpack_n p (Seq.slice pk bytes_seed_a (crypto_publickeybytes p)) /\
         bpu == M.add nbar (n p)
                  (M.mul nbar (n p) (n p) sp (F.gen_matrix p seed_a)) ep /\
         vu == M.add nbar nbar
                 (M.add nbar nbar (M.mul nbar (n p) nbar sp bm) epp)
                 (F.key_encode p mu) /\
         vct == Seq.append (F.pack_n p bpu) (F.pack_8 p vu) /\
         vbp == M.mod_pow2 nbar (n p) p.logq bpu /\
         vv == M.mod_pow2 nbar nbar p.logq vu))
      (ensures (let ct, b2, v2 = F.enc_ct p mu pk seed_se in
                vct == ct /\ vbp == b2 /\ vv == v2))
  = ()
(* A fresh solver context: the queries for [keypair_coins] above leave the
   solver slow enough that the ones here time out. *)
#push-options "--z3refresh"

(** The ciphertext, and the two matrices that went into it reduced to
    [logq] bits.  Decapsulation re-runs this and compares those two against
    what it received, which is why they are returned rather than dropped. *)
fn enc_ct ([@@@FStar.Attributes.monomorphize] p: params)
          (cdf: A.array U16.t) (ct: A.array S8.t) (bp: A.array S16.t) (v: A.array S16.t)
          (mu: A.array S8.t) (pk: A.array S8.t) (seed_se: A.array S8.t)
          (#pcd: perm) (#pmu: perm) (#ppk: perm) (#pss: perm)
          (#vcdf: erased (Seq.lseq U16.t (cdf_len p)))
          (#vct0: erased (Seq.lseq S8.t (crypto_ciphertextbytes p)))
          (#vbp0: erased (Seq.lseq S16.t (nbar * n p)))
          (#vv0: erased (Seq.lseq S16.t (nbar * nbar)))
          (#vmu: erased (Seq.lseq S8.t (bytes_mu p)))
          (#vpk: erased (Seq.lseq S8.t (crypto_publickeybytes p)))
          (#vss: erased (Seq.lseq S8.t (crypto_bytes p)))
requires A.pts_to cdf #pcd vcdf ** A.pts_to ct vct0 ** A.pts_to bp vbp0 **
         A.pts_to v vv0 ** A.pts_to mu #pmu vmu ** A.pts_to pk #ppk vpk **
         A.pts_to seed_se #pss vss ** pure (reveal vcdf == reveal p.cdf)
ensures exists* vct vbp vv.
        A.pts_to cdf #pcd vcdf ** A.pts_to ct vct ** A.pts_to bp vbp **
        A.pts_to v vv ** A.pts_to mu #pmu vmu ** A.pts_to pk #ppk vpk **
        A.pts_to seed_se #pss vss **
        pure (Seq.length vbp == nbar * n p /\ Seq.length vv == nbar * nbar /\
              (let c, b2, v2 = F.enc_ct p vmu vpk vss in
               vct == c /\ vbp == b2 /\ vv == v2))
{
  A.pts_to_len cdf;
  A.pts_to_len ct;
  A.pts_to_len bp;
  A.pts_to_len v;
  A.pts_to_len mu;
  A.pts_to_len pk;
  A.pts_to_len seed_se;
  Hacl.SizeT.fits32 ();
  let cb = p.cbytes;
  let nn = p.nn;
  let d = SZ.uint32_to_sizet p.logq;
  let ents = SZ.mul 8sz nn;
  let smb = SZ.mul 2sz ents;
  let pmb = SZ.mul d nn;
  let pkb = SZ.add 16sz pmb;
  let two_smb = SZ.mul 2sz smb;
  let rlen = SZ.add two_smb 128sz;
  let c2 = SZ.mul d 8sz;
  assert_norm (16 * 1344 < pow2 32);
  assert (pure (SZ.v ents == nbar * n p /\ SZ.v smb == secretmatrixbytes p /\
                SZ.v pmb == publicmatrixbytes p /\
                SZ.v pkb == crypto_publickeybytes p /\
                SZ.v c2 == ct2bytes p /\
                SZ.v rlen == 2 * secretmatrixbytes p + 2 * (nbar * nbar) /\
                SZ.v rlen < pow2 32));

  let mut sa = [| (S8.zero <: S8.t); 16sz |];
  Copy.copy_range sa 0sz pk 0sz 16sz;
  A.pts_to_len sa;
  with vsa. assert (A.pts_to sa vsa);
  slice_eq vpk 0 vsa;
  assert (pure (vsa == Seq.slice vpk 0 bytes_seed_a));

  let mut bb = [| (S8.zero <: S8.t); pmb |];
  Copy.copy_range bb 0sz pk 16sz pmb;
  A.pts_to_len bb;
  with vbb. assert (A.pts_to bb vbb);
  slice_eq vpk 16 vbb;
  assert (pure (vbb == Seq.slice vpk bytes_seed_a (crypto_publickeybytes p)));
  (* [unpack] takes its byte buffer at the indexed length
     [d * (len / 8)]; spell that out for [vbb]. *)
  assert (pure (SZ.v ents % 8 == 0 /\ SZ.v ents / 8 == SZ.v nn));
  assert (pure (Seq.length vbb == SZ.v pmb));
  assert (pure (Seq.length vbb == SZ.v d * (SZ.v ents / 8)));
  let mut bm = [| (S16.zero <: S16.t); ents |];
  Seq.lemma_create_len (SZ.v ents) (S16.zero <: S16.t);
  assert (pure (SZ.v d <= 16 /\ SZ.v ents <= 8 * 1344));
  Math.lemma_mult_le_right (SZ.v ents) (SZ.v d) 16;
  Math.lemma_mult_le_left 16 (SZ.v ents) (8 * 1344);
  assert_norm (16 * (8 * 1344) < pow2 32);
  assert (pure (SZ.v d * SZ.v ents < pow2 32));
  Pack.unpack bm bb d ents;
  with vbm. assert (A.pts_to bm vbm);
  assert (pure (vbm == F.unpack_n p vbb));

  let mut mbuf = [| (S8.zero <: S8.t); SZ.add 1sz cb |];
  A.((mbuf.(0sz) <- S8.classify 0x96uy));
  Copy.copy_range mbuf 1sz seed_se 0sz cb;
  with vmbuf. assert (A.pts_to mbuf vmbuf);
  cons_eq (S8.classify 0x96uy) vss vmbuf;

  let mut r = [| (S8.zero <: S8.t); rlen |];
  shake_p p r rlen mbuf (SZ.add 1sz cb);
  with vr. assert (A.pts_to r vr);
  assert (pure (vr == shake p (Seq.cons (S8.classify 0x96uy) vss)
                            (2 * secretmatrixbytes p + 2 * (nbar * nbar))));
  slice_eq vr 0 (Seq.slice vr 0 (secretmatrixbytes p));
  slice_eq vr (secretmatrixbytes p)
           (Seq.slice vr (secretmatrixbytes p) (2 * secretmatrixbytes p));
  slice_eq vr (2 * secretmatrixbytes p)
           (Seq.slice vr (2 * secretmatrixbytes p)
                         (2 * secretmatrixbytes p + 2 * (nbar * nbar)));

  let mut sp = [| (S16.zero <: S16.t); ents |];
  let mut ep = [| (S16.zero <: S16.t); ents |];
  let mut epp = [| (S16.zero <: S16.t); 64sz |];
  (* [sample_matrix] takes its byte buffer at the indexed length [blen] and
     slices three disjoint windows out of it. *)
  A.pts_to_len r;
  Seq.lemma_create_len (SZ.v ents) (S16.zero <: S16.t);
  Seq.lemma_create_len 64 (S16.zero <: S16.t);
  assert (pure (Seq.length vr == SZ.v rlen /\
                SZ.v smb == 2 * (8 * SZ.v nn) /\
                SZ.v two_smb == 2 * SZ.v smb /\
                SZ.v rlen == 2 * SZ.v smb + 128));
  Seq.lemma_len_slice vr 0 (2 * (8 * SZ.v nn));
  Seq.lemma_len_slice vr (SZ.v smb) (SZ.v smb + 2 * (8 * SZ.v nn));
  Seq.lemma_len_slice vr (SZ.v two_smb) (SZ.v two_smb + 2 * (8 * 8));
  Sample.sample_matrix p cdf sp r 8sz nn rlen 0sz;
  Sample.sample_matrix p cdf ep r 8sz nn rlen smb;
  Sample.sample_matrix p cdf epp r 8sz 8sz rlen two_smb;
  with vsp. assert (A.pts_to sp vsp);
  with vep. assert (A.pts_to ep vep);
  with vepp. assert (A.pts_to epp vepp);
  assert (pure (vsp == F.sample_matrix p nbar (n p)
                         (Seq.slice vr 0 (secretmatrixbytes p))));
  assert (pure (vep == F.sample_matrix p nbar (n p)
                         (Seq.slice vr (secretmatrixbytes p)
                                       (2 * secretmatrixbytes p))));
  assert (pure (vepp == F.sample_matrix p nbar nbar
                          (Seq.slice vr (2 * secretmatrixbytes p)
                                        (2 * secretmatrixbytes p + 2 * (nbar * nbar)))));

  Gen.mul_sa p sa sp bp;
  Mat.add bp ep ents #nbar #(n p);
  with vbpu. assert (A.pts_to bp vbpu);
  assert (pure (vbpu == M.add nbar (n p)
                          (M.mul nbar (n p) (n p) vsp (F.gen_matrix p vsa)) vep));

  Mat.mul v sp bm 8sz nn 8sz;
  Mat.add v epp 64sz #nbar #nbar;
  let mut enc = [| (S16.zero <: S16.t); 64sz |];
  Encode.key_encode p enc mu;
  Mat.add v enc 64sz #nbar #nbar;
  with vvu. assert (A.pts_to v vvu);
  assert (pure (vvu == M.add nbar nbar
                         (M.add nbar nbar (M.mul nbar (n p) nbar vsp vbm) vepp)
                         (F.key_encode p vmu)));

  let mut c1b = [| (S8.zero <: S8.t); pmb |];
  let mut c2b = [| (S8.zero <: S8.t); c2 |];
  Pack.pack c1b bp d ents;
  Pack.pack c2b v d 64sz;
  A.pts_to_len c1b;
  A.pts_to_len c2b;
  Copy.copy_at ct 0sz c1b pmb;
  Copy.copy_at ct pmb c2b c2;
  with vct. assert (A.pts_to ct vct);
  append2_eq (F.pack_n p vbpu) (F.pack_8 p vvu) vct;
  assert (pure (vct == Seq.append (F.pack_n p vbpu) (F.pack_8 p vvu)));

  Mat.mod_pow2 bp ents p.logq #nbar #(n p);
  Mat.mod_pow2 v 64sz p.logq #nbar #nbar;
  with vbp. assert (A.pts_to bp vbp);
  with vv. assert (A.pts_to v vv);
  assert (pure (vbp == M.mod_pow2 nbar (n p) p.logq vbpu));
  assert (pure (vv == M.mod_pow2 nbar nbar p.logq vvu));
  enc_ct_eq p vmu vpk vss vct vbp vv vsa vr vsp vep vepp vbm vbpu vvu;
  assert (pure (let c, b2, v2 = F.enc_ct p vmu vpk vss in
                vct == c /\ vbp == b2 /\ vv == v2));
}


(** {2 Encapsulation} *)
#pop-options


(** Encapsulation from an explicit message.  The API draws [mu] at random;
    decapsulation supplies the message it recovered. *)
fn enc_mu ([@@@FStar.Attributes.monomorphize] p: params)
          (cdf: A.array U16.t) (ct: A.array S8.t) (ss: A.array S8.t)
          (mu: A.array S8.t) (pk: A.array S8.t)
          (#pcd: perm) (#pmu: perm) (#ppk: perm)
          (#vcdf: erased (Seq.lseq U16.t (cdf_len p)))
          (#vct0: erased (Seq.lseq S8.t (crypto_ciphertextbytes p)))
          (#vss0: erased (Seq.lseq S8.t (crypto_bytes p)))
          (#vmu: erased (Seq.lseq S8.t (bytes_mu p)))
          (#vpk: erased (Seq.lseq S8.t (crypto_publickeybytes p)))
requires A.pts_to cdf #pcd vcdf ** A.pts_to ct vct0 ** A.pts_to ss vss0 **
         A.pts_to mu #pmu vmu ** A.pts_to pk #ppk vpk **
         pure (reveal vcdf == reveal p.cdf)
ensures exists* vct vss.
        A.pts_to cdf #pcd vcdf ** A.pts_to ct vct ** A.pts_to ss vss **
        A.pts_to mu #pmu vmu ** A.pts_to pk #ppk vpk **
        pure (vct == fst (F.enc p vmu vpk) /\ vss == snd (F.enc p vmu vpk))
{
  A.pts_to_len cdf;
  A.pts_to_len ct;
  A.pts_to_len ss;
  A.pts_to_len mu;
  A.pts_to_len pk;
  Hacl.SizeT.fits32 ();
  let cb = p.cbytes;
  let nn = p.nn;
  let d = SZ.uint32_to_sizet p.logq;
  let ents = SZ.mul 8sz nn;
  let pmb = SZ.mul d nn;
  let pkb = SZ.add 16sz pmb;
  let mub = SZ.mul (SZ.uint32_to_sizet p.bits) 8sz;
  let ctb = SZ.add pmb (SZ.mul d 8sz);
  let two_cb = SZ.mul 2sz cb;
  let kbl = SZ.add ctb cb;
  assert_norm (16 * 1344 < pow2 32);
  assert (pure (SZ.v ents == nbar * n p /\ SZ.v pkb == crypto_publickeybytes p /\
                SZ.v mub == bytes_mu p /\ SZ.v ctb == crypto_ciphertextbytes p /\
                SZ.v two_cb == SZ.v cb + SZ.v cb /\ SZ.v kbl == SZ.v ctb + SZ.v cb));

  let mut pkh = [| (S8.zero <: S8.t); cb |];
  shake_p p pkh cb pk pkb;
  A.pts_to_len pkh;
  with vpkh. assert (A.pts_to pkh vpkh);
  assert (pure (vpkh == shake p vpk (crypto_bytes p)));

  let mut hm = [| (S8.zero <: S8.t); SZ.add cb mub |];
  A.pts_to_len hm;
  Copy.copy_at hm 0sz pkh cb;
  Copy.copy_at hm cb mu mub;
  with vhm. assert (A.pts_to hm vhm);
  append2_eq vpkh vmu vhm;

  let mut sek = [| (S8.zero <: S8.t); two_cb |];
  shake_p p sek two_cb hm (SZ.add cb mub);
  A.pts_to_len sek;
  with vsek. assert (A.pts_to sek vsek);
  assert (pure (vsek == shake p (Seq.append vpkh vmu) (2 * crypto_bytes p)));

  let mut se = [| (S8.zero <: S8.t); cb |];
  A.pts_to_len se;
  Copy.copy_range se 0sz sek 0sz cb;
  with vse. assert (A.pts_to se vse);
  slice_eq vsek 0 vse;

  let mut bp = [| (S16.zero <: S16.t); ents |];
  let mut vm = [| (S16.zero <: S16.t); 64sz |];
  enc_ct p cdf ct bp vm mu pk se;
  with vct. assert (A.pts_to ct vct);

  let mut kb = [| (S8.zero <: S8.t); kbl |];
  A.pts_to_len kb;
  Copy.copy_at kb 0sz ct ctb;
  A.pts_to_len kb;
  A.pts_to_len sek;
  Copy.copy_range kb ctb sek cb cb;
  with vkb. assert (A.pts_to kb vkb);
  slice_eq vsek (crypto_bytes p)
           (Seq.slice vsek (crypto_bytes p) (2 * crypto_bytes p));
  append2_eq vct (Seq.slice vsek (crypto_bytes p) (2 * crypto_bytes p)) vkb;
  shake_p p ss cb kb kbl;
  with vss. assert (A.pts_to ss vss);
  assert (pure (vct == fst (F.enc p vmu vpk) /\ vss == snd (F.enc p vmu vpk)));
}

(** {2 Decapsulation} *)

(** Prefix agreement between two matrices, as a ghost boolean. *)
let agree (va vb: Seq.seq S16.t) (i: nat) : GTot bool =
  SEM.strong_excluded_middle
    (forall (k: nat). k < i /\ k < Seq.length va /\ k < Seq.length vb ==>
       Seq.index va k == Seq.index vb k)

(** At full length, agreement is equality. *)
let eq_from_agree (va vb: Seq.seq S16.t)
  : Lemma (requires Seq.length va == Seq.length vb)
          (ensures (agree va vb (Seq.length va) <==> va == vb))
  = if agree va vb (Seq.length va) then Seq.lemma_eq_intro va vb

(** Whether two matrices agree, as a mask rather than as a [bool]: the
    comparison decides whether the real shared secret or the rejection
    value is returned, and which of those happened must not be observable
    from the outside.  Secret integers carry no decidable equality -- that
    is the point of them -- so the loop is stated with {!agree}. *)
fn eq_mask_arr (a: A.array S16.t) (b: A.array S16.t) (len: SZ.t)
               (#pa: perm) (#pb: perm)
               (#va: erased (Seq.seq S16.t)) (#vb: erased (Seq.seq S16.t))
requires A.pts_to a #pa va ** A.pts_to b #pb vb **
         pure (Seq.length va == SZ.v len /\ Seq.length vb == SZ.v len)
returns m: S16.t
ensures A.pts_to a #pa va ** A.pts_to b #pb vb **
        pure ((S16.v m == 0 \/ S16.v m == pow2 16 - 1) /\
              (S16.v m == pow2 16 - 1 <==> reveal va == reveal vb))
{
  A.pts_to_len a;
  A.pts_to_len b;
  let mut acc = S16.ones;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (vacc: S16.t).
    pts_to i vi ** pts_to acc vacc ** A.pts_to a #pa va ** A.pts_to b #pb vb **
    pure (SZ.v vi <= SZ.v len /\
          S16.v vacc == (if agree va vb (SZ.v vi) then pow2 16 - 1 else 0))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let vacc = !acc;
    let x = A.(a.(vi));
    let y = A.(b.(vi));
    let m = S16.eq_mask x y;
    UInt.logand_lemma_1 #16 (S16.v vacc);
    UInt.logand_lemma_2 #16 (S16.v vacc);
    UInt.logand_commutative #16 (S16.v vacc) (S16.v m);
    UInt.logand_lemma_1 #16 (S16.v m);
    UInt.logand_lemma_2 #16 (S16.v m);
    acc := S16.logand vacc m;
    i := SZ.add vi 1sz;
  };
  let r = !acc;
  eq_from_agree va vb;
  r
}

(** Copying a matrix; [Hacl.Impl.Copy] is about bytes.  Decapsulation needs
    one, because the received [c] is both subtracted from and compared. *)
fn copy16 (dst: A.array S16.t) (src: A.array S16.t) (len: SZ.t)
          (#ps: perm) (#vd: erased (Seq.seq S16.t)) (#vs: erased (Seq.seq S16.t))
requires A.pts_to dst vd ** A.pts_to src #ps vs **
         pure (Seq.length vd == SZ.v len /\ Seq.length vs == SZ.v len)
ensures exists* v. A.pts_to dst v ** A.pts_to src #ps vs ** pure (v == reveal vs)
{
  A.pts_to_len dst;
  A.pts_to_len src;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S16.t).
    pts_to i vi ** A.pts_to dst v ** A.pts_to src #ps vs **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==> Seq.index v k == Seq.index vs k))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let x = A.(src.(vi));
    A.((dst.(vi) <- x));
    i := SZ.add vi 1sz;
  };
  with v. assert (A.pts_to dst v);
  Seq.lemma_eq_intro v (reveal vs);
  assert (pure (v == reveal vs));
}

(** Writing [dst[dbase + k] <- select mask x[k] y[k]], for a mask that is
    all ones or all zeroes.  This is the implicit rejection: whether the
    real key or the rejection value came out must not be branched on. *)
fn select_copy (dst: A.array S8.t) (dbase: SZ.t) (x: A.array S8.t) (y: A.array S8.t)
               (len: SZ.t) (mask: S8.t { S8.v mask == 0 \/ S8.v mask == pow2 8 - 1 })
               (#px: perm) (#py: perm) (#vd: erased (Seq.seq S8.t))
               (#vx: erased (Seq.seq S8.t)) (#vy: erased (Seq.seq S8.t))
requires A.pts_to dst vd ** A.pts_to x #px vx ** A.pts_to y #py vy **
         pure (SZ.v dbase + SZ.v len <= Seq.length vd /\
               Seq.length vx == SZ.v len /\ Seq.length vy == SZ.v len)
ensures exists* v. A.pts_to dst v ** A.pts_to x #px vx ** A.pts_to y #py vy **
        pure (Seq.length v == Seq.length vd /\
              SZ.v dbase + SZ.v len <= Seq.length v /\
              Seq.length vx == SZ.v len /\ Seq.length vy == SZ.v len /\
              (forall (k: nat). k < SZ.v len ==>
                 Seq.index v (SZ.v dbase + k) ==
                   (if S8.v mask = 0 then Seq.index vy k else Seq.index vx k)) /\
              (forall (k: nat). k < Seq.length vd /\
                               (k < SZ.v dbase \/ SZ.v dbase + SZ.v len <= k) ==>
                 Seq.index v k == Seq.index vd k))
{
  A.pts_to_len dst;
  A.pts_to_len x;
  A.pts_to_len y;
  let mut i = 0sz;
  while (let vi = !i; SZ.lt vi len)
  invariant exists* (vi: SZ.t) (v: Seq.seq S8.t).
    pts_to i vi ** A.pts_to dst v ** A.pts_to x #px vx ** A.pts_to y #py vy **
    pure (SZ.v vi <= SZ.v len /\ Seq.length v == Seq.length vd /\
          SZ.v dbase + SZ.v len <= Seq.length v /\
          Seq.length vx == SZ.v len /\ Seq.length vy == SZ.v len /\
          (forall (k: nat). k < SZ.v vi ==>
             Seq.index v (SZ.v dbase + k) ==
               (if S8.v mask = 0 then Seq.index vy k else Seq.index vx k)) /\
          (forall (k: nat). k < Seq.length vd /\
                           (k < SZ.v dbase \/ SZ.v dbase + SZ.v vi <= k) ==>
             Seq.index v k == Seq.index vd k))
  decreases (SZ.v len - SZ.v (!i))
  {
    let vi = !i;
    let a = A.(x.(vi));
    let b = A.(y.(vi));
    A.((dst.(SZ.add dbase vi) <- S8.select mask a b));
    i := SZ.add vi 1sz;
  };
}

(** Whether the re-encryption matched.  This is a ghost boolean: the
    implementation only ever has the mask. *)
let okb (p: params) (vbpr vbp2: M.matrix nbar (n p)) (vcr vv2: M.matrix nbar nbar)
  : GTot bool
  = SEM.strong_excluded_middle (Seq.equal vbpr vbp2 /\ Seq.equal vcr vv2)

(** The two comparisons, combined and narrowed to a byte.  All of it is
    bit-level reasoning about two values that are each all ones or all
    zeroes, and none of it has anything to do with the heap, so it is a
    pure lemma: inside [dec] the context is far too large for the solver
    to get through it. *)
let mask_ok (p: params) (a b: M.matrix nbar (n p)) (c e: M.matrix nbar nbar)
            (m1 m2 m16: S16.t) (mask: S8.t)
  : Lemma
      (requires (S16.v m1 == 0 \/ S16.v m1 == pow2 16 - 1) /\
                (S16.v m1 == pow2 16 - 1 <==> a == b) /\
                (S16.v m2 == 0 \/ S16.v m2 == pow2 16 - 1) /\
                (S16.v m2 == pow2 16 - 1 <==> c == e) /\
                S16.v m16 == UInt.logand #16 (S16.v m1) (S16.v m2) /\
                S8.v mask == S16.v m16 % pow2 8)
      (ensures (S8.v mask == 0 \/ S8.v mask == pow2 8 - 1) /\
               (S8.v mask == pow2 8 - 1 <==> okb p a b c e))
  = UInt.logand_lemma_1 #16 (S16.v m1);
    UInt.logand_lemma_2 #16 (S16.v m1);
    UInt.logand_commutative #16 (S16.v m1) (S16.v m2);
    UInt.logand_lemma_1 #16 (S16.v m2);
    UInt.logand_lemma_2 #16 (S16.v m2);
    assert_norm (pow2 16 - 1 == 65535);
    assert_norm (pow2 8 - 1 == 255);
    assert_norm (65535 % pow2 8 == 255);
    assert_norm (0 % pow2 8 == 0)

(** The pre-image of the final hash: the ciphertext, then either the real
    key stream or the rejection value, chosen by a mask that the caller has
    related to [ok].  Pure, for the same reason {!mask_ok} is. *)
let kb_eq (ok: bool) (mask: S8.t) (ctv x y res: Seq.seq S8.t)
  : Lemma
      (requires (S8.v mask == 0 \/ S8.v mask == pow2 8 - 1) /\
                (S8.v mask == pow2 8 - 1 <==> ok) /\
                Seq.length x == Seq.length y /\
                Seq.length res == Seq.length ctv + Seq.length x /\
                (forall (k: nat). k < Seq.length ctv ==>
                   Seq.index res k == Seq.index ctv k) /\
                (forall (k: nat). k < Seq.length x ==>
                   Seq.index res (Seq.length ctv + k) ==
                     (if S8.v mask = 0 then Seq.index y k else Seq.index x k)))
      (ensures res == Seq.append ctv (if ok then x else y))
  = assert_norm (pow2 8 - 1 == 255);
    if ok then Seq.lemma_eq_intro res (Seq.append ctv x)
    else Seq.lemma_eq_intro res (Seq.append ctv y)

(** Decapsulation, spelled out; the same idiom as [enc_ct_eq]. *)
let dec_eq (p: params)
           (vct: Seq.lseq S8.t (crypto_ciphertextbytes p))
           (vsk: Seq.lseq S8.t (crypto_secretkeybytes p))
           (vs: Seq.lseq S8.t (crypto_bytes p))
           (vpk: Seq.lseq S8.t (crypto_publickeybytes p))
           (vsbytes: Seq.lseq S8.t (secretmatrixbytes p))
           (vpkh: Seq.lseq S8.t (crypto_bytes p))
           (vbpm: M.matrix nbar (n p)) (vcm: M.matrix nbar nbar)
           (vst: M.matrix nbar (n p)) (vprod: M.matrix nbar nbar)
           (vmdiff: M.matrix nbar nbar)
           (vmu: Seq.lseq S8.t (bytes_mu p))
           (vsek: Seq.lseq S8.t (2 * crypto_bytes p))
           (vse: Seq.lseq S8.t (crypto_bytes p))
           (vct2: Seq.lseq S8.t (crypto_ciphertextbytes p))
           (vbp2: M.matrix nbar (n p)) (vv2: M.matrix nbar nbar)
           (vbpr: M.matrix nbar (n p)) (vcr: M.matrix nbar nbar)
           (vkb: Seq.lseq S8.t (crypto_ciphertextbytes p + crypto_bytes p))
           (vss: Seq.lseq S8.t (crypto_bytes p))
  : Lemma
      (requires
        (let cb = crypto_bytes p in
         let pkb = crypto_publickeybytes p in
         let smb = secretmatrixbytes p in
         vs == Seq.slice vsk 0 cb /\
         vpk == Seq.slice vsk cb (cb + pkb) /\
         vsbytes == Seq.slice vsk (cb + pkb) (cb + pkb + smb) /\
         vpkh == Seq.slice vsk (cb + pkb + smb) (crypto_secretkeybytes p) /\
         vbpm == F.unpack_n p (Seq.slice vct 0 (ct1bytes p)) /\
         vcm == F.unpack_8 p (Seq.slice vct (ct1bytes p) (crypto_ciphertextbytes p)) /\
         vst == M.from_bytes nbar (n p) vsbytes /\
         vprod == M.mul_t nbar (n p) nbar vbpm vst /\
         vmdiff == M.sub nbar nbar vcm vprod /\
         vmu == F.key_decode p vmdiff /\
         vsek == shake p (Seq.append vpkh vmu) (2 * cb) /\
         vse == Seq.slice vsek 0 cb /\
         (let c, b2, v2 = F.enc_ct p vmu vpk vse in
          vct2 == c /\ vbp2 == b2 /\ vv2 == v2) /\
         vbpr == M.mod_pow2 nbar (n p) p.logq vbpm /\
         vcr == M.mod_pow2 nbar nbar p.logq vcm /\
         vkb == Seq.append vct
                  (if okb p vbpr vbp2 vcr vv2
                   then Seq.slice vsek cb (2 * cb) else vs) /\
         vss == shake p vkb cb))
      (ensures vss == F.dec p vct vsk)
  = ()

(** Decapsulation.  Recover [mu] from the ciphertext with the secret
    matrix, re-run encapsulation on it, and return the real shared secret
    if -- and a pseudorandom function of the rejection value [s] if not --
    the result reproduces what was received. *)
fn dec ([@@@FStar.Attributes.monomorphize] p: params)
       (cdf: A.array U16.t) (ss: A.array S8.t)
       (ct: A.array S8.t) (sk: A.array S8.t)
       (#pcd: perm) (#pct: perm) (#psk: perm)
       (#vcdf: erased (Seq.lseq U16.t (cdf_len p)))
       (#vss0: erased (Seq.lseq S8.t (crypto_bytes p)))
       (#vct: erased (Seq.lseq S8.t (crypto_ciphertextbytes p)))
       (#vsk: erased (Seq.lseq S8.t (crypto_secretkeybytes p)))
requires A.pts_to cdf #pcd vcdf ** A.pts_to ss vss0 **
         A.pts_to ct #pct vct ** A.pts_to sk #psk vsk **
         pure (reveal vcdf == reveal p.cdf)
ensures exists* vss.
        A.pts_to cdf #pcd vcdf ** A.pts_to ss vss **
        A.pts_to ct #pct vct ** A.pts_to sk #psk vsk **
        pure (vss == F.dec p vct vsk)
{
  A.pts_to_len cdf;
  A.pts_to_len ss;
  A.pts_to_len ct;
  A.pts_to_len sk;
  Hacl.SizeT.fits32 ();
  let cb = p.cbytes;
  let nn = p.nn;
  let d = SZ.uint32_to_sizet p.logq;
  let ents = SZ.mul 8sz nn;
  let smb = SZ.mul 2sz ents;
  let pmb = SZ.mul d nn;
  let pkb = SZ.add 16sz pmb;
  let c2 = SZ.mul d 8sz;
  let ctb = SZ.add pmb c2;
  let mub = SZ.mul (SZ.uint32_to_sizet p.bits) 8sz;
  let two_cb = SZ.mul 2sz cb;
  let hml = SZ.add cb mub;
  let kbl = SZ.add ctb cb;
  let off1 = SZ.add cb pkb;
  let off2 = SZ.add off1 smb;
  assert_norm (16 * 1344 < pow2 32);
  assert (pure (SZ.v ents == nbar * n p /\ SZ.v smb == secretmatrixbytes p /\
                SZ.v pmb == ct1bytes p /\ SZ.v c2 == ct2bytes p /\
                SZ.v pkb == crypto_publickeybytes p /\
                SZ.v ctb == crypto_ciphertextbytes p /\
                SZ.v mub == bytes_mu p /\
                SZ.v two_cb == SZ.v cb + SZ.v cb /\
                SZ.v hml == SZ.v cb + SZ.v mub /\
                SZ.v kbl == SZ.v ctb + SZ.v cb /\
                SZ.v off1 == SZ.v cb + SZ.v pkb /\
                SZ.v off2 == SZ.v cb + SZ.v pkb + SZ.v smb /\
                SZ.v off2 + SZ.v cb == crypto_secretkeybytes p /\
                SZ.fits (2 * SZ.v ents) /\ SZ.v d * SZ.v ents < pow2 32 /\
                SZ.v d * 64 < pow2 32 /\ SZ.v ents % 8 == 0 /\
                SZ.v ents / 8 == SZ.v nn /\
                SZ.v d * (SZ.v ents / 8) == SZ.v pmb /\
                SZ.v d * (64 / 8) == SZ.v c2));

  (* The four pieces of the secret key. *)
  let mut sv = [| (S8.zero <: S8.t); cb |];
  A.pts_to_len sv;
  let mut pkv = [| (S8.zero <: S8.t); pkb |];
  A.pts_to_len pkv;
  let mut sbytes = [| (S8.zero <: S8.t); smb |];
  A.pts_to_len sbytes;
  let mut pkh = [| (S8.zero <: S8.t); cb |];
  A.pts_to_len pkh;
  Copy.copy_range sv 0sz sk 0sz cb;
  Copy.copy_range pkv 0sz sk cb pkb;
  Copy.copy_range sbytes 0sz sk off1 smb;
  Copy.copy_range pkh 0sz sk off2 cb;
  with vs. assert (A.pts_to sv vs);
  with vpk. assert (A.pts_to pkv vpk);
  with vsb. assert (A.pts_to sbytes vsb);
  with vpkh. assert (A.pts_to pkh vpkh);
  slice_eq vsk 0 vs;
  slice_eq vsk (crypto_bytes p) vpk;
  slice_eq vsk (crypto_bytes p + crypto_publickeybytes p) vsb;
  slice_eq vsk (crypto_bytes p + crypto_publickeybytes p + secretmatrixbytes p) vpkh;
  assert (pure (vs == Seq.slice vsk 0 (crypto_bytes p) /\
                vpk == Seq.slice vsk (crypto_bytes p)
                                 (crypto_bytes p + crypto_publickeybytes p)));

  (* The two pieces of the ciphertext. *)
  let mut c1b = [| (S8.zero <: S8.t); pmb |];
  A.pts_to_len c1b;
  let mut c2b = [| (S8.zero <: S8.t); c2 |];
  A.pts_to_len c2b;
  Copy.copy_range c1b 0sz ct 0sz pmb;
  Copy.copy_range c2b 0sz ct pmb c2;
  with vc1. assert (A.pts_to c1b vc1);
  with vc2. assert (A.pts_to c2b vc2);
  slice_eq vct 0 vc1;
  slice_eq vct (ct1bytes p) vc2;

  let mut bpm = [| (S16.zero <: S16.t); ents |];
  A.pts_to_len bpm;
  let mut cm = [| (S16.zero <: S16.t); 64sz |];
  A.pts_to_len cm;
  Pack.unpack bpm c1b d ents;
  Pack.unpack cm c2b d 64sz;
  with vbpm. assert (A.pts_to bpm vbpm);
  with vcm. assert (A.pts_to cm vcm);
  assert (pure (vbpm == F.unpack_n p (Seq.slice vct 0 (ct1bytes p))));
  assert (pure (vcm == F.unpack_8 p
                  (Seq.slice vct (ct1bytes p) (crypto_ciphertextbytes p))));

  (* mu = key_decode (c - bp * S^T). *)
  let mut st = [| (S16.zero <: S16.t); ents |];
  A.pts_to_len st;
  Mat.from_bytes st sbytes ents #nbar #(n p);
  with vst. assert (A.pts_to st vst);
  let mut prod = [| (S16.zero <: S16.t); 64sz |];
  A.pts_to_len prod;
  Mat.mul_t prod bpm st 8sz nn 8sz;
  with vprod. assert (A.pts_to prod vprod);
  let mut mdiff = [| (S16.zero <: S16.t); 64sz |];
  A.pts_to_len mdiff;
  copy16 mdiff cm 64sz;
  Mat.sub mdiff prod 64sz #nbar #nbar;
  with vmdiff. assert (A.pts_to mdiff vmdiff);
  assert (pure (vmdiff == M.sub nbar nbar vcm vprod));
  let mut mu = [| (S8.zero <: S8.t); mub |];
  A.pts_to_len mu;
  Decode.key_decode p mu mdiff;
  with vmu. assert (A.pts_to mu vmu);

  (* Re-derive the encapsulation randomness from mu and re-encrypt. *)
  let mut hm = [| (S8.zero <: S8.t); hml |];
  A.pts_to_len hm;
  Copy.copy_at hm 0sz pkh cb;
  Copy.copy_at hm cb mu mub;
  with vhm. assert (A.pts_to hm vhm);
  append2_eq vpkh vmu vhm;

  let mut sek = [| (S8.zero <: S8.t); two_cb |];
  A.pts_to_len sek;
  shake_p p sek two_cb hm hml;
  with vsek. assert (A.pts_to sek vsek);
  assert (pure (vsek == shake p (Seq.append vpkh vmu) (2 * crypto_bytes p)));

  let mut se = [| (S8.zero <: S8.t); cb |];
  A.pts_to_len se;
  Copy.copy_range se 0sz sek 0sz cb;
  with vse. assert (A.pts_to se vse);
  slice_eq vsek 0 vse;

  let mut ct2 = [| (S8.zero <: S8.t); ctb |];
  A.pts_to_len ct2;
  let mut bp2 = [| (S16.zero <: S16.t); ents |];
  let mut v2 = [| (S16.zero <: S16.t); 64sz |];
  enc_ct p cdf ct2 bp2 v2 mu pkv se;
  with vct2. assert (A.pts_to ct2 vct2);
  with vbp2. assert (A.pts_to bp2 vbp2);
  with vv2. assert (A.pts_to v2 vv2);

  (* The comparison, as a mask. *)
  Mat.mod_pow2 bpm ents p.logq #nbar #(n p);
  Mat.mod_pow2 cm 64sz p.logq #nbar #nbar;
  with vbpr. assert (A.pts_to bpm vbpr);
  with vcr. assert (A.pts_to cm vcr);
  let m1 = eq_mask_arr bpm bp2 ents;
  let m2 = eq_mask_arr cm v2 64sz;
  let m16 = S16.logand m1 m2;
  let mask = Cast.u16_to_u8 m16;
  mask_ok p vbpr vbp2 vcr vv2 m1 m2 m16 mask;
  assert (pure ((S8.v mask == 0 \/ S8.v mask == pow2 8 - 1) /\
                (S8.v mask == pow2 8 - 1 <==> okb p vbpr vbp2 vcr vv2)));

  let mut kb = [| (S8.zero <: S8.t); kbl |];
  A.pts_to_len kb;
  Copy.copy_at kb 0sz ct ctb;
  A.pts_to_len kb;
  let mut sk2 = [| (S8.zero <: S8.t); cb |];
  A.pts_to_len sk2;
  Copy.copy_range sk2 0sz sek cb cb;
  with vk2. assert (A.pts_to sk2 vk2);
  slice_eq vsek (crypto_bytes p) vk2;
  select_copy kb ctb sk2 sv cb mask;
  with vkb. assert (A.pts_to kb vkb);
  kb_eq (okb p vbpr vbp2 vcr vv2) mask vct vk2 vs vkb;
  assert (pure (vkb == Seq.append vct
                  (if okb p vbpr vbp2 vcr vv2 then vk2 else vs)));
  shake_p p ss cb kb kbl;
  with vss. assert (A.pts_to ss vss);
  dec_eq p vct vsk vs vpk vsb vpkh vbpm vcm vst vprod vmdiff vmu vsek vse
         vct2 vbp2 vv2 vbpr vcr vkb vss;
  assert (pure (vss == F.dec p vct vsk));
}

#pop-options
