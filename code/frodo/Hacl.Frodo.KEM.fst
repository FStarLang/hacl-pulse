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
module Gen = Hacl.Frodo.Gen

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
  = Seq.lemma_eq_intro res (Seq.append a (Seq.append b (Seq.append c d)))

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

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

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

#push-options "--z3rlimit 400 --fuel 1 --ifuel 1"

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
  let mut bm = [| (S16.zero <: S16.t); ents |];
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

#pop-options
