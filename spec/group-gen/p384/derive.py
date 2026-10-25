# Derives the P-384 group-law inputs from the P-256 ones.  The formulas
# (RCB Algorithms 4 and 6 for a = -3) and the Singular cofactors in
# p256/cof.txt are the same for every a = -3 curve, with b kept symbolic;
# only p, b and the PARI/GP no-roots certificates (p384/nr.txt, from
# ../cas/p384-noroots.gp) change.
#
# Run from spec/group-gen: python3 p384/derive.py
# It writes Spec.P384.GroupSv, Spec.P384.GroupNR and p384/{checks,assoc1,2,3}.py;
# then run p256/gen.py on the latter (see ../README.md).
import os, re, sys
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
GG = os.path.join(HERE, '..')
SPEC = os.path.join(GG, '..')
sys.path.insert(0, os.path.join(GG, 'p256'))

p = 2**384 - 2**128 - 2**96 + 2**32 - 1
b = 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
P256M = "0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
P256B = "0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"

def rd(f): return open(os.path.join(GG, f)).read()
def wr(path, s):
    open(path, 'w').write(s)

def rename(s):
    return s.replace("Spec.P256", "Spec.P384").replace("P-256", "P-384")

# GroupSv: everything but the modulus, b and the primality lemma is generic.
sv = rename(open(os.path.join(SPEC, 'Spec.P256.GroupSv.fst')).read())
assert P256M in sv and P256B in sv
sv = sv.replace(P256M, hex(p)).replace(P256B, hex(b))
sv = sv.replace("Spec.Group.Primes.prime_p256 ()", "Spec.P384.Primes.prime_p384 ()")
wr(os.path.join(SPEC, 'Spec.P384.GroupSv.fst'), sv)

# GroupNR: the template, with the P-384 constants.
ns = {}
exec(open(os.path.join(HERE, 'nr.txt')).read(), ns)
c3 = 20*b % p; c1 = 12*b % p; c0 = (27 - 8*b*b) % p
s = rename(rd('NR.tmpl'))
s = s.replace('%C3%', str(c3)).replace('%C1%', str(c1)).replace('%C0%', str(c0))
s = s.replace('%UF%', '; '.join(map(str, ns['uf']))).replace('%UQ%', '; '.join(map(str, ns['uq'])))
wr(os.path.join(SPEC, 'Spec.P384.GroupNR.fst'), s)

# The check lists: same identities, cofactors reduced modulo the P-384 prime.
import cof
cof.p = p
lines = [l for l in open(os.path.join(GG, 'p256', 'cof.txt')).read().split("\n")
         if l.strip() and not l.startswith("//") and "sizes" not in l and "G:" not in l]
cofs = [f"let cof{i+1} : list (nat & list nat) = {cof.fst(cof.tolist(l, [cof.x1, cof.y1, cof.x2, cof.y2], b))}"
        for i, l in enumerate(lines[:3])]
ck = rd('p256/checks.py')
m = re.search(r"pre=\[('let cof1.*?)\],\n", ck)
ck = ck[:m.start(1)] + ", ".join(repr(c) for c in cofs) + ck[m.end(1):]
# With 384-bit cofactors the solver no longer sees unaided that k2's
# combination of three zeros is zero; lin0 says so.
LIN0 = """(** A combination of three zeros is zero. *)
let lin0 (c: ctx { c.m == m0 }) (a1 a2 a3 r1 r2 r3: sv c)
  : Lemma (requires ok c /\\ c.o == o /\\ tof (vl r1) == 0 /\\ tof (vl r2) == 0 /\\ tof (vl r3) == 0)
          (ensures tof (vl (sadd (sadd (smul a1 r1) (smul a2 r2)) (smul a3 r3))) == 0)
  = m0_lem (); o_eqs ();
    let z (a r: sv c) : Lemma (requires tof (vl r) == 0) (ensures tof (vl (smul a r)) == 0) =
      assert (tof (vl (smul a r)) == P.fmul (tof (vl a)) (tof (vl r)));
      Spec.ModArith.mul_zero #P.prime (tof (vl a))
    in
    z a1 r1; z a2 r2; z a3 r3"""
k2p = 'f"eqn_val c (a, {V(1)}, e)"]'
assert ck.count(k2p) == 1
ck = ck.replace(k2p, 'f"eqn_val c (a, {V(1)}, e)", "FStar.Classical.move_requires (lin0 c (spoly cof1) (spoly cof2) (spoly cof3) rx ry) rz"]')
ck = ck.replace("pre=['let cof1", "pre=[" + repr(LIN0) + ", 'let cof1", 1)
hdr = 'CURVE="P384"\nCNAME="P-384"\n'
wr(os.path.join(HERE, 'checks.py'), hdr + ck.replace('Spec.P256.GroupChecks', 'Spec.P384.GroupChecks'))
for i in (1, 2, 3):
    a = rd(f'p256/assoc{i}.py').replace(f'Spec.P256.GroupAssoc{i}', f'Spec.P384.GroupAssoc{i}')
    assert 'P256' not in a
    wr(os.path.join(HERE, f'assoc{i}.py'), hdr + a)
