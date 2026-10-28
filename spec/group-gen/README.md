# Generators for the group-law proofs

These scripts and computer-algebra inputs generated the machine-produced
modules behind `Spec.{P256,P384,K256,Ed25519}.Group.fst`. **Do not edit the
generated `.fst` files by hand.** Change the generator instead and
regenerate. Every script below reproduces its committed module
byte-for-byte.

F* never trusts the CAS tools. Their output (polynomial cofactors, the
non-residues `uf`/`uq`, Pocklington witnesses) is just certificate data.
F* re-checks all of it with the verified polynomial normalizer in
`Spec.Group.{Poly,Check}`.

## Generated modules

| Module | Command (run from this directory) |
|---|---|
| `Spec.P256.GroupSv` | written by hand; it serves as the template for K256 |
| `Spec.K256.GroupSv` | `python3 k256/mksv.py` (derived from the P256 GroupSv and `Spec.K256.fst`) |
| `Spec.Ed25519.GroupSv` | `python3 ed25519/mksv.py` (from `ed25519/sv.tmpl`) |
| `Spec.P256.GroupNR` | `python3 genNR.py` (from `NR.tmpl`) |
| `Spec.K256.GroupNR` | `python3 k256/mknr.py` (derived from the P256 GroupNR) |
| `Spec.P256.GroupChecks` | `python3 p256/gen.py p256/checks.py ../Spec.P256.GroupChecks.fst` |
| `Spec.P256.GroupAssoc{1,2,3}` | `python3 p256/gen.py p256/assocN.py ../Spec.P256.GroupAssocN.fst` |
| `Spec.P256.JacChecks` | `python3 p256/gen.py p256/jac.py ../Spec.P256.JacChecks.fst` (Jacobian doubling and mixed addition; `Spec.P256.JacSv` is written by hand) |
| `Spec.K256.GroupChecks` | `python3 p256/gen.py k256/checks.py ../Spec.K256.GroupChecks.fst` |
| `Spec.K256.GroupAssoc{1,2,3}` | `python3 p256/gen.py k256/assocN.py ../Spec.K256.GroupAssocN.fst` |
| `Spec.P384.GroupSv`, `Spec.P384.GroupNR`, `p384/{checks,assoc1,2,3}.py` | `python3 p384/derive.py` (from the P-256 inputs, with `p384/nr.txt`) |
| `Spec.P384.GroupChecks` | `python3 p256/gen.py p384/checks.py ../Spec.P384.GroupChecks.fst` |
| `Spec.P384.GroupAssoc{1,2,3}` | `python3 p256/gen.py p384/assocN.py ../Spec.P384.GroupAssocN.fst` |
| `Spec.P384.JacChecks` | `python3 p256/gen.py p384/jac.py ../Spec.P384.JacChecks.fst` (Jacobian doubling and mixed addition; `Spec.P384.JacSv` is written by hand) |
| `Spec.P384.Primes` | `python3 p384/mkprimes.py` (from `p384/nodes.txt`) |
| `Spec.P256.Win{0..3}`, `Hacl.P256.Win{0..3}` | `python3 p256/wintables.py` (fixed-base tables for `G`; `Spec.P256.Base` is written by hand) |
| `Spec.P384.Base`, `Spec.P384.Win{0..5}`, `Hacl.P384.Win{0..5}` | `python3 p384/wintables.py` (fixed-base tables for `G`; F* re-checks every point) |
| `Spec.Ed25519.GroupChecks` | `python3 ed25519/gen.py ed25519/checks.py ../Spec.Ed25519.GroupChecks.fst` |
| `Spec.Ed25519.GroupAssoc{1,2}` | `python3 ed25519/gen.py ed25519/assocN.py ../Spec.Ed25519.GroupAssocN.fst` |
| `Spec.Ed25519.Comb{B,T0..7,Table}`, `Hacl.Ed25519.CombData{,0..7}` | `python3 ed25519/comb.py ../..` (the fixed-base comb's tables) |

`gen.py` executes the spec file it is given. That file sets `MOD`,
`CHECKS` and, optionally, `CURVE`/`BL`/`CNAME` and `OPENS` (extra
`open`s appended to the header). `gen.py` then emits one
lemma per polynomial identity, each discharged by the normalizer, plus
the wrapper lemmas that state the identity over the curve's field.
`hdr.txt` is the module header that gets prepended to the output.

All other modules are written by hand:
- the generic layers `Spec.Group.{Poly,Check,Field,Prime,Primes,Proj}`;
- the per-curve `Group.fst`.

## CAS inputs (`cas/`)

- `*-completeness.sing` (Singular): `lift` computations that produce the
  cofactors for the completeness identities, i.e. why the sum of two
  valid points has Z ≠ 0 or reaches the point at infinity only in the
  expected cases. `p256/cof.py` and `k256/cof.py` convert the Singular
  output (`cof.txt`) into the `spoly` coefficient lists used in
  `checks.py`. The Ed25519 certificate (d·W² − V² = k·(δ − ε) with
  k = δ + 2·u1v1·ι + ε) is encoded in the `add_z` checks of
  `ed25519/checks.py`.
- `*-noroots.gp` (PARI/GP): shows that the relevant cubic has no root in
  𝔽ₚ, and computes the polynomial data in `NR.tmpl` / `k256/mknr.py`.
  `gp -q cas/p384-noroots.gp > p384/nr.txt` writes the P-384 data.
- The P-256 completeness cofactors keep `b` symbolic, so `p256/cof.txt`
  also serves P-384, which shares `a = -3` and the formulas;
  `p384/derive.py` only reduces them modulo the P-384 prime.
- `*-assoc.sing`, `k256-formulas.py`, `p256/y3.py` (sympy): exploratory
  checks of the formulas and of associativity.

## Primality (`primes/`)

`pocklington.gp` builds recursive Pocklington certificates for
2²⁵⁵−19 and for the P-256 and secp256k1 primes. It prints them as
`nodes.txt`:
- `S n`: n is small and checked directly;
- `P n q,a,u ...`: for each factor q, a witness a and u = (a^((n−1)/q) − 1)⁻¹ mod n.

These nodes were transcribed into `Spec.Group.Primes.fst`, where
`Spec.Group.Prime` checks them.

`p384/pocklington.gp` does the same for the P-384 prime and group order,
printing `p384/nodes.txt`; `p384/mkprimes.py` turns that into
`Spec.P384.Primes.fst`.  PARI does not factor `n - 1` in reasonable time,
so the script supplies its two large prime factors via `addprimes`; the
90-bit one was found with GMP-ECM (`ecm -c 2000 1000000`), and PARI
re-proves both before using them.

## Tools

- `python3`; `sympy` is needed only for the exploratory scripts.
- Singular.
- PARI/GP.
- GMP-ECM, only to rediscover the factor of the P-384 `n - 1` noted above.
