# Transcribes p384/nodes.txt (printed by p384/pocklington.gp) into
# Spec.P384.Primes, in the format of Spec.Group.{Primes,OrderPrimes}.
# Run from spec/group-gen: python3 p384/mkprimes.py
import os
HERE = os.path.dirname(os.path.abspath(__file__))
SPEC = os.path.join(HERE, '..', '..')
P = 2**384 - 2**128 - 2**96 + 2**32 - 1
N = 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973

LIC = open(os.path.join(SPEC, 'Spec.Group.OrderPrimes.fst')).read().split('*)')[0] + '*)\n\n'
out = [LIC + """(** Primality of the P-384 field prime and group order.

    Recursive Pocklington certificates in the format of
    {!Spec.Group.Primes}, produced by [spec/group-gen/p384/pocklington.gp]
    and checked by {!Spec.Group.Prime.pock_sound} and
    {!Spec.Group.Prime.trial_sound}: the computer-algebra system is not
    trusted, only its witnesses are used.  A certificate lists only as much
    of [N - 1] as Pocklington needs, a factored part [F] with [F^2 > N]. *)
module Spec.P384.Primes

open FStar.Math.Euclid
open Spec.Group.Prime

#set-options "--fuel 0 --ifuel 0"
"""]
idx = {}
for line in open(os.path.join(HERE, 'nodes.txt')).read().split('\n'):
    if not line.strip(): continue
    w = line.split()
    n = int(w[1])
    if n in idx: continue
    i = len(idx); idx[n] = i
    if w[0] == 'S':
        out.append(f"let pr_{i} () : Lemma (is_prime {n}) =\n  assert_norm (trial {n} 2); trial_sound {n}\n")
        continue
    es = [tuple(map(int, e.split(','))) for e in w[2:]]
    lit = lambda es: "[" + "; ".join(f"({q}, {a}, {u})" for q, a, u in es) + "]"
    k = len(es)
    body = [f"let pr_{i} () : Lemma (is_prime {n}) =", f"  let l{k} : list entry = [] in", "  all_prime_nil ();"]
    for j in range(k - 1, -1, -1):
        q, a, u = es[j]
        body.append(f"  let l{j} : list entry = ({q}, {a}, {u}) :: l{j+1} in")
        body.append(f"  pr_{idx[q]} (); all_prime_cons {q} {a} {u} l{j+1};")
    body.append(f"  assert_norm (pock {n} {lit(es)});")
    body.append(f"  assert (l0 == {lit(es)});")
    body.append(f"  pock_sound {n} l0\n")
    out.append("\n".join(body))
out.append(f"let prime_p384 () : Lemma (is_prime (pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1)) =\n"
           f"  pr_{idx[P]} (); assert_norm (pow2 384 - pow2 128 - pow2 96 + pow2 32 - 1 == {P})\n")
if N in idx:
    out.append(f"let prime_p384_order () : Lemma (is_prime {N}) = pr_{idx[N]} ()\n")
open(os.path.join(SPEC, 'Spec.P384.Primes.fst'), 'w').write("\n".join(out))
