#!/usr/bin/env python3
"""Generate the P-384 dedicated squaring (lemmas + Pulse) for Hacl.P384.Field64."""

M = (2**64 - 1) ** 2


def wk(k):
    return {0: "1", 1: "w"}.get(k, "w%d" % k)


def term(k, x):
    return x if k == 0 else "%s * %s" % (wk(k), x)


def cr(r):
    """Cumulative cross sum of rows 0..r, as a formula in the P's."""
    ts = [term(i + j, "p%d%d" % (i, j)) for i in range(r + 1) for j in range(i + 1, 6)]
    return " + ".join(ts)


def wsum(names):
    """names: dict pos -> name."""
    return " + ".join(term(k, names[k]) for k in sorted(names))


out = []
L = out.append

# ---------------------------------------------------------------- lemmas
for r in range(5):
    params = []
    req = []
    prods = [(i, j) for i in range(r + 1) for j in range(i + 1, 6)]
    params += ["p%d%d" % ij for ij in prods]
    req += ["p%d%d <= %d" % (i, j, M) for (i, j) in prods]
    js = list(range(r + 1, 6))
    params += ["l%d" % j for j in js] + ["h%d" % j for j in js]
    req += ["l%d < w /\\ h%d < w /\\ l%d + w * h%d == p%d%d" % (j, j, j, j, r, j) for j in js]
    old = {}
    if r >= 1:
        old = {k: "o%d" % k for k in range(1, r + 6)}
        params += [old[k] for k in sorted(old)]
        req += ["%s < w" % old[k] for k in sorted(old)]
        req += ["%s == %s" % (wsum(old), cr(r - 1))]
    new = {}
    eqs = []
    carries = []
    lo, top = 2 * r + 1, r + 6
    # q chain (row words) -- for r == 0 the row words are the new words
    q = {lo: "l%d" % (r + 1)}
    prev = "0"
    for k in range(lo + 1, top):
        qn, cn = "q%d" % k, "cq%d" % k
        params += [qn, cn]
        req += ["%s < w /\\ %s <= 1" % (qn, cn)]
        eqs.append("%s + w * %s == l%d + h%d + %s" % (qn, cn, k - r, k - r - 1, prev))
        q[k] = qn
        prev = cn
    qn, cn = "q%d" % top, "cq%d" % top
    params += [qn, cn]
    req += ["%s < w /\\ %s <= 1" % (qn, cn)]
    eqs.append("%s + w * %s == h5 + %s" % (qn, cn, prev))
    q[top] = qn
    if r == 0:
        new = q
    else:
        prev = "0"
        for k in range(lo, top):
            nn, cn = "n%d" % k, "ca%d" % k
            params += [nn, cn]
            req += ["%s < w /\\ %s <= 1" % (nn, cn)]
            eqs.append("%s + w * %s == %s + %s + %s" % (nn, cn, old[k], q[k], prev))
            new[k] = nn
            prev = cn
        nn, cn = "n%d" % top, "ca%d" % top
        params += [nn, cn]
        req += ["%s < w /\\ %s <= 1" % (nn, cn)]
        eqs.append("%s + w * %s == %s + %s" % (nn, cn, q[top], prev))
        new[top] = nn
    res = {k: old[k] for k in old if k < lo}
    res.update(new)
    L("let sqx%d (%s: nat)" % (r, " ".join(params)))
    L("  : Lemma (requires %s)" % " /\\\n                    ".join(req + eqs))
    L("          (ensures %s == %s)" % (wsum(res), cr(r)))
    L("  = ()")
    L("")

# diag lemma
params = ["p%d%d" % (i, j) for i in range(6) for j in range(i, 6)]
req = ["p%d%d <= %d" % (i, j, M) for i in range(6) for j in range(i, 6)]
params += ["t%d" % k for k in range(1, 11)]
req += ["t%d < w" % k for k in range(1, 11)]
req += ["%s == %s" % (wsum({k: "t%d" % k for k in range(1, 11)}), cr(4))]
params += ["d%d" % k for k in range(1, 11)] + ["e%d" % k for k in range(1, 11)]
req += ["d%d < w /\\ e%d <= 1" % (k, k) for k in range(1, 11)]
eqs = []
prev = "0"
for k in range(1, 11):
    eqs.append("d%d + w * e%d == t%d + t%d + %s" % (k, k, k, k, prev))
    prev = "e%d" % k
# d11 = e10
params += ["s%d" % i for i in range(6)] + ["g%d" % i for i in range(6)]
req += ["s%d < w /\\ g%d < w /\\ s%d + w * g%d == p%d%d" % (i, i, i, i, i, i) for i in range(6)]
dw = {}
for i in range(6):
    dw[2 * i] = "s%d" % i
    dw[2 * i + 1] = "g%d" % i
params += ["u%d" % k for k in range(1, 12)] + ["f%d" % k for k in range(1, 12)]
req += ["u%d < w /\\ f%d <= 1" % (k, k) for k in range(1, 12)]
prev = "0"
for k in range(1, 12):
    dk = "d%d" % k if k <= 10 else "e10"
    eqs.append("u%d + w * f%d == %s + %s + %s" % (k, k, dk, dw[k], prev))
    prev = "f%d" % k
res = {0: "s0"}
res.update({k: "u%d" % k for k in range(1, 12)})
diag = " + ".join(term(2 * i, "p%d%d" % (i, i)) for i in range(6))
L("let sqd (%s: nat)" % " ".join(params))
L("  : Lemma (requires %s)" % " /\\\n                    ".join(req + eqs))
L("          (ensures %s == %s + 2 * (%s))" % (wsum(res), diag, cr(4)))
L("  = ()")
L("")

# expansion
diag_a = " + ".join(term(2 * i, "(a%d * a%d)" % (i, i)) for i in range(6))
cross_a = " + ".join(term(i + j, "(a%d * a%d)" % (i, j)) for i in range(6) for j in range(i + 1, 6))
L("let sq_expand (a0 a1 a2 a3 a4 a5: int)")
L("  : Lemma (ev6 a0 a1 a2 a3 a4 a5 * ev6 a0 a1 a2 a3 a4 a5 ==")
L("           %s + 2 * (%s))" % (diag_a, cross_a))
L("  = assert (ev6 a0 a1 a2 a3 a4 a5 * ev6 a0 a1 a2 a3 a4 a5 ==")
L("           %s + 2 * (%s))" % (diag_a, cross_a))
L("      by (T.norm [delta_only [`%ev6; `%w; `%w2; `%w3; `%w4; `%w5; `%w6; `%w7; `%w8; `%w9; `%w10; `%w11]];")
L("          Canon.int_semiring ())")
L("")

LEMMAS = "\n".join(out)

# ---------------------------------------------------------------- Pulse
out = []
L = out.append
V = lambda x: "(S64.v %s)" % x


def mul(i, j, pre):
    L("  let m%s = S128.mul_wide a%d a%d;" % (pre, i, j))
    L("  let l%s = L.lo m%s;" % (pre, pre))
    L("  let h%s = L.hi m%s;" % (pre, pre))
    L("  L.lo_hi m%s;" % pre)
    L("  pbound (S64.v a%d) (S64.v a%d);" % (i, j))


def addc(c, s, cin, x, y):
    L("  let %s = K.addc %s %s %s r;" % (c, cin, x, y))
    L("  let %s = !r;" % s)


def P(i, j):
    return "(S64.v a%d * S64.v a%d)" % (i, j)


# cross
L('[@@ CInline; CPrologue "__attribute__((always_inline))"]')
L("fn sq_cross (t: A.array S64.t) (a0 a1 a2 a3 a4 a5: S64.t) (#vt: erased (Seq.seq S64.t))")
L("requires A.pts_to t vt ** pure (Seq.length vt == 12)")
L("ensures exists* (vt': Seq.seq S64.t).")
L("  A.pts_to t vt' **")
L("  ENSURES")
LINE_ENS = len(out) - 1
L("{")
L("  let z0 = S64.classify 0uL;")
L("  consts ();")
L("  let mut r = z0;")
cur = {}  # pos -> pulse name
for r in range(5):
    js = list(range(r + 1, 6))
    for j in js:
        mul(r, j, "%d%d" % (r, j))
    lo, top = 2 * r + 1, r + 6
    q = {lo: "l%d%d" % (r, r + 1)}
    qc = {}
    prev = "z0"
    for k in range(lo + 1, top):
        addc("cq%d_%d" % (r, k), "q%d_%d" % (r, k), prev, "l%d%d" % (r, k - r), "h%d%d" % (r, k - r - 1))
        q[k] = "q%d_%d" % (r, k)
        qc[k] = "cq%d_%d" % (r, k)
        prev = "cq%d_%d" % (r, k)
    addc("cq%d_%d" % (r, top), "q%d_%d" % (r, top), prev, "z0", "h%d5" % r)
    q[top] = "q%d_%d" % (r, top)
    qc[top] = "cq%d_%d" % (r, top)
    args = []
    prods = [(i, j) for i in range(r + 1) for j in range(i + 1, 6)]
    args += [P(i, j) for (i, j) in prods]
    args += [V("l%d%d" % (r, j)) for j in js] + [V("h%d%d" % (r, j)) for j in js]
    new = {}
    if r >= 1:
        args += [V(cur[k]) for k in range(1, r + 6)]
    for k in range(lo + 1, top + 1):
        args += [V(q[k]), V(qc[k])]
    if r == 0:
        new = dict(q)
    else:
        prev = "z0"
        for k in range(lo, top):
            addc("ca%d_%d" % (r, k), "n%d_%d" % (r, k), prev, cur[k], q[k])
            args += [V("n%d_%d" % (r, k)), V("ca%d_%d" % (r, k))]
            new[k] = "n%d_%d" % (r, k)
            prev = "ca%d_%d" % (r, k)
        addc("ca%d_%d" % (r, top), "n%d_%d" % (r, top), prev, "z0", q[top])
        args += [V("n%d_%d" % (r, top)), V("ca%d_%d" % (r, top))]
        new[top] = "n%d_%d" % (r, top)
    L("  sqx%d %s;" % (r, " ".join(args)))
    cur.update(new)
L("  put12 t z0 %s z0;" % " ".join(cur[k] for k in range(1, 11)))
L("}")
L("")
CROSS = out

# diag
out = []
L = out.append
L('[@@ CInline; CPrologue "__attribute__((always_inline))"]')
L("fn sq_diag (t: A.array S64.t) (a0 a1 a2 a3 a4 a5: S64.t) (#vt: erased (Seq.seq S64.t))")
L("requires A.pts_to t vt **")
L("  pure (Seq.length vt == 12 /\\ F64.ix vt 0 == 0 /\\ F64.ix vt 11 == 0 /\\ tv vt == CROSS)")
L("ensures exists* (vt': Seq.seq S64.t).")
L("  A.pts_to t vt' **")
L("  pure (Seq.length vt' == 12 /\\ tv vt' == DIAG + 2 * (CROSS))")
L("{")
L("  let z0 = S64.classify 0uL;")
L("  A.pts_to_len t;")
L("  consts ();")
for k in range(1, 11):
    L("  let t%d = A.(t.(%dsz));" % (k, k))
L("  let mut r = z0;")
prev = "z0"
for k in range(1, 11):
    addc("e%d" % k, "d%d" % k, prev, "t%d" % k, "t%d" % k)
    prev = "e%d" % k
for i in range(6):
    mul(i, i, "%d%d" % (i, i))
dw = {}
for i in range(6):
    dw[2 * i] = "l%d%d" % (i, i)
    dw[2 * i + 1] = "h%d%d" % (i, i)
prev = "z0"
for k in range(1, 12):
    dk = "d%d" % k if k <= 10 else "e10"
    addc("f%d" % k, "u%d" % k, prev, dk, dw[k])
    prev = "f%d" % k
args = [P(i, j) for i in range(6) for j in range(i, 6)]
args += [V("t%d" % k) for k in range(1, 11)]
args += [V("d%d" % k) for k in range(1, 11)] + [V("e%d" % k) for k in range(1, 11)]
args += [V("l%d%d" % (i, i)) for i in range(6)] + [V("h%d%d" % (i, i)) for i in range(6)]
args += [V("u%d" % k) for k in range(1, 12)] + [V("f%d" % k) for k in range(1, 12)]
L("  sqd %s;" % " ".join(args))
L("  put12 t l00 %s;" % " ".join("u%d" % k for k in range(1, 12)))
L("}")
L("")
DIAGF = out


def subst_a(s):
    import re
    return re.sub(r"p(\d)(\d)", lambda m: "(S64.v a%s * S64.v a%s)" % (m.group(1), m.group(2)), s)


CROSS_A = subst_a(cr(4))
DIAG_A = subst_a(" + ".join(term(2 * i, "p%d%d" % (i, i)) for i in range(6)))
CROSS[LINE_ENS] = ("  pure (Seq.length vt' == 12 /\\ F64.ix vt' 0 == 0 /\\ F64.ix vt' 11 == 0 /\\ "
                   "tv vt' == %s)" % CROSS_A)
DIAGF = [l.replace("DIAG", DIAG_A).replace("CROSS", CROSS_A) for l in DIAGF]

print(LEMMAS)
print("\n".join(CROSS))
print("\n".join(DIAGF))
