"""Print the design notes' ML-DSA table from an others.sh output dir.

Usage: python3 mkmldsa.py <bench-dir> [canary tolerance, default 0.02]

One row per parameter set and operation, one column per contender (fastest
of all runs, after dropping runs with an unhealthy canary, as mkothers.py
does), the fastest entry in each row in bold, and a last column giving the
better of the two hacl-pulse builds divided by the fastest other library.
"""
import csv, glob, os, sys

d = sys.argv[1]
TOL = float(sys.argv[2]) if len(sys.argv) > 2 else 0.02

COLS = [  # (csv file prefix, header)
    ("pulse-gcc",       "hacl-pulse (gcc)"),
    ("pulse-clang",     "hacl-pulse (clang)"),
    ("pqcrystals-ref",  "pq-crystals ref"),
    ("openssl",         "OpenSSL"),
    ("pqcrystals-avx2", "pq-crystals avx2"),
    ("mldsa-native",    "mldsa-native"),
    ("awslc",           "AWS-LC"),
    ("libcrux",         "libcrux"),
]
PULSE = {"pulse-gcc", "pulse-clang"}


def canary(f):
    for r in csv.reader(open(f)):
        if len(r) >= 4 and r[1] == 'canary':
            return float(r[3])
    return None


CAN = {f: canary(f) for f in glob.glob(os.path.join(d, "O*.csv"))}
FLOOR = min(c for c in CAN.values() if c)
DROPPED = {f for f, c in CAN.items() if c is None or c > (1 + TOL) * FLOOR}
print("canary floor %.0f ms; dropped %d of %d runs"
      % (FLOOR / 1e6, len(DROPPED), len(CAN)), file=sys.stderr)


def load(prefix):
    best = {}
    for f in glob.glob(os.path.join(d, "O%s_*.csv" % prefix)):
        if f in DROPPED:
            continue
        for r in csv.reader(open(f)):
            if len(r) < 4 or not r[1].startswith("mldsa"):
                continue
            ns = float(r[3])
            if r[1] not in best or ns < best[r[1]]:
                best[r[1]] = ns
    return best


DATA = {c: load(c) for c, _ in COLS}
for c, _ in COLS:
    if not DATA[c]:
        sys.exit("no healthy ML-DSA run of %s in %s" % (c, d))


def t(ns):
    return "{:,} us".format(int(round(ns / 1000.0)))


print("| operation | " + " | ".join(h for _, h in COLS) + " | hacl-pulse ÷ fastest other |")
print("| --- | " + " | ".join("---:" for _ in COLS) + " | ---: |")
for p in (44, 65, 87):
    for op, label in (("keypair", "keygen"), ("sign", "sign"), ("verify", "verify")):
        k = "mldsa%d-%s" % (p, op)
        vals = {c: DATA[c].get(k) for c, _ in COLS}
        fastest = min(v for v in vals.values() if v is not None)
        pulse = min(vals[c] for c in PULSE)
        other = min(v for c, v in vals.items() if c not in PULSE and v is not None)
        cells = ["--" if v is None else ("**%s**" % t(v) if v == fastest else t(v))
                 for v in (vals[c] for c, _ in COLS)]
        print("| ML-DSA-%d %s | %s | %.2fx |" % (p, label, " | ".join(cells), pulse / other))
