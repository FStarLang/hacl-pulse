"""Regenerate the README's other-libraries table from an others.sh output dir.

Usage: python3 mkothers.py <bench-dir> [canary tolerance, default 0.02]

One row per primitive, one column per contender (fastest of all runs), the
fastest entry in each row in bold, and a last column giving the better of
the two hacl-pulse builds divided by the fastest other library.  Rows are
sorted by that ratio.  Runs with an unhealthy canary are dropped first.  A dash means the library does not offer the row.

The ML-DSA-only contenders get no column here and do not count in the
ratio; mkmldsa.py prints the full ML-DSA table.
"""
import csv, glob, os, sys

d = sys.argv[1]
TOL = float(sys.argv[2]) if len(sys.argv) > 2 else 0.02

COLS = [  # (csv file prefix, header)
    ("pulse-gcc",   "hacl-pulse (gcc)"),
    ("pulse-clang", "hacl-pulse (clang)"),
    ("openssl",     "OpenSSL"),
    ("awslc",       "AWS-LC"),
    ("libsodium",   "libsodium"),
    ("libjade",     "libjade"),
    ("firedancer",  "Firedancer"),
    ("dalek",       "dalek"),
]
PULSE = {"pulse-gcc", "pulse-clang"}

def canary(f):
    for r in csv.reader(open(f)):
        if len(r) >= 4 and r[1] == 'canary':
            return float(r[3])
    return None

# A run whose canary is more than TOL (2%) above the best seen anywhere measured a
# slower core, not a slower library, and is dropped.
CAN = {f: canary(f) for f in glob.glob(os.path.join(d, "O*.csv"))}
FLOOR = min(c for c in CAN.values() if c)
DROPPED = [f for f, c in CAN.items() if c is None or c > (1 + TOL) * FLOOR]
print("canary floor %.0f ms; dropped %d of %d runs"
      % (FLOOR / 1e6, len(DROPPED), len(CAN)), file=sys.stderr)

def load(prefix):
    best = {}
    for f in glob.glob(os.path.join(d, "O%s_*.csv" % prefix)):
        if f in DROPPED:
            continue
        for r in csv.reader(open(f)):
            if len(r) < 5 or r[0] == 'impl':
                continue
            try:
                ns = float(r[3])
            except ValueError:
                continue
            k = (r[1], r[2])
            if k not in best or ns < best[k]:
                best[k] = ns
    return best

DATA = {c: load(c) for c, _ in COLS}
for c in DATA:
    if not DATA[c]:
        sys.exit("no healthy run of %s in %s" % (c, d))

# (display name, size label, benchmark key, size key)
ROWS = [
    ("MD5",                  "256 KiB", "md5", "262144"),
    ("SHA-1",                "256 KiB", "sha1", "262144"),
    ("SHA-256",              "256 KiB", "sha2-256", "262144"),
    ("SHA-512",              "256 KiB", "sha2-512", "262144"),
    ("SHA3-256",             "256 KiB", "sha3-256", "262144"),
    ("SHAKE128",             "256 KiB", "shake128", "262144"),
    ("BLAKE2b",              "256 KiB", "blake2b", "262144"),
    ("BLAKE2s",              "256 KiB", "blake2s", "262144"),
    ("HMAC-SHA-256",         "256 KiB", "hmac-sha2-256", "262144"),
    ("HMAC-SHA-512",         "256 KiB", "hmac-sha2-512", "262144"),
    ("Poly1305",             "256 KiB", "poly1305", "262144"),
    ("ChaCha20",             "256 KiB", "chacha20", "262144"),
    ("Salsa20",              "256 KiB", "salsa20", "262144"),
    ("ChaCha20-Poly1305",    "256 KiB", "chacha20poly1305-enc", "262144"),
    ("NaCl secretbox",       "256 KiB", "nacl-secretbox-easy", "262144"),
    ("AES-128-GCM",          "256 KiB", "aes128-gcm-enc", "262144"),
    ("AES-256-GCM",          "256 KiB", "aes256-gcm-enc", "262144"),
    ("X25519",               "--",      "x25519-scalarmult", "0"),
    ("Ed25519 sign",         "--",      "ed25519-sign-64B", "0"),
    ("Ed25519 verify",       "--",      "ed25519-verify-64B", "0"),
    ("P-256 ECDH",           "--",      "p256-ecdh", "0"),
    ("P-256 ECDSA sign",     "--",      "p256-ecdsa-sign", "0"),
    ("P-256 ECDSA verify",   "--",      "p256-ecdsa-verify", "0"),
    ("secp256k1 ECDSA sign", "--",      "k256-ecdsa-sign", "0"),
    ("RSA-PSS-2048 sign",    "--",      "rsapss-2048-sign", "0"),
    ("RSA-PSS-2048 verify",  "--",      "rsapss-2048-verify", "0"),
    ("FFDHE-2048",           "--",      "ffdhe2048-shared-secret", "0"),
    ("ML-KEM-768 keygen",    "--",      "mlkem768-keypair", "0"),
    ("ML-KEM-768 encaps",    "--",      "mlkem768-encapsulate", "0"),
    ("ML-KEM-768 decaps",    "--",      "mlkem768-decapsulate", "0"),
    ("ML-DSA-65 keygen",     "--",      "mldsa65-keypair", "0"),
    ("ML-DSA-65 sign",       "--",      "mldsa65-sign", "0"),
    ("ML-DSA-65 verify",     "--",      "mldsa65-verify", "0"),
]

def t(ns):
    if ns >= 1e6:
        return "%.1f ms" % (ns / 1e6)
    if ns >= 1e4:
        return "{:,} us".format(int(round(ns / 1000.0)))
    return "%.1f us" % (ns / 1000.0)

out = []
for name, szl, k, sz in ROWS:
    key = (k, sz)
    vals = {c: DATA[c].get(key) for c, _ in COLS}
    pulse = [vals[c] for c in PULSE if vals[c] is not None]
    others = [v for c, v in vals.items() if c not in PULSE and v is not None]
    if not pulse:
        print("MISSING", key, file=sys.stderr)
        continue
    ratio = min(pulse) / min(others) if others else None
    out.append((ratio if ratio is not None else 0.0, name, szl, vals))

out.sort(key=lambda r: r[0])
print("| primitive | size | " + " | ".join(h for _, h in COLS) + " | hacl-pulse ÷ fastest other |")
print("| --- | ---: | " + " | ".join("---:" for _ in COLS) + " | ---: |")
for ratio, name, szl, vals in out:
    fastest = min(v for v in vals.values() if v is not None)
    cells = []
    for c, _ in COLS:
        v = vals[c]
        if v is None:
            cells.append("--")
        elif v == fastest:
            cells.append("**%s**" % t(v))
        else:
            cells.append(t(v))
    rs = "%.2fx" % ratio if ratio else "--"
    print("| %s | %s | %s | %s |" % (name, szl, " | ".join(cells), rs))
