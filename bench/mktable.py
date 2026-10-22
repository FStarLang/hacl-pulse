"""Regenerate the design notes' performance table from a benchmark output directory.

Usage: python3 mktable.py <bench-dir>

Prints markdown rows sorted ascending by the hacl-pulse / HACL*-best ratio,
with the portable-C reference as the secondary column.
"""
import csv, glob, os, sys

d = sys.argv[1]

def load(pat):
    best = {}
    for f in glob.glob(os.path.join(d, pat)):
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

P = load('Tpulse_*.csv')
R = load('Tref_*.csv')
B = load('Tbest_*.csv')

# (display name, size label, benchmark key, size key)
ROWS = [
    ("SHA-256",              "256 KiB", "sha2-256", "262144"),
    ("SHA3-256",             "256 KiB", "sha3-256", "262144"),
    ("SHA-512",              "256 KiB", "sha2-512", "262144"),
    ("HMAC-SHA-512",         "256 KiB", "hmac-sha2-512", "262144"),
    ("HMAC-SHA-256",         "256 KiB", "hmac-sha2-256", "262144"),
    ("ChaCha20",             "256 KiB", "chacha20", "262144"),
    ("SHAKE128",             "256 KiB", "shake128", "262144"),
    ("ChaCha20-Poly1305",    "256 KiB", "chacha20poly1305-enc", "262144"),
    ("RSA-PSS-2048 sign",    "--",      "rsapss-2048-sign", "0"),
    ("FFDHE-2048",           "--",      "ffdhe2048-shared-secret", "0"),
    ("RSA-2048 modexp",      "--",      "bn2048-modexp-consttime", "0"),
    ("SHA-1",                "256 KiB", "sha1", "262144"),
    ("BLAKE2s",              "256 KiB", "blake2s", "262144"),
    ("P-256 ECDH",           "--",      "p256-dh-initiator", "0"),
    ("P-256 ECDSA verify",   "--",      "p256-ecdsa-verify", "0"),
    ("P-256 ECDSA sign",     "--",      "p256-ecdsa-sign", "0"),
    ("X25519",               "--",      "x25519-scalarmult", "0"),
    ("Poly1305",             "256 KiB", "poly1305", "262144"),
    ("RSA-PSS-2048 verify",  "--",      "rsapss-2048-verify", "0"),
    ("secp256k1 ECDSA sign", "--",      "k256-ecdsa-sign", "0"),
    ("NaCl secretbox",       "256 KiB", "nacl-secretbox-easy", "262144"),
    ("Salsa20",              "256 KiB", "salsa20", "262144"),
    ("Ed25519 sign",         "--",      "ed25519-sign-64B", "0"),
    ("BLAKE2b",              "256 KiB", "blake2b", "262144"),
    ("AES-128-GCM",          "256 KiB", "aes128-gcm-enc", "262144"),
    ("MD5",                  "256 KiB", "md5", "262144"),
]

def t(ns):
    if ns >= 1e6:
        return "%.1f ms" % (ns / 1e6)
    return "{:,} us".format(int(round(ns / 1000.0)))

out = []
for name, szl, k, sz in ROWS:
    key = (k, sz)
    if key not in P:
        print("MISSING", key, file=sys.stderr)
        continue
    p = P[key]
    r = R.get(key)
    b = B.get(key)
    if b is None:
        b = r
    out.append((p / b, name, szl, p, r, b))

out.sort()
print("| primitive | size | hacl-pulse | HACL\\* best | ratio | HACL\\* | ratio |")
print("| --- | ---: | ---: | ---: | ---: | ---: | ---: |")
for ratio, name, szl, p, r, b in out:
    rr = "%.2fx" % (p / r) if r else ""
    rs = t(r) if r else ""
    print("| %s | %s | %s | %s | **%.2fx** | %s | %s |"
          % (name, szl, t(p), t(b), ratio, rs, rr))
