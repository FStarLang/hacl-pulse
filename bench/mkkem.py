"""Regenerate the ML-KEM and ML-DSA tables from a benchmark output directory.

Usage: python3 mkkem.py <bench-dir>

HACL* has neither, so unlike mktable.py these tables are absolute: one column
per parameter set, one row per operation, hacl-pulse only.  The ML-DSA table
is printed after the ML-KEM one when the run has its rows.  Reduction is by
minimum over every run, for the reason given in design/notes.md: interference can
only ever make a measurement slower.
"""
import csv, glob, os, sys

d = sys.argv[1]

best = {}
for f in glob.glob(os.path.join(d, 'Tpulse_*.csv')):
    for r in csv.reader(open(f)):
        if len(r) < 5 or r[0] == 'impl':
            continue
        try:
            ns = float(r[3])
        except ValueError:
            continue
        if ns < best.get(r[1], float('inf')):
            best[r[1]] = ns

SETS = ['512', '768', '1024']
OPS = [('keypair', 'keypair'),
       ('encapsulate', 'encapsulate'),
       ('decapsulate', 'decapsulate')]

missing = [f'mlkem{s}-{k}' for s in SETS for k, _ in OPS if f'mlkem{s}-{k}' not in best]
if missing:
    print('MISSING', ' '.join(missing), file=sys.stderr)
    sys.exit(1)

print('| operation | ML-KEM-512 | ML-KEM-768 | ML-KEM-1024 |')
print('| --- | ---: | ---: | ---: |')
for key, name in OPS:
    cells = ['%d us' % round(best['mlkem%s-%s' % (s, key)] / 1000.0) for s in SETS]
    print('| %s | %s |' % (name, ' | '.join(cells)))

DSETS = ['44', '65', '87']
DOPS = ['keypair', 'sign', 'verify']
if all(f'mldsa{s}-{k}' in best for s in DSETS for k in DOPS):
    print()
    print('| operation | ML-DSA-44 | ML-DSA-65 | ML-DSA-87 |')
    print('| --- | ---: | ---: | ---: |')
    for key in DOPS:
        cells = ['%d us' % round(best['mldsa%s-%s' % (s, key)] / 1000.0) for s in DSETS]
        print('| %s | %s |' % (key, ' | '.join(cells)))
