"""Regenerate the design notes' ML-KEM table from a benchmark output directory.

Usage: python3 mkkem.py <bench-dir>

HACL* has no ML-KEM, so unlike mktable.py this table is absolute: one column
per parameter set, one row per operation, hacl-pulse only.  Reduction is by
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

print('| operation | 512 | 768 | 1024 |')
print('| --- | ---: | ---: | ---: |')
for key, name in OPS:
    cells = ['%d us' % round(best['mlkem%s-%s' % (s, key)] / 1000.0) for s in SETS]
    print('| %s | %s |' % (name, ' | '.join(cells)))
