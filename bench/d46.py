import csv, os, sys, glob
def load(d, pat):
    best={}
    for f in glob.glob(os.path.join(d, pat)):
        for r in csv.reader(open(f)):
            if len(r)<5 or r[0]=='impl': continue
            try: ns=float(r[3])
            except ValueError: continue
            k=(r[1], r[2])
            if k not in best or ns<best[k]: best[k]=ns
    return best
new_d, old_d, cfg = sys.argv[1], sys.argv[2], sys.argv[3]
new = load(new_d, cfg+'pulse_*.csv'); old = load(old_d, cfg+'pulse_*.csv')
print(f"{'benchmark':28s} {'size':>8s} {'new':>12s} {'old':>12s} {'old/new':>8s}")
for k in sorted(new):
    n=new[k]; o=old.get(k)
    if not o: continue
    r=o/n
    if abs(r-1) > 0.04:
        print(f"{k[0]:28s} {k[1]:>8s} {n:12.0f} {o:12.0f} {r:7.2f}x" + ("  <== REGRESSION" if r<1 else ""))
