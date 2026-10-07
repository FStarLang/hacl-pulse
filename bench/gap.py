import csv,glob,os,sys
d=sys.argv[1]
def load(pat):
    best={}
    for f in glob.glob(os.path.join(d,pat)):
        for r in csv.reader(open(f)):
            if len(r)<5 or r[0]=='impl': continue
            try: ns=float(r[3])
            except ValueError: continue
            k=(r[1],r[2])
            if k not in best or ns<best[k]: best[k]=ns
    return best
p=load('Tpulse_*.csv'); r=load('Tref_*.csv')
rows=[(p[k]/r[k],k,p[k],r[k]) for k in p if k in r and r[k]>0]
rows.sort(reverse=True)
print(f"{'benchmark':30s}{'size':>9s}{'pulse ns':>12s}{'ref ns':>12s}{'ratio':>8s}")
for ratio,k,pn,rn in rows[:int(sys.argv[2]) if len(sys.argv)>2 else 25]:
    print(f"{k[0]:30s}{k[1]:>9s}{pn:12.0f}{rn:12.0f}{ratio:7.2f}x")
