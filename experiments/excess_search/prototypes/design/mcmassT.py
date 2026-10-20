import sys, math, pickle
LIM=int(sys.argv[1])
from mcmodel import *
rows=pickle.load(open('../rows_1000000.pkl','rb'))
res=[]; sing=[]
for (p,h,Q,arm_,m,E) in rows:
    if not (727<p<=LIM): continue
    if arm_=='Z' and len(Q)>=2:
        o=row_costs_T(p); res.append((p,h,E,o['D'],o['best']))
    elif arm_ in ('O','C','D'):
        s=singleton_cost_T(p)
        if s: sing.append((p,h,E,s['direct'],s['crossed']))
pickle.dump((res,sing),open(f'mcmassT_{LIM}.pkl','wb'))
def q(xs,f): xs=sorted(xs); return xs[int(f*(len(xs)-1))]
def report(name,L):
    print(f'--- {name}: rows {len(L)}, mass {sum(1/r[0] for r in L):.4f}')
    print('  direct quantiles (s)',['%.3g'%q([r[3] for r in L],f) for f in (.25,.5,.75,.9,.99)])
    print('  best   quantiles (s)',['%.3g'%q([r[4] for r in L],f) for f in (.25,.5,.75,.9,.99)])
    for B in (1,60,3600,86400):
        sD=[r for r in L if r[3]<=B]; sB=[r for r in L if r[4]<=B]
        print(f'  budget {B:>6}s/row: direct {len(sD):>5} rows mass {sum(1/r[0] for r in sD):.4f} ({sum(r[3] for r in sD)/3600:.1f} h) | best {len(sB):>5} rows mass {sum(1/r[0] for r in sB):.4f} ({sum(r[4] for r in sB)/3600:.1f} h)')
report(f'[tensor regime] multi arm Z 727<p<={LIM}',res)
report(f'[tensor regime] singleton 727<p<={LIM}',sing)
