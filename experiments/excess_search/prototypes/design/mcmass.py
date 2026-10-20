import sys, math, pickle, collections
LIM=int(sys.argv[1]) if len(sys.argv)>1 else 10**4
from mcmodel import *
rows=pickle.load(open('../rows_1000000.pkl','rb'))
res=[]; sing=[]
for (p,h,Q,arm_,m,E) in rows:
    if not (727<p<=LIM): continue
    if arm_=='Z' and len(Q)>=2:
        I,o=row_costs(p); res.append((p,h,E,o['D'],o['best'],o['ex'],len(o['bestC'])))
    elif arm_ in ('O','C','D'):
        s=singleton_cost(p)
        if s: sing.append((p,h,E,s['direct'],s['crossed'],s['ex']))
pickle.dump((res,sing),open(f'mcmass_{LIM}.pkl','wb'))
def q(xs,f): xs=sorted(xs); return xs[int(f*(len(xs)-1))]
def report(name,L,iD,iB):
    print(f'--- {name}: rows {len(L)}, mass {sum(1/r[0] for r in L):.4f}')
    print('  direct cost quantiles (s)',['%.3g'%q([r[iD] for r in L],f) for f in (.25,.5,.75,.9,.99)])
    print('  best   cost quantiles (s)',['%.3g'%q([r[iB] for r in L],f) for f in (.25,.5,.75,.9,.99)])
    for B in (1,60,3600,86400,7*86400):
        sD=[r for r in L if r[iD]<=B]; sB=[r for r in L if r[iB]<=B]
        print(f'  budget {B:>7}s/row: direct {len(sD):>5} rows mass {sum(1/r[0] for r in sD):.4f} (total {sum(r[iD] for r in sD)/3600:.1f} h) | best {len(sB):>5} rows mass {sum(1/r[0] for r in sB):.4f} (total {sum(r[iB] for r in sB)/3600:.1f} h)')
report(f'multi-component arm Z, 727<p<={LIM}',res,3,4)
report(f'singleton O/C/D (crossed 719-style), 727<p<={LIM}',sing,3,4)
