import pickle, sys, math, itertools, collections
from mcstruct import *
LIM=int(sys.argv[2])
out=pickle.load(open(f'mc_{LIM}.pkl','rb'))
def best(o):
    e0=o['e0']; big=[c for c in o['cs'] if c['D']//gcd(c['D'],e0)>1]
    bestv=None
    for k in range(len(big)+1):
        for C in itertools.combinations(range(len(big)),k):
            e=e0
            for i in C: e=lcm(e,big[i]['fr'])
            sizes=[e]
            for i,c in enumerate(big):
                sizes.append(c['b'] if i in C else c['D'])
            v=max(sizes)
            if bestv is None or v<bestv[0]: bestv=(v,C,e)
    return bestv
res=[]
for o in out:
    v,C,e=best(o)
    res.append((o['p'],o['h'],o['E'],v,e,len(C)))
pickle.dump(res,open(f'mccost_{LIM}.pkl','wb'))
def q(xs,f): xs=sorted(xs); return xs[int(f*(len(xs)-1))]
print('rows',len(res))
print('E   quantiles',[q([r[2] for r in res],f) for f in (.1,.25,.5,.75,.9,.99)])
print('best quantiles',[q([r[3] for r in res],f) for f in (.1,.25,.5,.75,.9,.99)])
print('ratio E/best quantiles',[round(q([r[2]/r[3] for r in res],f),1) for f in (.1,.25,.5,.75,.9,.99)])
print('strategy (#crossed) counts',collections.Counter(r[5] for r in res))
# distinct h
hs={}
for r in res: hs.setdefault(r[1],[]).append(r)
print('distinct h',len(hs))
for B in (1e4,1e5,1e6,1e7,1e8,1e9):
    sD=sum(1/r[0] for r in res if r[2]<=B); sB=sum(1/r[0] for r in res if r[3]<=B)
    nD=sum(1 for r in res if r[2]<=B); nB=sum(1 for r in res if r[3]<=B)
    print(f'budget {B:.0e}: direct rows {nD} mass {sD:.4f} | best rows {nB} mass {sB:.4f}')
print('total mass multi', sum(1/r[0] for r in res))
