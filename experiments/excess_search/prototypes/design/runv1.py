import sys, subprocess, pickle, os
ARGS=[int(x) for x in sys.argv[1:]]
from mcstruct import *
from gentower import emit, closure
rows=pickle.load(open('../rows_1000000.pkl','rb'))
byh={}
for r in rows: byh.setdefault(r[1],[]).append(r[0])
def tasks_for(p, extra_neg=True):
    I=row_info(p); h=I['h']; e0=I['e0']; cs=I['cs']
    T=[ "euler "+" ".join(map(str,byh.get(h,[p]))) ]
    T.append(f"res {e0}")
    # negative control: test field lcm(h, partial) missing part of G
    if extra_neg and I['G']>1 and e0!=h and I['E']%h==0:
        # drop G: use e=h if valid divisor
        T.append(f"res {h}")
    big=[c for c in cs if c['D']//gcd(c['D'],e0)>1]
    ex=e0
    for c in big:
        if c['r']!=2: ex=lcm(ex,c['fr'])
    for c in big:
        if c['r']!=2 and c['a']==1: T.append(f"cross {c['q']} {ex}")
    b1=[c for c in big if c['r']!=2 and c['a']==1]
    if len(b1)==2: T.append(f"cross2 {b1[0]['q']} {b1[1]['q']} {ex}")
    if big and len(cs)>=2:
        g=1
        for c in cs:
            if c is not big[0]: g=lcm(g,gcd(c['D'],big[0]['D']))
        T.append(f"phase {g} {big[0]['q']}")
        T.append(f"phase 1 {big[0]['q']}")
    return T,I,ex
if __name__=='__main__':
    for p in ARGS:
        T,I,ex=tasks_for(p)
        open(f'tw_{p}.txt','w').write(emit(p)+"\n")
        open(f'tk_{p}.txt','w').write("\n".join(T)+"\n")
        print(f"=== p={p} h={I['h']} Q={I['Q']} E={I['E']} G={I['G']} e0={I['e0']} ex={ex}", flush=True)
        r=subprocess.run(['./mcverify',f'tw_{p}.txt',f'tk_{p}.txt'],capture_output=True,text=True,timeout=3000)
        print(r.stdout+r.stderr, flush=True)
