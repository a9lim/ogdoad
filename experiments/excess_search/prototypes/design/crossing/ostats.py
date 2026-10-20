import pickle, math, sys, collections
sys.argv=[sys.argv[0],'100000']
from census import *
rows=pickle.load(open('rows_100000.pkl','rb'))
def vr(n,r):
    v=0
    while n%r==0: n//=r; v+=1
    return v
out=[]
for (p,h,Q,a,m,E) in rows:
    if p<=727 or a not in ('O','C','D'): continue
    R=Q[0]; r=min(factor(R)); bb=b(r); s=h//R
    f=ordtwo(r)
    t=lcm(f,s)
    t=lcm(t, r**vr(bb,r))
    assert bb%t==0, (p,bb,t)
    D=bb//t
    out.append((p,h,R,r,bb,t,D,R*t,E))
pickle.dump(out,open('ostats.pkl','wb'))
for P in (10**4,10**5):
    sel=[o for o in out if o[0]<=P]
    mass=sum(1/o[0] for o in sel)
    print('P',P,'rows',len(sel),'mass',round(mass,4),'distinct h',len(set(o[1] for o in sel)))
    for B in (1e4,1e5,1e6,1e7,1e8,1e9,1e12):
        for key,name in ((4,'b'),(7,'Rt'),(8,'E')):
            s2=[o for o in sel if o[key]<=B]
            print(f'  {name}<={B:.0e}: rows {len(s2)} mass {sum(1/o[0] for o in s2):.4f}',end=';')
        print()
for o in out[:30]: print(o)
