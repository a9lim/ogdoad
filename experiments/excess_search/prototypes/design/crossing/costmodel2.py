"""Refined cost model (single core, jobe-class x86 with PCLMUL) for singleton tops.
P(b): measured gf2x_mul on jobe.  Tiered tensor rep of K_1 with leaves <= LEAF bits:
  M(b) = 9 * 2^(tiers-1) * P(b);  squaring S = 0.25 M;  psi-power F = 1 M.
Row cost (one distinct h; all rows p with f(p)=h share it):
  root   = e*(0.4 f + 4 log2 D + 5) M
  bsgs   = 4 sqrt(2D) M
  inner  = 2 D^2 m_k(t) / PAR     (embarrassingly parallel; PAR=1 here)
  bm     = 30 D log2(D)^2 m_k(t)  (half-gcd BM over k)
  final  = (2 log2(t/s)+4) M_H(Rt) + Euler in F_{2^h}
  build  = 2 tiers * R_2 * M(b)   (embedding chi_{R_2} = a_2 v_2; a_2 cached from row r_1)
"""
import pickle, math, sys, collections
sys.argv=[sys.argv[0],'100000']
from census import *
PTS=[(1e5,0.142e-3),(1e6,3.05e-3),(3e6,10.47e-3),(1e7,42.5e-3),(3e7,130e-3),(1e8,0.506),(3e8,2.0),(1e9,6.93)]
def P(b):
    b=max(b,1e3)
    if b<=PTS[0][0]: return PTS[0][1]*(b/PTS[0][0])
    for (x0,y0),(x1,y1) in zip(PTS,PTS[1:]):
        if b<=x1:
            s=math.log(y1/y0)/math.log(x1/x0); return y0*(b/x0)**s
    x0,y0=PTS[-2]; x1,y1=PTS[-1]; s=math.log(y1/y0)/math.log(x1/x0); return y1*(b/x1)**s
LEAF=3e4
def mk(t):
    w=math.ceil(t/64); return 10e-9+1.2e-9*w**1.6
def vr(n,r):
    v=0
    while n%r==0: n//=r; v+=1
    return v
def tiers(D):
    if D<=LEAF: return 1
    return 1+math.ceil(math.log(D/LEAF)/math.log(300))
def plan(h,R):
    fr=factor(R); (r,e),=fr.items(); b1=b(r); s=h//R
    f=ordtwo(r); t=lcm(f,s); t=lcm(t,r**vr(b1,r))
    D=b1//t
    L=tiers(D); M=9*2**(L-1)*P(b1)
    lg=math.log2(max(D,2))
    root=e*(0.4*f+4*lg+5)*M if D>1 else 0
    bsgs=4*math.sqrt(2*D)*M if D>1 else 0
    inner=2*D*D*mk(t)
    bm=30*D*lg**2*mk(t)
    MH=9*P(R*t)
    final=(2*math.log2(max(t//max(s,1),2))+4)*MH + 2*h*mk(h)
    build=2*L*M
    tot=root+bsgs+inner+bm+final+build
    return dict(h=h,R=R,r=r,e=e,b=b1,t=t,D=D,L=L,root=root,bsgs=bsgs,inner=inner,bm=bm,final=final,total=tot,f=f)
if __name__=='__main__':
    rows=pickle.load(open('rows_100000.pkl','rb'))
    byh=collections.defaultdict(list)
    for (p,h,Q,a,m,E) in rows:
        if p>727 and a in ('O','C','D'): byh[(h,Q[0])].append((p,E))
    plans=[]
    for (h,R),lst in byh.items():
        x=plan(h,R); x['ps']=[p for p,_ in lst]; x['E']=lst[0][1]; plans.append(x)
    pickle.dump(plans,open('plans2.pkl','wb'))
    for PM in (10**4,10**5):
        sel=[(x,sum(1/p for p in x['ps'] if p<=PM)) for x in plans if min(x['ps'])<=PM]
        tot=sum(m for _,m in sel)
        print(f'p<={PM}: distinct h {len(sel)}  mass {tot:.4f}')
        sel.sort(key=lambda z:z[0]['total'])
        cum=0; cm=0; marks=[60,600,3600,36000,360000,3.6e6,3.6e7]; i=0
        for x,m in sel:
            while i<len(marks) and x['total']>marks[i]:
                print(f'   per-h cost <= {marks[i]:>9.0f}s : mass {cm:.4f} ({100*cm/tot:.1f}%), cumulative core-hours {cum/3600:9.1f}'); i+=1
            cum+=x['total']; cm+=m
        while i<len(marks):
            print(f'   per-h cost <= {marks[i]:>9.0f}s : mass {cm:.4f} ({100*cm/tot:.1f}%), cumulative core-hours {cum/3600:9.1f}'); i+=1
        print(f'   all: core-hours {cum/3600:.3g}')
    for p in (733,743,797,839,1019,1433,1439,2879,4507,719,9839):
        xs=[x for x in plans if p in x['ps']]
        if xs:
            x=xs[0]; print(p,{k:(f'{v:.3g}' if isinstance(v,float) else v) for k,v in x.items() if k!='ps'})
