"""Cost model for the crossing engine on singleton-top rows (arms O/C/D).
P(b): gf2x_mul time measured on jobe (x86 PCLMUL), interpolated log-log.
M(b) = 6 P(b) for a K-multiplication in the tensor representation (conservative)."""
import pickle, math, sys
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
def M(b): return 6*P(b)
def mk(t):  # one multiplication in F_{2^t}, seconds (clmul, single core)
    w=math.ceil(t/64); return 10e-9+1.2e-9*w**1.6
def vr(n,r):
    v=0
    while n%r==0: n//=r; v+=1
    return v
def plan(p,h,Q,arm,m,E):
    R=Q[0]; fr=factor(R); (r,e),=fr.items(); b1=b(r); s=h//R
    f=ordtwo(r); t=lcm(f,s); t=lcm(t,r**vr(b1,r))
    D=b1//t
    root = e*(f/5 + 6*math.log2(max(D,2)) + 4)*M(b1)
    cp_mult = 4*math.sqrt(2*D)*M(b1)
    cp_inner = 2*D*D*mk(t)
    bm = 20*D*math.log2(max(D,2))**2*mk(t) + 1e-6*D
    fin = (2*math.log2(max(t//max(s,1),2))+2)*M(R*t) + 2*h*mk(h)
    # lower level: alpha_r singleton?
    h2=ordtwo(r); Q2=Qset(h2); single = (len(Q2)==1 and Q2[0]%2==1)
    total = root+cp_mult+cp_inner+bm+fin
    return dict(p=p,h=h,R=R,r=r,e=e,b=b1,t=t,D=D,Rt=R*t,E=E,root=root,cpm=cp_mult,cpi=cp_inner,bm=bm,fin=fin,total=total,single=single,f=f)
if __name__=='__main__':
    rows=pickle.load(open('rows_100000.pkl','rb'))
    plans=[plan(*r) for r in rows if r[0]>727 and r[3] in ('O','C','D')]
    pickle.dump(plans,open('plans.pkl','wb'))
    for P_ in (10**4,10**5):
        sel=[x for x in plans if x['p']<=P_]
        tot=sum(1/x['p'] for x in sel)
        print(f'p<={P_}: singleton-top rows {len(sel)}, mass {tot:.4f}; lower level singleton: rows {sum(x["single"] for x in sel)} mass {sum(1/x["p"] for x in sel if x["single"]):.4f}')
        for B in (60,600,3600,36000,360000,3.6e6):
            s2=[x for x in sel if x['total']<=B]
            print(f'   cost<= {B:>9.0f}s: rows {len(s2):5d} mass {sum(1/x["p"] for x in s2):.4f} ({100*sum(1/x["p"] for x in s2)/tot:.1f}%)  core-hours for all {sum(x["total"] for x in s2)/3600:.1f}')
    for p in (733,797,839,1019,1433,4507,719):
        x=[y for y in plans if y['p']==p]
        if x: x=x[0]; print({k:(round(v,3) if isinstance(v,float) else v) for k,v in x.items()})
