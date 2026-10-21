# Sanity check of Theorem A's character decomposition at h=24 (kappa=16+omega, N=765, p=241, m=8)
# and of Prop 1 / Lemma 1.1 at h=12 (kappa=4+omega, N=45, p=13, m=1). Computes conjugates, not rows.
import sys
sys.path.insert(0,'/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/0d823db5-514b-4211-b6ff-3cb614bd36e4/scratchpad/me')
from nim import nmul, npow
from math import gcd
def mk(Fq):
    def mul(x,y):
        c=[0]*5
        for i in range(3):
            for j in range(3): c[i+j]^=nmul(x[i],y[j])
        # omega^3=2, omega^4=2 omega
        c[0]^=nmul(2,c[3]); c[1]^=nmul(2,c[4])
        return (c[0],c[1],c[2])
    def pw(x,e):
        r=(1,0,0)
        while e:
            if e&1: r=mul(r,x)
            x=mul(x,x); e>>=1
        return r
    return mul,pw
def add(x,y): return tuple(a^b for a,b in zip(x,y))
def run(c, qbits, N, p, h):
    mul,pw=mk(None); Q=(1<<(3*qbits))-1
    om=(0,1,0); cc=(c,0,0)
    kap=add(cc,om)
    oc = 15 if c==4 else 85
    rho=mul(om, pw(cc,oc-1)); assert pw(rho,N)==(1,0,0) and all(pw(rho,N//l)!=(1,0,0) for l in (3,5,17) if N%l==0)
    t=pw(rho,(N+1)//2); ti=pw(t,N-1)
    eb=add(t,ti)
    print('h',h,'identity kappa = z1 t ebar:', mul(mul(cc,t),eb)==kap)
    e=Q//p
    w=pw(eb,e); print(' ebar^((q-1)/p) != 1 (row holds at selected prime):', w!=(1,0,0), ' same for kappa:', pw(kap,e)==w)
    tab={}; y=(1,0,0)
    for j in range(p): tab[y]=j; y=mul(y,w)
    G=[s for s in range(1,N) if gcd(s,N)==1]
    F={}
    for s in G:
        ts=pw(t,s); F[s]=tab[pw(add(ts,pw(t,N-s)),e)]
    ok=all(F[(2*s)%N]==2*F[s]%p and F[N-s]==F[s] for s in G); print(' F(2s)=2F(s), F(-s)=F(s):',ok)
    vals=set(); seen=set()
    reps=[]
    for s in G:
        if s in seen: continue
        orb=set(); x=s
        for j in range(4*h):
            orb.add(x); orb.add(N-x); x=2*x%N
        seen|=orb; reps.append(s)
    print(' m =',len(reps),' F on coset reps:',[(s,F[s]) for s in reps])
    return F,G
run(4,4,45,13,12)
F,G=run(16,8,765,241,24)
# characters of G=(Z/765)^x into F_241^x with psi(-1)=1, psi(2)=2
p=241; N=765
g=next(a for a in range(2,p) if all(pow(a,(p-1)//l,p)!=1 for l in (2,3,5)))
def dec(s):
    i=next(i for i in range(6) if pow(2,i,9)==s%9); j=next(j for j in range(4) if pow(2,j,5)==s%5)
    k=next(k for k in range(16) if pow(3,k,17)==s%17); return i,j,k
D={s:dec(s) for s in G}
out=[]
for al in range(6):
  for be in range(4):
    for ga in range(16):
      A=pow(g,40*al,p);B=pow(g,60*be,p);C=pow(g,15*ga,p)
      psi=lambda s:(pow(A,D[s][0],p)*pow(B,D[s][1],p)*pow(C,D[s][2],p))%p
      if psi(N-1)!=1 or psi(2)!=2: continue
      a=sum(F[s]*pow(psi(s),p-2,p) for s in G)%p
      i5,_,k5=dec(5*0+ (5 if True else 0)) if False else (next(i for i in range(6) if pow(2,i,9)==5),0,next(k for k in range(16) if pow(3,k,17)==5))
      psi5=(pow(A,i5,p)*pow(C,k5,p))%p
      out.append((B==1, C==1, psi5 if B==1 else None, a))
for o in out: print(' psi: trivial on I_5=%s, trivial on I_17=%s, psi(5) [if 5 missing]=%s, a_psi=%d'%o)
