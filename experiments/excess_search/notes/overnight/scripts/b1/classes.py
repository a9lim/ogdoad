# Structural status of translates kappa+c (c<256) via Theorem A coefficient vectors.
# v_c[psi] = [f_psi | N_c] * conj(psi(u_c)) * prod_{l|N_c, l not| f_psi} (1-psi(l)),
# psi over even chars mod L with psi(2) = exp(2 pi i/h) (one prime P above p).
import sys, math, cmath, itertools
import numpy as np
from nim import nmul, npow
from math import gcd
def fac(n):
    out={};d=2
    while d*d<=n:
        while n%d==0: out[d]=out.get(d,0)+1; n//=d
        d+=1
    if n>1: out[n]=out.get(n,0)+1
    return out
def ordmod(a,n):
    k=1;x=a%n
    while x!=1: x=x*a%n;k+=1
    return k
# nimber generator of F_256^x
def nord(x):
    k=1;y=x
    while y!=1: y=nmul(y,x);k+=1
    return k
g=next(x for x in range(2,256) if nord(x)==255)
dlog={1:0}; y=1
for i in range(1,255):
    y=nmul(y,g); dlog[y]=i
def run(name, L, mA, B, h, cmax=256, show16=True):
    F=fac(L); comps=sorted(F)
    gens={}
    for l in comps:
        m=l**F[l]; ph=m//l*(l-1)
        gens[l]=next(x for x in range(2,m) if gcd(x,l)==1 and ordmod(x,m)==ph)
    logs={}
    def lg(x,l):
        m=l**F[l]; ph=m//l*(l-1); key=(x%m,l)
        if key not in logs:
            y=1
            for i in range(ph):
                if y==x%m: logs[key]=i;break
                y=y*gens[l]%m
        return logs[key]
    phis={l:l**F[l]//l*(l-1) for l in comps}
    def chi(k,x):  # value as fraction of turn
        return sum(k[i]*lg(x,l)/phis[l] for i,l in enumerate(comps))%1.0
    def cond(k):
        f=1
        for i,l in enumerate(comps):
            if k[i]%phis[l]:
                o=phis[l]//gcd(k[i],phis[l]); v=0
                while o%l==0: o//=l; v+=1
                f*=l**(v+1)
        return f
    rel=[]
    for k in itertools.product(*[range(phis[l]) for l in comps]):
        if abs(chi(k,L-1))>1e-9 and abs(chi(k,L-1)-1)>1e-9: continue
        v2=chi(k,2)
        if abs(v2-1.0/h)<1e-9 or abs(v2-1.0/h-1)<1e-9: rel.append((k,cond(k)))
    def lift(u,N):  # unit mod L, = u mod N, = 1 mod prime powers of L not dividing N
        for U in range(u,L*N+1,N):
            if gcd(U,L)==1 and all((U-1)%(l**F[l])==0 for l in comps if N%l): return U
        raise
    def liftl(l,f):
        m=L//(l**F[l])
        for U in range(l, L*m+1, m):
            if gcd(U,L)==1 and (U-1)%(l**F[l])==0: return U
    vecs=[]; info=[]
    for c in range(cmax):
        y=B^c
        if y==0: vecs.append(np.zeros(len(rel),complex)); info.append((c,'root')); continue
        mt=(mA - dlog[y]*(L//255))%L
        N=L//gcd(mt,L); u=mt//(L//N)
        v=[]
        for k,f in rel:
            if N%f: v.append(0); continue
            U=lift(u%N,N)
            z=cmath.exp(-2j*math.pi*chi(k,U))
            for l in fac(N):
                if f%l: z*= (1-cmath.exp(2j*math.pi*chi(k,liftl(l,f))))
            v.append(z)
        vecs.append(np.array(v)); info.append((c,N))
    # new directions
    new=[]; M=np.zeros((0,len(rel)),complex); r=0
    forced=[]
    for c,v in enumerate(vecs):
        if np.linalg.norm(v)<1e-8: forced.append(c); continue
        M2=np.vstack([M,v]); r2=np.linalg.matrix_rank(M2,tol=1e-7)
        if r2>r: new.append(c); r=r2
        M=M2
    print(f"== {name}: L={L}, h={h}, #relevant psi (one P)={len(rel)}, conductors={sorted(set(f for _,f in rel))}")
    print("   forced c<16:", [c for c in forced if c<16], " forced count <256:", len(forced))
    print("   new-direction translates (possible m_p values, generic) <%d:"%cmax, new)
    if show16:
        # proportionality classes among c<16
        cls=[]
        for c in range(16):
            v=vecs[c]
            if np.linalg.norm(v)<1e-8: continue
            for C in cls:
                w=vecs[C[0]]; A=np.vstack([w,v])
                if np.linalg.matrix_rank(A,tol=1e-7)==1: C.append(c); break
            else: cls.append([c])
        print("   proportional classes c<16:", cls)
        print("   N_c for c<16:", {c:info[c][1] for c in range(16)})
d2=dlog[2]; d4=dlog[4]; d16=dlog[16]
which=sys.argv[1:]
def mA_root(L,n,base_exp,power):
    # A of exact order n with A^power = nimber with dlog base_exp
    for x in range(1,n):
        if gcd(x,n)!=1: continue
        m=(L//n)*x
        if (m*power - base_exp*(L//255))%L==0: return m
    raise
if 'C' in which or not which:
    for k in (1,2):
        n=3**(k+1); L=n*85//gcd(n,85)*1; L=n*85
        run(f"arm C k={k}", L, mA_root(L,n,d2,3**k), 0, 3**k)
if 'D' in which or not which:
    for k in (2,):
        n=3**(k+1); L=n*85
        run(f"arm D k={k}", L, mA_root(L,n,d2,3**k), 0, 2*3**k)
if 'O5' in which or not which:
    L=3*25*17
    for h in (5,10,20): run(f"arm O r=5 a=1", L, mA_root(L,75,d4,5), 0, h, show16=(h==10))
if 'O17' in which or not which:
    L=3*5*289
    for h in (17,34,68,136): run(f"arm O r=17 a=1", L, mA_root(L,1445,d16,17), 0, h)
if 'Z' in which or not which:
    for b in (1,):
        n=3**(b+1); L=n*85
        run(f"arm Z Q={{3^{b},4}}", L, mA_root(L,n,d2,3**b), 4, 4*3**b)
