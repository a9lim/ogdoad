# r=257, a=1 instance of the Theorem A class engine, with efficient relevant-psi enumeration.
import math, cmath, itertools, numpy as np
from math import gcd
from nim import nmul, npow
from classes import fac, ordmod, g, dlog   # reuse nimber dlog on F_256
def run(name,L,mA,h,cmax=256):
    F=fac(L); comps=sorted(F); mods={l:l**F[l] for l in comps}; phis={l:mods[l]//l*(l-1) for l in comps}
    gens={};tab={}
    for l in comps:
        m=mods[l]; ph=phis[l]
        gl=next(x for x in range(2,m) if gcd(x,l)==1 and ordmod(x,m)==ph); gens[l]=gl
        t={};y=1
        for i in range(ph): t[y]=i; y=y*gl%m
        tab[l]=t
    lg=lambda x,l: tab[l][x%mods[l]]
    chi=lambda k,x: sum(k[l]*lg(x,l)/phis[l] for l in comps)%1.0
    big=comps[-1]; rest=comps[:-1]
    rel=[]
    for ks in itertools.product(*[range(phis[l]) for l in rest]):
        k=dict(zip(rest,ks))
        part=sum(k[l]*lg(2,l)/phis[l] for l in rest)
        d=lg(2,big); P=phis[big]
        # need kb*d/P = 1/h - part (mod 1)  ->  kb*d = (1/h-part)*P mod P
        tgt=((1.0/h-part)*P)%P
        if abs(tgt-round(tgt))>1e-6: continue
        tgt=int(round(tgt))%P; gg=gcd(d,P)
        if tgt%gg: continue
        kb0=(tgt//gg)*pow(d//gg,-1,P//gg)%(P//gg)
        for j in range(gg):
            k2=dict(k); k2[big]=kb0+j*(P//gg)
            if abs(chi(k2,L-1))<1e-9 or abs(chi(k2,L-1)-1)<1e-9:
                f=1
                for l in comps:
                    if k2[l]%phis[l]:
                        o=phis[l]//gcd(k2[l],phis[l]);v=0
                        while o%l==0:o//=l;v+=1
                        f*=l**(v+1)
                rel.append((k2,f))
    def lift(u,N):
        for U in range(u,L*N+1,N):
            if gcd(U,L)==1 and all((U-1)%mods[l]==0 for l in comps if N%l): return U
    def liftl(l):
        m=L//mods[l]
        for U in range(l,L*m+1,m):
            if gcd(U,L)==1 and (U-1)%mods[l]==0: return U
    LL={l:liftl(l) for l in comps}
    vecs=[];Ns={}
    for c in range(cmax):
        if c==0: vecs.append(np.zeros(len(rel),complex)); continue
        mt=(mA-dlog[c]*(L//255))%L; N=L//gcd(mt,L); u=mt//(L//N); Ns[c]=N
        U=lift(u%N,N); v=[]
        for k,f in rel:
            if N%f: v.append(0);continue
            z=cmath.exp(-2j*math.pi*chi(k,U))
            for l in fac(N):
                if f%l: z*=(1-cmath.exp(2j*math.pi*chi(k,LL[l])))
            v.append(z)
        vecs.append(np.array(v))
    new=[];forced=[];M=np.zeros((0,len(rel)),complex);r=0
    for c,v in enumerate(vecs):
        if np.linalg.norm(v)<1e-8: forced.append(c);continue
        M=np.vstack([M,v]); r2=np.linalg.matrix_rank(M,tol=1e-6)
        if r2>r: new.append(c); r=r2
    cls=[]
    for c in range(1,16):
        if np.linalg.norm(vecs[c])<1e-8: continue
        for C in cls:
            if np.linalg.matrix_rank(np.vstack([vecs[C[0]],vecs[c]]),tol=1e-6)==1: C.append(c);break
        else: cls.append([c])
    print(f"== {name}: h={h}, #rel={len(rel)}, forced<16={[c for c in forced if c<16]}, #forced<256={len(forced)}, rank<256={r}")
    print("   new directions <256:",new[:20],"..." if len(new)>20 else "")
    print("   classes c<16:",cls)
# kappa_257: order 5*17*257^2, kappa^257 = 256 (nimber in F_2^16)
e5=17476; e17=15420
n5=npow(256,e5); n17=npow(256,e17)
k5=npow(n5,3); k17=npow(n17,9)      # 257^{-1}=3 mod 5, 9 mod 17
assert npow(k5,257)==n5 and npow(k17,257)==n17
L=3*5*17*257**2
mA=(dlog[nmul(k5,k17)]*(L//255) + L//257**2)%L
for s in range(5): run("arm O r=257 a=1",L,mA,257*2**s)
