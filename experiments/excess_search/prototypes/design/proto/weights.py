"""Weights (term counts) of free chain min polys over F_2 (spread X->X^q, Taylor shift X->X+1)."""
import sys, collections
from terms import *
from functools import lru_cache
LIM=int(sys.argv[1]); BMAX=int(sys.argv[2])
def spread(P, q):
    out=0; i=0
    while P:
        if P&1: out|=1<<(i*q)
        P>>=1; i+=1
    return out
def taylor1(P):
    n=P.bit_length(); k=0
    while (1<<k) < n:
        s=1<<k; blk=s<<1
        # mask selecting low halves of blocks of size 2s
        m=0; unit=((1<<s)-1)
        # build mask by doubling
        m=unit; width=blk
        while width < n: m |= m << width; width <<= 1
        P ^= (P >> s) & m; k+=1
    return P
TWO={2: 0b111, 4: 0b10011}   # chi_2: X^2+X+1 ; chi_4: X^4+X+1  (min polys over F_2)
@lru_cache(None)
def P_alpha(r):
    """F_2 min poly of alpha_r if obtainable by free ops from a 2-power bottom; else None."""
    h=ordtwo(r); Q=Qset(h); m=rule(r,h,Q)
    if len(Q)!=1 or m>1: return None
    q=Q[0]; s,k=cprime(q)
    if s==2:
        if q not in TWO: return None
        P=TWO[q]
    else:
        Ps=P_alpha(s)
        if Ps is None: return None
        if Ps.bit_length()-1 > BMAX//q: return None
        P=spread(Ps,q)
    return taylor1(P) if m==1 else P
rows=[p for p in primes[1:] if 727<p<=LIM]
stat=[]
for p in rows:
    h=ordtwo(p); Q=Qset(h)
    if len(Q)!=1: continue
    q=Q[0]; s,k=cprime(q)
    if s==2: continue
    Ps=P_alpha(s)
    E=deg(cl_alpha(p))
    if Ps is None: stat.append((p,E,s,None,None)); continue
    stat.append((p,E,s,Ps.bit_length()-1,Ps.bit_count()))
free=[x for x in stat if x[3] is not None]
print('singleton-Q rows', len(stat), 'with free-chain base poly (b_s<=BMAX/q)', len(free))
for x in sorted(free, key=lambda t:t[1])[:40]:
    print(f'p={x[0]} E={x[1]} s={x[2]} b_s={x[3]} weight={x[4]} frac={x[4]/x[3]:.3f}')
w=collections.Counter()
for x in free:
    w[min(5,int(10*x[4]/x[3]) if x[4]>5 else 0)]+=1
print('weight-fraction buckets (0 means <=5 terms):', sorted(w.items()))
print('sparse (<=64 terms) rows:', [(x[0],x[1],x[4]) for x in free if x[4]<=64])
