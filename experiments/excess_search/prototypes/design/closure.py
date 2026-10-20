"""Closure structure of rows: components, sharing, reuse."""
import sys, math, pickle, collections
sys.path.insert(0,'..')
sys.argv=[sys.argv[0], sys.argv[1] if len(sys.argv)>1 else '100000']
from census import *
from functools import lru_cache

def comp_prime(q):
    f=factor(q); (r,k),=f.items(); return r,k

@lru_cache(None)
def closure_q(q):
    """downward closure of component chi_q as frozenset of q's (2-powers as 2^k)."""
    r,k=comp_prime(q)
    if r==2:
        return frozenset(2**j for j in range(1,k+1))
    s={r**j for j in range(1,k+1)}
    return frozenset(s)|closure_alpha(r)
@lru_cache(None)
def closure_alpha(r):
    h=ordtwo(r); Q=Qset(h); m=rule(r,h,Q)
    s=set()
    for q in Q: s|=closure_q(q)
    # finite excess m: m in C_a with d_finite(m)=2^a -> needs chi_2..chi_{2^a}
    if m>=2:
        a=d_finite(m).bit_length()-1
        s|={2**j for j in range(1,a+1)}
    return frozenset(s)
def deg(S):
    d=1
    for q in S: d*=comp_prime(q)[0]
    return d
if __name__=='__main__':
    bad=0
    for p in primes[1:]:
        h=ordtwo(p); Q=Qset(h); m=rule(p,h,Q)
        E=lcm(dsum(Q), d_finite(m))
        S=closure_alpha(p)
        if deg(S)!=E: bad+=1; print('deg mismatch',p,deg(S),E)
    print('deg(closure)==E mismatches:',bad, 'rows', len(primes)-1)
