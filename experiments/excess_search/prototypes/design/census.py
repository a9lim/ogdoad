"""Arm census, field degrees, and random-model sums for the 0/1/4 rule."""
import sys, math
from functools import lru_cache
from math import gcd
sys.setrecursionlimit(100000)
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**5

def sieve(n):
    s = bytearray([1])*(n+1); s[0]=s[1]=0
    for i in range(2,int(n**0.5)+1):
        if s[i]: s[i*i::i]=bytearray(len(s[i*i::i]))
    return [i for i in range(n+1) if s[i]]
primes = sieve(N)
spf = list(range(N+1))
for p in primes:
    if p*p > N: break
    for m in range(p*p, N+1, p):
        if spf[m]==m: spf[m]=p
def factor(n):
    out={}
    while n>1:
        p=spf[n] if n<=N else None
        if p is None:
            d=2
            while d*d<=n:
                while n%d==0: out[d]=out.get(d,0)+1; n//=d
                d+=1
            if n>1: out[n]=out.get(n,0)+1
            return out
        while n%p==0: out[p]=out.get(p,0)+1; n//=p
    return out
def ordtwo(p):
    o=p-1
    for q in factor(p-1):
        while o%q==0 and pow(2,o//q,p)==1: o//=q
    return o
def lcm(a,b): return a//gcd(a,b)*b

RULE_M = {}
def d_finite(m):
    if m<=1: return 1
    k=1
    while m >= (1<<(1<<k)): k+=1
    return 1<<k   # m < 2^(2^k) -> degree 2^k
@lru_cache(None)
def b(r):           # degree of alpha_r
    h=ordtwo(r); Q=Qset(h)
    m=rule(r,h,Q)
    return lcm(dsum(Q), d_finite(m))
def dq(q):
    f=factor(q); (r,k),=f.items()
    if r==2: return q
    return q*b(r)
def dsum(Q):
    d=1
    for q in Q: d=lcm(d,dq(q))
    return d
@lru_cache(None)
def Qset(h):
    if h==1: return ()
    f=factor(h); r=min(f); q=r**f[r]; g=h//q
    Q=Qset(g)
    if dsum(Q)%q!=0: Q=tuple(sorted(Q+(q,)))
    return Q
def arm(h,Q):
    if len(Q)==1 and Q[0]%2==1:
        r=min(factor(Q[0]))
        if r==3:
            return 'C' if h==Q[0] else 'D'
        return 'O'
    if len(Q)==1 and Q[0]%2==0: return 'ZF'
    return 'Z'
def rule(p,h,Q):
    a=arm(h,Q)
    return {'Z':0,'ZF':0,'O':1,'C':1,'D':4}[a]

if __name__=='__main__':
    import collections
    S=collections.Counter(); cnt=collections.Counter()
    rows=[]
    for p in primes[1:]:
        h=ordtwo(p); Q=Qset(h); a=arm(h,Q); m=rule(p,h,Q)
        E=lcm(dsum(Q), d_finite(m))
        rows.append((p,h,Q,a,m,E))
        if p>727: S[a]+=1.0/p
        cnt[a]+=1
    # check against OEIS table
    oeis=[int(x) for x in open('/Users/a9lim/Work/ogdoad/src/scalar/big/ordinal/b380496.txt').read().split()[1::2]]
    bad=[(r[0],r[4],o) for r,o in zip(rows,oeis) if r[4]!=o]
    print('OEIS mismatches:',bad)
    print('counts',dict(cnt))
    print('sum 1/p over (727,N] by arm', {k:round(v,4) for k,v in S.items()}, 'total', round(sum(S.values()),4))
    import pickle; pickle.dump(rows,open(f'rows_{N}.pkl','wb'))
    Es=sorted(r[5] for r in rows if r[0]>727)
    for qq in (0.1,0.25,0.5,0.75,0.9,0.99):
        print('E quantile',qq,Es[int(qq*(len(Es)-1))])
