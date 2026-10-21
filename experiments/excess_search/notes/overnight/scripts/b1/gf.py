# GF(2^n) arithmetic, int-encoded polynomials; used only for B1 lemma sanity checks.
import random
def pmulmod(a,b,f,n):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if a>>n &1: a^=f
    return r
def ppow(a,e,f,n):
    r=1
    while e:
        if e&1: r=pmulmod(r,a,f,n)
        a=pmulmod(a,a,f,n); e>>=1
    return r
def pgcd(a,b):
    while b:
        while a and a.bit_length()>=b.bit_length():
            a^=b<<(a.bit_length()-b.bit_length())
        a,b=b,a
    return a
def primes_of(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1: out.append(n)
    return out
def irreducible(f,n):
    x=2
    if ppow(x,1<<n,f,n)!=x: return False   # x^(2^n)=x
    for q in primes_of(n):
        y=x
        for _ in range(n//q): y=pmulmod(y,y,f,n)
        if pgcd(f, y^x)!=1: return False
    return True
def find_irred(n):
    for k in range(1,n):
        f=(1<<n)|(1<<k)|1
        if irreducible(f,n): return f
    for a in range(1,n):
        for b in range(a+1,n):
            for c in range(b+1,n):
                f=(1<<n)|(1<<c)|(1<<b)|(1<<a)|1
                if irreducible(f,n): return f
class F:
    def __init__(s,n):
        s.n=n; s.f=find_irred(n); s.q=(1<<n)-1
    def mul(s,a,b): return pmulmod(a,b,s.f,s.n)
    def pw(s,a,e): return ppow(a,e%s.q if a else e,s.f,s.n)
    def root(s,m,rng=random.Random(1)):
        # element of exact order m
        assert s.q%m==0
        while True:
            g=rng.randrange(2,1<<s.n)
            r=s.pw(g,s.q//m)
            if all(s.pw(r,m//l)!=1 for l in primes_of(m)): return r
    def kummer(s,x,p,theta):
        # Phi_p(x) in Z/p with x^((q)/p)=theta^Phi
        y=s.pw(x,s.q//p); t=1
        for k in range(p):
            if t==y: return k
            t=s.mul(t,theta)
        raise ValueError
