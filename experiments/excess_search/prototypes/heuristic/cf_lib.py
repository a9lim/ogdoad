"""Fast arm census to N (numpy spf sieve); same Q(h)/arm logic as ../census.py.

Output: census_<N>.npz with arrays p, h, arm (0=Z,1=ZF,2=O,3=C,4=D), r, a
(r,a = singleton component prime/exponent for O/C/D/ZF, 0 for Z), nq (|Q|).
"""
import sys, math, time
import numpy as np
from math import gcd
sys.setrecursionlimit(1000000)
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**7
t0 = time.time()
spf = np.zeros(N + 1, dtype=np.int32)
lim = int(N ** 0.5) + 1
for p in range(2, lim + 1):
    if spf[p] == 0:
        seg = spf[p * p::p]
        seg[seg == 0] = p
        spf[p * p::p] = seg
isprime = (spf == 0)
isprime[:2] = False
primes = np.nonzero(isprime)[0]
print('sieve done', len(primes), round(time.time() - t0, 1), flush=True)
spf_l = spf  # numpy access

def factor(n):
    out = {}
    while n > 1:
        p = int(spf_l[n]) if n <= N else 0
        if p == 0:
            if n <= N:
                p = n
            else:
                d = 2
                while d * d <= n:
                    while n % d == 0:
                        out[d] = out.get(d, 0) + 1; n //= d
                    d += 1
                if n > 1: out[n] = out.get(n, 0) + 1
                return out
        while n % p == 0:
            out[p] = out.get(p, 0) + 1; n //= p
    return out

_ord = {}
def ordtwo(p):
    o = _ord.get(p)
    if o is not None: return o
    o = p - 1
    for q in factor(p - 1):
        while o % q == 0 and pow(2, o // q, p) == 1: o //= q
    _ord[p] = o
    return o

def lcm(a, b): return a // gcd(a, b) * b
def d_finite(m):
    if m <= 1: return 1
    k = 1
    while m >= (1 << (1 << k)): k += 1
    return 1 << k
_b = {}
def b(r):
    v = _b.get(r)
    if v is not None: return v
    h = ordtwo(r); Q = Qset(h); m = rule(h, Q)
    v = lcm(dsum(Q), d_finite(m)); _b[r] = v
    return v
def comp(q):
    f = factor(q); (r, k), = f.items(); return r, k
def dq(q):
    r, k = comp(q)
    return q if r == 2 else q * b(r)
def dsum(Q):
    d = 1
    for q in Q: d = lcm(d, dq(q))
    return d
_Q = {}
def Qset(h):
    v = _Q.get(h)
    if v is not None: return v
    if h == 1: return ()
    f = factor(h); r = min(f); q = r ** f[r]; g = h // q
    Q = Qset(g)
    if dsum(Q) % q != 0: Q = tuple(sorted(Q + (q,)))
    _Q[h] = Q
    return Q
def armcode(h, Q):
    if len(Q) == 1:
        r, k = comp(Q[0])
        if r == 2: return 1
        if r == 3: return 3 if h == Q[0] else 4
        return 2
    return 0
def rule(h, Q):
    return {0: 0, 1: 0, 2: 1, 3: 1, 4: 4}[armcode(h, Q)]

