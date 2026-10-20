"""Check the multi-component crossing used by reduce.py (cross(q1,q2) cases)."""
import sys, re, time
from tower import *
from reduce import reduced, vp
from math import gcd
def frob(z, k):
    for _ in range(k): z = z * z
    return z
def cross_comp(T, R, t):
    r = min(factor(R)); aexp = vp(R, r); b = bdeg(r)
    alpha = T.alpha(r); E = T.E
    mod = r ** min(aexp, vp((1 << b) - 1, r))
    e = ((1 << b) - 1) // ((1 << t) - 1); w = pow(e, -1, mod)
    c = alpha ** (e * w); beta = alpha / c
    z = pari.sqrtn(beta, R); zeta = T.g ** (((1 << E) - 1) // R)
    for _ in range(R):
        if frob(z, b) == z: break
        z = z * zeta
    else: raise AssertionError
    assert z ** R == beta
    v = T.chi[R] / z
    assert v ** R == c and frob(v, R * t) == v
    return z, v, b
for p in map(int, sys.argv[1:]):
    t0 = time.time()
    h = ordtwo(p); Q = Qset(h); m = mrule(p)
    E0, (cost, how) = reduced(p, h, Q)
    mm = re.match(r"cross\(([\d, ]+)\) M=(\d+) K=(\d+) t=\{(.*)\}", how)
    S = [int(s) for s in mm.group(1).split(',') if s.strip()]
    degM = int(mm.group(2)); Kall = int(mm.group(3))
    ts = {int(k): int(v) for k, v in (kv.split(':') for kv in mm.group(4).split(','))}
    T = Tower(Q); E = T.E
    from census import lcm
    assert lcm(Kall, degM) == E, (Kall, degM, E)
    parts = {R: cross_comp(T, R, ts[R]) for R in S}
    rest = [q for q in Q if q not in S]
    u = T.kappa(rest) + T.nimber(m)
    g = gcd(Kall, degM); n = Kall // g
    N = T.one
    for j in range(n):
        term = u
        for R, (a, v, b) in parts.items():
            term = term + v * frob(a, g * j)
        N = N * term
    x = T.kappa(Q) + T.nimber(m)
    direct = x ** (((1 << E) - 1) // ((1 << degM) - 1))
    ok = (N == direct)
    ph = (N ** (((1 << degM) - 1) // p) == T.one)
    print(p, Q, 'E', E, 'M', degM, 'Kall', Kall, 'n', n, 'identity', ok, 'row nonpower', not ph, f'{time.time()-t0:.1f}s', flush=True)
