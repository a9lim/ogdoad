"""Numerical check of the crossed norm descent on small rows (arms O and Z).

For a row p, cross one odd component chi_R (R=r^a): chi_R = v * a with
v^R = c in k=F_(2^t) subset K=F_2(alpha_r), a in K.  Then for x = v a + u
(u = remaining components + rule nimber, all in M):
  N_{F_E/M}(x) = v^n f_a(u/v),  f_a = char poly of a over K cap M, n=[K:K cap M].
Checks: identity against the direct norm, Euler phase in M against direct
Euler in F_E, and the row verdict (and the forced translates).
"""
import sys, time
from tower import *
from reduce import reduced, tmin, vp
from math import gcd
X = pari('x')

def frob(z, k):  # z^(2^k)
    for _ in range(k): z = z * z
    return z

def check_row(p):
    h = ordtwo(p); Q = Qset(h); m = mrule(p)
    E0, (cost, how) = reduced(p, h, Q)
    T = Tower(Q, extra=(4,) if m >= 4 else ())
    E = T.E
    # pick crossed component and t from reduced()
    import re
    mm = re.match(r"cross\((\d+),\) M=(\d+) K=(\d+) t=\{\d+: (\d+)\}", how)
    assert mm, how
    R, degM, bK, t = map(int, mm.groups())
    r = min(factor(R)); aexp = vp(R, r); b = bdeg(r); assert b == bK
    alpha = T.alpha(r)
    assert frob(alpha, b) == alpha
    v_r = vp((1 << b) - 1, r); mod = r ** min(aexp, v_r)
    e = ((1 << b) - 1) // ((1 << t) - 1)
    w = pow(e, -1, mod)
    c = alpha ** (e * w)
    assert frob(c, t) == c
    beta = alpha / c
    z = pari.sqrtn(beta, R)
    # move root into K
    g = T.g
    zeta = g ** (((1 << E) - 1) // R)
    for j in range(R):
        if frob(z, b) == z: break
        z = z * zeta
    else:
        raise AssertionError('no root in K')
    a = z
    assert a ** R == beta
    chi = T.chi[R]
    v = chi / a
    assert v ** R == c and frob(v, R * t) == v
    # rest u: other components + rule nimber
    rest = [q for q in Q if q != R]
    gKM = gcd(b, degM)
    n = b // gKM
    # char poly of a over K cap M (degree n): conjugates a^(2^(gKM*j))
    conj = [a]
    for j in range(1, n): conj.append(frob(conj[-1], gKM))
    fa = pari(1)
    for s in conj: fa = fa * (X - s)
    for coef in pari.Vec(fa):
        assert frob(coef, gKM) == coef   # coefficients in K cap M
    results = []
    for mt in sorted(set([m] + list(range(m)))):
        u = T.kappa(rest) + T.nimber(mt)
        x = chi + u
        direct_norm = x ** (((1 << E) - 1) // ((1 << degM) - 1))
        if u == 0 * T.one:
            W = v ** n * pari.subst(fa, 'x', 0 * T.one)   # f_a(0)
        else:
            W = v ** n * pari.subst(fa, 'x', u / v)
        assert W == direct_norm, 'identity failed'
        assert frob(W, degM) == W
        ph_direct = x ** (((1 << E) - 1) // p) == T.one
        ph_cross = W ** (((1 << degM) - 1) // p) == T.one
        assert ph_direct == ph_cross
        results.append((mt, 'power' if ph_direct else 'NONPOWER'))
    return dict(p=p, h=h, Q=Q, arm=arm(h, Q), E=E, M=degM, K=b, t=t, n=n, rule=m, translates=results)

if __name__ == '__main__':
    for p in map(int, sys.argv[1:]):
        t0 = time.time()
        print(check_row(p), f'{time.time()-t0:.1f}s', flush=True)
