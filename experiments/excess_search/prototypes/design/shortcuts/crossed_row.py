"""Exact crossed-descent test for an arm-O row (singleton Q={R}), never building F_E.

K = F_2(alpha_r) (degree b, built by Tower on the parent's component set),
k = F_(2^t) subset K, H = F_(2^(R t)) built independently with k embedded.
chi_R = v * a,  v^R = c in k,  a = (alpha/c)^(1/R) in K.
N_{F_E/H}(chi_R + m) = v^n f_a(m/v)   (n = b/t, f_a = char poly of a over k)
Row p: rule value m=1 must be a non-p-th power; m=0 is the forced translate.
"""
import sys, time
from tower import *
from reduce import tmin, vp
from census import lcm
X = pari('x')
def frob(z, k):
    for _ in range(k): z = z * z
    return z
def crossed(p, verbose=True):
    t0 = time.time()
    h = ordtwo(p); Q = Qset(h); m = mrule(p); assert arm(h, Q) == 'O', (p, Q)
    R = Q[0]; r = min(factor(R)); aexp = vp(R, r); b = bdeg(r); s = h // R
    t = tmin(r, b, s); assert t and b % t == 0 and lcm(R * t, 1) % h == 0
    n = b // t
    # K: the parent's field, containing alpha_r
    hr = ordtwo(r); Qr = Qset(hr); mr = mrule(r)
    TK = Tower(Qr, extra=(4,) if mr >= 4 else ())
    assert TK.E == b, (TK.E, b)
    alpha = TK.alpha(r)
    mod = r ** min(aexp, vp((1 << b) - 1, r))
    e = ((1 << b) - 1) // ((1 << t) - 1); w = pow(e, -1, mod)
    c = alpha ** (e * w); assert frob(c, t) == c
    beta = alpha / c
    a = pari.sqrtn(beta, R); assert a ** R == beta          # exact check
    tK = time.time() - t0
    conj = [a]
    for j in range(1, n): conj.append(frob(conj[-1], t))
    assert frob(conj[-1], t) == a                            # orbit closes: deg a | n over k
    fa = pari(1)
    for z in conj: fa = fa * (X - z)
    coeffs = list(pari.Vec(fa))                              # leading first
    # abstract k and its embedding into K
    kg = pari(f"ffgen(ffinit(2,{t}),'kk)")
    mK = pari.ffembed(kg, TK.g)
    inv = pari.ffinvmap(mK)
    ck = pari.ffmap(inv, c)
    coeffs_k = [pari.ffmap(inv, z) for z in coeffs]
    for z, zk in zip(coeffs, coeffs_k):
        assert pari.ffmap(mK, zk) == z                       # coefficients really lie in k
    tf = time.time() - t0
    # H = k[V]/(V^R - c) as a tower (no absolute field construction)
    Vv = pari('V')
    modH = Vv ** R - ck
    one = pari.Mod(kg ** 0, modH)
    def W(mval):   # V^n f_a(mval/V) = sum_i coeffs[i] mval^(n-i) V^i (coeffs[0] leading)
        acc = 0 * kg
        polyV = sum((coeffs_k[i] * (kg ** 0 * mval) ** (n - i)) * Vv ** i for i in range(n + 1))
        return pari.Mod(polyV, modH)
    # sanity: H is a field of degree R t  <=>  c not an r-th power in k
    assert ck ** (((1 << t) - 1) // r) != kg ** 0
    th = time.time() - t0
    N = (1 << (R * t)) - 1
    out = {}
    for mm in range(m + 1):
        if mm >= 2: break
        Wm = W(mm)
        out[mm] = 'power' if Wm ** (N // p) == one else 'NONPOWER'
    tt = time.time() - t0
    if verbose:
        print(f'p={p} h={h} Q={Q} E={R*b} -> K={b} t={t} n={n} H={R*t}; translates {out}; '
              f'times K {tK:.1f}s fa {tf:.1f}s H {th:.1f}s total {tt:.1f}s', flush=True)
    return out
if __name__ == '__main__':
    for p in map(int, sys.argv[1:]):
        crossed(p)
