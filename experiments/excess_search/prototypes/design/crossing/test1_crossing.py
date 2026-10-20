"""T1: single-level crossing identity vs brute-force full-field norm.

For a singleton-top row (h, R, alpha in K = F_2(alpha) of degree b):
  brute:   T  = N_{F/F_{2^h}}(1+chi),  F = F_2[X]/P_alpha(X^R)
  crossed: k = F_{2^t} (t = lcm(f(r), s) with v_r(t)=v_r(b)), K = k[Y]/g(Y) for a
           factor g of P_alpha over k,  c = N_{K/k}(alpha)^w,  a = (alpha/c)^{1/R},
           f_a = charpoly of a over k,  W = V^D f_a(1/V) in H = k[V]/(V^R - c),
           T' = N_{H/F_{2^h}}(W).
Claim (checked here): minpoly_{F_2}(T) == minpoly_{F_2}(T')  (Frobenius conjugates).
"""
import sys, os, time, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xlib import *
import flint

def lcm(a, b): return a * b // math.gcd(a, b)

def kth_root(x, R, N, one, ctx=None):
    """An R-th root of x in a cyclic group of order N (x assumed an R-th power).
    Works prime factor by prime factor of R; exact (verified by caller)."""
    # factor R
    fac = {}
    n = R; d = 2
    while d * d <= n:
        while n % d == 0:
            fac[d] = fac.get(d, 0) + 1; n //= d
        d += 1
    if n > 1: fac[n] = fac.get(n, 0) + 1
    y = x
    for r, a in fac.items():
        for _ in range(a):
            y = prime_root(y, r, N, one, ctx)
    return y

def prime_root(x, r, N, one, ctx=None):
    """r-th root (r prime) of an r-th power x in a cyclic group of order N."""
    e = 0; q = N
    while q % r == 0:
        q //= r; e += 1
    if e == 0:
        return x ** pow(r, -1, N)
    l = pow(r, -1, q)
    s0 = x ** l
    eps = x ** ((r * l - 1) % N)       # lies in the r-Sylow
    import random
    rnd = random.Random(12345)
    while True:
        if ctx is not None:
            cand = ctx([rnd.randrange(2) for _ in range(ctx.degree())])
        else:
            cand = (x + one) ** rnd.randrange(1, N)
        if cand == 0: continue
        gen = cand ** q
        if gen ** (r ** (e - 1)) != one:
            break
    re_ = r ** e
    target = eps ** (N - 1)            # eps^{-1}
    gamma = gen ** (r ** (e - 1))      # order r
    table = {}
    cur = one
    for i in range(r):
        table[str(cur)] = i
        cur = cur * gamma
    j = 0
    for i in range(e):
        hh = (target * gen ** ((re_ - j) % re_)) ** (r ** (e - 1 - i))
        j += table[str(hh)] * r ** i
    assert gen ** j == target
    assert j % r == 0, "not an r-th power"
    root = s0 * gen ** (j // r)
    assert root ** r == x
    return root

def coord0_F(e):
    lst = e.to_list()
    return int(lst[0]) & 1 if lst else 0

def run_row(name, P_alpha, R, r, h, rows, t_override=None):
    b = deg(P_alpha)
    n = R * b
    t0 = time.time()
    # ---- brute force in F
    F = field(inflate(P_alpha, R), 'X')
    X = F.gen()
    T = (F.one() + X) ** ((2 ** n - 1) // (2 ** h - 1))
    mT = minpoly_F2_of(T, coord0_F)
    tb = time.time() - t0
    # ---- crossing
    s = h // R
    t = lcm(ordtwo(r), s)
    t = lcm(t, r ** vr(b, r))
    if t_override: assert t_override % t == 0; t = t_override
    assert b % t == 0
    D = b // t
    assert vr(2 ** t - 1, r) == vr(2 ** b - 1, r)
    k = flint.fq_default_ctx(2, t, 'l')
    Rk = flint.fq_default_poly_ctx(k)
    Pk = Rk([k((P_alpha >> i) & 1) for i in range(b + 1)])
    fac = Pk.factor()[1]
    g = fac[0][0].monic()
    assert g.degree() == D
    Y = Rk.gen()
    def kmul(u, v): return u.mul_mod(v, g)
    normY = g[0]                          # N_{K/k}(Y) = g(0) in char 2
    S = (2 ** b - 1) // (2 ** t - 1)
    gK = math.gcd(R, 2 ** b - 1)
    w = pow(S % gK, -1, gK) if gK > 1 else 0
    c = normY ** w
    z = Y * Rk(c ** -1)
    # norm-split root:  x R + y S = 1
    y = pow(S % R, -1, R)
    xexp = (1 - y * S) // R
    assert xexp * R + y * S == 1
    Nz = (z.pow_mod(S, g))
    assert Nz.degree() <= 0
    Nz = Nz[0]
    nu = kth_root(Nz ** y, R, 2 ** t - 1, k.one(), k)
    zinv = z.inverse_mod(g)
    a = zinv.pow_mod(-xexp, g) * Rk(nu) % g
    assert a.pow_mod(R, g) == z % g, "root check failed"
    # charpoly of a over k by BM on coefficient-0 sequence, verified
    seq = []
    cur = Rk.one()
    for i in range(2 * D + 2):
        seq.append(cur[0] if cur.degree() >= 0 else k.zero())
        cur = kmul(cur, a)
    C, L = berlekamp_massey(seq, k.one(), k.zero())
    assert L == D, (L, D)
    Cl = C + [k.zero()] * (L + 1 - len(C))
    fa = [Cl[L - i] for i in range(L + 1)]       # fa[i] = coeff of X^i
    # verify fa(a) = 0
    acc = Rk.zero()
    for i in range(D, -1, -1):
        acc = (acc * a + Rk(fa[i])) % g
    assert acc == 0
    # W = V^D fa(1/V) = sum_i fa[i] V^{D-i}  in H = k[V]/(V^R - c)
    Hmod = Rk.gen() ** R - Rk(c)
    W = Rk([fa[D - j] for j in range(D + 1)]) % Hmod
    Tp = W.pow_mod((2 ** (R * t) - 1) // (2 ** h - 1), Hmod)
    def coord0_H(e):
        if e.degree() < 0: return 0
        lst = e[0].to_list()
        return int(lst[0]) & 1 if lst else 0
    class Hel:
        pass
    # minpoly of Tp via BM on coord0_H sequence (wrap ops)
    seq = []
    cur = Rk.one()
    for i in range(2 * h + 2):
        seq.append(flint.nmod(coord0_H(cur), 2))
        cur = cur.mul_mod(Tp, Hmod)
    C2, L2 = berlekamp_massey(seq, flint.nmod(1, 2), flint.nmod(0, 2))
    bits = 0
    C2 = C2 + [flint.nmod(0, 2)] * (L2 + 1 - len(C2))
    for i in range(L2 + 1):
        if int(C2[i]): bits |= 1 << (L2 - i)
    # verify
    acc = Rk.zero()
    for e_ in range(L2, -1, -1):
        acc = acc.mul_mod(Tp, Hmod)
        if (bits >> e_) & 1: acc = acc + Rk.one()
    assert acc % Hmod == 0
    tc = time.time() - t0 - tb
    ok = bits == mT
    # Euler symbols for the rows with this h
    sym = {}
    for p in rows:
        sym[p] = (T ** ((2 ** h - 1) // p) != F.one())
    print(f"{name}: h={h} R={R} b={b} n={n} t={t} D={D} |H|={R*t}  minpoly match={ok} "
          f"deg={deg(mT)}  nonres(rule holds)={sym}  brute {tb:.1f}s crossed {tc:.1f}s")
    assert ok
    return T

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == 'bigt':
        run_row("p=179 (h=178) t=44", P_alpha89(), 89, 89, 178, [179], 44)
        run_row("p=179 (h=178) t=110", P_alpha89(), 89, 89, 178, [179], 110)
        run_row("p=727 (h=121) t=20 (D=1)", P_alpha11(), 121, 11, 121, [727], 20)
    else:
        run_row("p=23,89 (h=11)", P_alpha11(), 11, 11, 11, [23, 89])
        run_row("p=727 (h=121)", P_alpha11(), 121, 11, 121, [727])
        run_row("p=179 (h=178)", P_alpha89(), 89, 89, 178, [179])
