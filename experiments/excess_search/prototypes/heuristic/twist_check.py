"""Fermat-twist lemma check: for a singleton odd component chi = chi_{r^a} with r a Fermat
prime, translates chi + c (c in mu_r, a finite nimber) have the same ell-th power status as
chi + 1 at every prime ell | 2^E - 1 with ell != r (derived: chi + c = c * sigma(chi + 1))."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + '/..')
from tower_copy import Tower, pari
from census import factor
def check(Q):
    T = Tower(Q)
    E = T.E; N = (1 << E) - 1
    (r, a), = factor(Q[0]).items()
    chi = T.chi[Q[0]]
    # mu_r inside the finite nimbers: F_{2^{f(r)}}, f(r) a power of two; use chi_{f(r)} tower element
    f = 1
    while pow(2, f, r) != 1: f += 1
    g = T.chi[f] if f > 1 else T.one   # chi_{2^k} generates F_{2^{2^k}} = F_{2^f}
    # find an element of order r in F_{2^f} = F_2(g)
    M = (1 << f) - 1
    x = g
    while True:
        c = x ** (M // r)
        if c != T.one: break
        x = x * g + T.one
    ells = [l for l in map(int, pari.factor(N)[0]) if l != r]
    out = []
    for l in ells:
        s1 = (chi + T.one) ** (N // l) == T.one
        sc = [((chi + c**i) ** (N // l) == T.one) for i in range(1, r)]
        out.append((l, s1, all(s == s1 for s in sc)))
    print(Q, 'E', E, 'r', r, [(l, s1, ok) for l, s1, ok in out if l < 10**7][:20], 'all tied:', all(ok for _, _, ok in out))
for Q in [(3,), (9,), (27,), (5,), (25,), (17,)]:
    try: check(Q)
    except Exception as e: print(Q, 'ERR', e)
