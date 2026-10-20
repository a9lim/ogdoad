"""Discrete-log coordinates of translates kappa + c (c a finite nimber < 16) at a prime ell.
Prints, for each c, log of (kappa+c)^((2^E-1)/ell) in Z/ell w.r.t. a fixed generator of mu_ell."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)) + '/..')
from tower_copy import Tower, pari
def coords(Q, extra, ell, cmax=16):
    T = Tower(Q, extra=extra); E = T.E; N = (1 << E) - 1
    assert N % ell == 0
    kap = T.kappa(Q)
    # generator of mu_ell
    g = T.g; z = g ** (N // ell); j = 1
    while z == T.one: j += 1; z = (g ** j) ** (N // ell)
    table = {}; w = T.one
    for i in range(ell): table[str(w)] = i; w = w * z
    out = {}
    for c in range(cmax):
        x = kap + T.nimber(c)
        if x == 0 * T.one: out[c] = None; continue
        out[c] = table[str(x ** (N // ell))]
    return E, out
for Q, extra, ell in [((9,), (4,), 19), ((9,), (4,), 73), ((5,), (), 41), ((5,), (), 11)]:
    E, out = coords(Q, extra, ell)
    print(Q, extra, 'E', E, 'ell', ell, out, flush=True)
