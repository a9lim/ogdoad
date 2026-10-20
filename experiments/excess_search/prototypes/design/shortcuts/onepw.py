"""Check: for arm Z with Q={q1,q2}, chi_p(kappa) = chi_p(1 + chi1/chi2) at every row prime,
and w = chi1/chi2 satisfies w^(q1 q2) = alpha1^q2 / alpha2^q1 (in a field of degree E/(q1q2) up to 2-power comps)."""
import sys
from tower import *
for p in map(int, sys.argv[1:]):
    h = ordtwo(p); Q = Qset(h)
    T = Tower(Q); E = T.E; N = (1 << E) - 1
    c1, c2 = T.chi[Q[0]], T.chi[Q[1]]
    w = c1 / c2
    lhs = (c1 + c2) ** (N // p); rhs = (T.one + w) ** (N // p)
    chi2p = c2 ** (N // p) == T.one; chi1p = c1 ** (N // p) == T.one
    A = w ** (Q[0] * Q[1])
    degA = int(pari.poldegree(pari.minpoly(A)))
    print(p, Q, 'E', E, 'phase(kappa)==phase(1+w):', lhs == rhs, 'chi1,chi2 p-th powers:', chi1p, chi2p, 'deg(w^(q1q2))', degA, 'E/(q1q2)', E // (Q[0]*Q[1]), 'kappa nonpower:', lhs != T.one, flush=True)
