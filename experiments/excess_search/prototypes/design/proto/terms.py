"""Term-algebra structure (independent of census.py's Q/degree code paths only where noted)."""
import sys, os, itertools
from functools import lru_cache
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..'))
_argv = sys.argv; sys.argv = ['x', '200000']
import census as C
sys.argv = _argv
factor, ordtwo, Qset, rule, primes = C.factor, C.ordtwo, C.Qset, C.rule, C.primes

def cprime(q):
    (r, k), = factor(q).items(); return r, k

def rule_m(r):
    h = ordtwo(r); Q = Qset(h); return rule(r, h, Q)

def ell(q): return cprime(q)[0]

@lru_cache(None)
def cl_q(q):
    r, k = cprime(q)
    if r == 2: return frozenset(2**j for j in range(1, k+1))
    return frozenset(r**j for j in range(1, k+1)) | cl_alpha(r)

@lru_cache(None)
def cl_alpha(r):
    h = ordtwo(r); Q = Qset(h); m = rule(r, h, Q)
    s = set()
    for q in Q: s |= cl_q(q)
    if m >= 2:
        a = C.d_finite(m).bit_length() - 1
        s |= {2**j for j in range(1, a+1)}
    return frozenset(s)

def deg(S):
    d = 1
    for q in S: d *= ell(q)
    return d

def nimber_monomials(m):
    """finite nimber m < 16 as list of monomials (frozensets of 2-power labels)."""
    assert 0 <= m < 16
    basis = {1: frozenset(), 2: frozenset({2}), 4: frozenset({4}), 8: frozenset({2, 4})}
    return [basis[b] for b in (1, 2, 4, 8) if m & b]

def rhs(q, m_override=None):
    """Defining relation right-hand side for component q as list of monomials."""
    r, k = cprime(q)
    if r == 2:
        return [frozenset(2**j for j in range(1, k))]
    if k >= 2:
        return [frozenset({r**(k-1)})]
    h = ordtwo(r); Q = Qset(h)
    m = rule(r, h, Q) if m_override is None else m_override
    return [frozenset({x}) for x in Q] + nimber_monomials(m)

def alpha_monomials(p, m=None):
    h = ordtwo(p); Q = Qset(h)
    if m is None: m = rule(p, h, Q)
    return [frozenset({x}) for x in Q] + nimber_monomials(m)

@lru_cache(None)
def shared_base(r):
    """union of pairwise branch-closure intersections over every Sum node in cl(alpha_r)."""
    h = ordtwo(r); Q = Qset(h); m = rule(r, h, Q)
    br = [cl_q(q) for q in Q]
    if m >= 2: br.append(frozenset({2, 4}))
    Cs = set()
    for x, y in itertools.combinations(br, 2): Cs |= x & y
    for q in Q:
        rr, k = cprime(q)
        if rr > 2: Cs |= shared_base(rr)
    return frozenset(Cs)

def base_set(p):
    S = cl_alpha(p)
    return frozenset(shared_base(p) | {q for q in S if q % 2 == 0})

def topo(S):
    return sorted(S, key=lambda q: (deg(cl_q(q)), q))
