"""Small explicit term-algebra models over PARI FFELT (for experiments only).

Builds F_{2^E} for the closure of a component set, embeds every component once
(shared components are one element), and exposes kappa_Q, alpha_r, etc.
Assumes the 0/1/4 rule for all ancestor rows (exact OEIS data for p<=709).
"""
import sys, os
sys.path.insert(0, '/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search')
sys.setrecursionlimit(100000)
import cypari2
pari = cypari2.Pari()
pari.allocatemem(4 * 10**9)
from census import ordtwo, Qset, rule, arm, factor, b as bdeg, dq, lcm
from math import gcd

def mrule(r):
    h = ordtwo(r); return rule(r, h, Qset(h))

def closure(Q, acc=None):
    """All components needed to define kappa_Q (downward closed)."""
    acc = set() if acc is None else acc
    for q in Q:
        add_comp(q, acc)
    return acc

def add_comp(q, acc):
    if q in acc: return
    (r, k), = factor(q).items()
    if r == 2:
        for j in range(1, k):
            add_comp(2 ** j, acc)
    else:
        if k > 1: add_comp(r ** (k - 1), acc)
        add_alpha(r, acc)
    acc.add(q)

def add_alpha(r, acc):
    h = ordtwo(r); Q = Qset(h); m = mrule(r)
    closure(Q, acc)
    for q in nimber_comps(m): add_comp(q, acc)

def nimber_comps(m):
    out = []
    i = 0
    while (1 << (1 << i)) <= max(m, 1) and m > 1:
        out.append(2 ** (i + 1)); i += 1
    return out

def compdeg(q):
    return dq(q)

class Tower:
    def __init__(self, Q, extra=()):
        comps = closure(Q)
        for q in extra: add_comp(q, comps)
        self.E = 1
        for q in comps: self.E = lcm(self.E, compdeg(q))
        self.g = pari(f"ffgen(ffinit(2,{self.E}),'t)")
        self.one = self.g ** 0
        self.chi = {}
        # topological order: sort by degree then value works since deps have smaller degree
        order = sorted(comps, key=lambda q: (compdeg(q), q))
        for q in order:
            self.embed(q)

    def nimber(self, m):
        """Finite nimber m as an element (needs its 2-power components)."""
        x = 0 * self.one
        i = 0
        while m:
            if m & 1:
                t = self.one
                j = 0
                while (1 << j) <= i:
                    if (i >> j) & 1:
                        t = t * self.chi[2 ** (j + 1)]
                    j += 1
                x = x + t
            m >>= 1; i += 1
        return x

    def kappa(self, Q):
        x = 0 * self.one
        for q in Q: x = x + self.chi[q]
        return x

    def alpha(self, r):
        h = ordtwo(r)
        return self.kappa(Qset(h)) + self.nimber(mrule(r))

    def embed(self, q):
        (r, k), = factor(q).items()
        X = pari('x')
        if r == 2:
            a = self.one
            for j in range(1, k): a = a * self.chi[2 ** j]
            y = self.as_root(a)
            assert y ** 2 + y == a
        else:
            a = self.chi[r ** (k - 1)] if k > 1 else self.alpha(r)
            y = pari.sqrtn(a, r)
            assert y ** r == a
        self.chi[q] = y

    def trace(self, z):
        s = z; w = z
        for _ in range(self.E - 1):
            w = w * w; s = s + w
        return s

    def as_root(self, a):
        """root of y^2+y=a (Tr(a)=0) via a trace-one element tau."""
        if not hasattr(self, 'tau'):
            j = 1
            while True:
                z = self.g ** j
                if self.trace(z) == self.one: break
                j += 1
            self.tau = z
        # y = sum_{i=1}^{E-1} (sum_{j=0}^{i-1} tau^(2^j)) a^(2^i)
        y = 0 * self.one; S = 0 * self.one; tj = self.tau; ai = a
        for i in range(1, self.E):
            S = S + tj; tj = tj * tj
            ai = ai * ai
            y = y + S * ai
        return y

    def is_power(self, x, ell):
        N = (1 << self.E) - 1
        assert N % ell == 0
        return x ** (N // ell) == self.one

if __name__ == '__main__':
    import time
    oeis = {}
    for line in open('/Users/a9lim/Work/ogdoad/src/scalar/big/ordinal/b380496.txt'):
        a, v = line.split(); oeis[int(a)] = int(v)
    # the b-file is indexed by n (n-th prime?) -- map
    print(list(oeis.items())[:5])
