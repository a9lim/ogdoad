"""Trivial tower: the term algebra itself in its monomial basis (numpy).  Independent oracle."""
import numpy as np
from terms import *

class Tower:
    def __init__(self, S, alpha_override=None):
        self.comps = topo(S)
        self.idx = {c: i for i, c in enumerate(self.comps)}
        self.shape = tuple(ell(c) for c in self.comps)
        self.rel = {c: rhs(c) for c in self.comps}
        for c in self.comps:
            for mono in self.rel[c]:
                assert all(x in self.idx and self.idx[x] < self.idx[c] for x in mono), (c, mono)
    def zero(self): return np.zeros(self.shape, dtype=np.uint8)
    def one(self):
        x = self.zero(); x[(0,)*len(self.shape)] = 1; return x
    def _sl(self, i, j):
        s = [slice(None)]*len(self.shape); s[i] = slice(j, j+1); return tuple(s)
    def mul_comp(self, x, c):
        i = self.idx[c]; l = self.shape[i]; a = self.rel[c]
        out = np.empty_like(x)
        if l == 2:
            x0 = x[self._sl(i, 0)]; x1 = x[self._sl(i, 1)]
            out[self._sl(i, 0)] = self.mul_rhs(x1, a)
            out[self._sl(i, 1)] = x0 ^ x1
        else:
            s_hi = [slice(None)]*len(self.shape); s_hi[i] = slice(1, l)
            s_lo = [slice(None)]*len(self.shape); s_lo[i] = slice(0, l-1)
            out[tuple(s_hi)] = x[tuple(s_lo)]
            out[self._sl(i, 0)] = self.mul_rhs(x[self._sl(i, l-1)], a)
        return out
    def mul_mono(self, x, mono):
        for c in mono: x = self.mul_comp(x, c)
        return x
    def mul_rhs(self, x, monos):
        acc = np.zeros_like(x)
        for mono in monos: acc ^= self.mul_mono(x, mono)
        return acc
    def vec(self, x):
        b = np.packbits(x.reshape(-1), bitorder='little').tobytes()
        return int.from_bytes(b, 'little')
    def mono_elem(self, monos):
        return self.mul_rhs(self.one(), monos)

def bm_gf2(bits):
    """Berlekamp-Massey over GF(2); returns min poly as int (bit i = coeff of X^i)."""
    Cc = 1; B = 1; L = 0; m = 1; Srev = 0
    for N, sN in enumerate(bits):
        Srev = (Srev << 1) | sN
        d = (Cc & Srev).bit_count() & 1
        if d:
            T = Cc; Cc ^= B << m
            if 2*L <= N:
                L = N + 1 - L; B = T; m = 1
            else: m += 1
        else: m += 1
    # reverse connection polynomial to get min poly of degree L
    poly = 0
    for i in range(L+1):
        if (Cc >> i) & 1: poly |= 1 << (L - i)
    return poly, L

def oracle_minpoly(S, monos):
    """min poly over F_2 of the element sum(monos) in F(S), via BM on constant coefficients."""
    T = Tower(S); E = deg(S)
    x = T.one(); bits = []
    z = (0,)*len(T.shape)
    for _ in range(2*E):
        bits.append(int(x[z])); x = T.mul_rhs(x, monos)
    return bm_gf2(bits)
