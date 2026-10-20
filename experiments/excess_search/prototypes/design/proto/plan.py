"""Planner: K-relative build recipe for Rad(p) over the base K = F(C'), C' = shared base + 2-power components."""
import sys
from terms import *
from tower import Tower

def gf2_solve_basis(vectors):
    """Gaussian elimination helper: returns function expressing a target int in span(vectors)."""
    piv = {}   # pivot bit -> (row, combo)
    for i, v in enumerate(vectors):
        combo = 1 << i
        while v:
            hb = v.bit_length() - 1
            if hb in piv:
                pv, pc = piv[hb]; v ^= pv; combo ^= pc
            else:
                piv[hb] = (v, combo); break
        else:
            return None, combo   # dependency found: combo is a relation
    def solve(t):
        combo = 0
        while t:
            hb = t.bit_length() - 1
            if hb not in piv: raise ValueError('not in span')
            pv, pc = piv[hb]; t ^= pv; combo ^= pc
        return combo
    return solve, None

def build_K(Cset):
    """Return (degK, P_K int, zvals dict comp->int in theta_K power basis, theta description)."""
    if not Cset:
        return 1, 0b10, {}, ()   # K = F_2 = F_2[x]/(x); element bits: only bit0
    T = Tower(Cset)
    d = deg(Cset)
    maxs = [c for c in Cset if not any(c != o and c in cl_q(o) for o in Cset)]
    theta = [frozenset({c}) for c in sorted(maxs)]
    th = T.mono_elem(theta)
    pows = []; x = T.one()
    for i in range(d):
        pows.append(T.vec(x)); x = T.mul_rhs(x, theta)
    solve, rel = gf2_solve_basis(pows)
    assert solve is not None, 'theta_K does not generate K'
    top = solve(T.vec(x))       # theta^d = sum combo
    PK = (1 << d) | top
    z = {c: solve(T.vec(T.mono_elem([frozenset({c})]))) for c in Cset}
    return d, PK, z, tuple(sorted(maxs))

class Planner:
    def __init__(self, p):
        self.p = p
        self.S = cl_alpha(p)
        self.C = base_set(p)
        self.degK, self.PK, self.z, self.thK = build_K(self.C)
        self.ops = []; self.memo = {}
    def zval_monos(self, monos):
        """K-value of a sum of monomials all inside C (each monomial a product of comps)."""
        # products: compute via the tower over C to be safe
        if not monos: return 0
        if self.degK == 1:
            # K = F_2: only the empty monomial (=1) can occur
            assert all(len(m) == 0 for m in monos)
            return len(monos) & 1
        T = Tower(self.C)
        # express element in theta_K basis by re-solving (small)
        d = self.degK; pows = []; x = T.one()
        theta = [frozenset({c}) for c in self.thK]
        for i in range(d): pows.append(T.vec(x)); x = T.mul_rhs(x, theta)
        solve, _ = gf2_solve_basis(pows)
        return solve(T.vec(T.mono_elem(monos)))
    def emit(self, *op):
        self.ops.append(op); return len(self.ops) - 1
    def Mod(self, q):
        key = ('Mod', q)
        if key in self.memo: return self.memo[key]
        r, k = cprime(q)
        assert r > 2 and q not in self.C
        if k >= 2:
            lower = r**(k-1)
            if lower in self.C:
                reg = self.emit('BINOM', r, self.zval_monos([frozenset({lower})]))
            else:
                reg = self.emit('SPREAD', self.Mod(lower), r)
        else:
            if cl_alpha(r) <= self.C:
                reg = self.emit('BINOM', r, self.zval_monos(rhs(r)))
            else:
                reg = self.emit('SPREAD', self.Rad(r), r)
        self.memo[key] = reg; return reg
    def Rad(self, r, m=None):
        key = ('Rad', r, m)
        if key in self.memo: return self.memo[key]
        monos = alpha_monomials(r, m)
        inK = [mo for mo in monos if mo <= self.C]
        out = [mo for mo in monos if not mo <= self.C]
        if not out:
            reg = self.emit('LIN', self.zval_monos(inK)); self.memo[key] = reg; return reg
        regs = []
        for mo in out:
            (q,) = tuple(mo); regs.append(self.Mod(q))
        reg = regs[0]
        for other in regs[1:]:
            reg = self.emit('SUM', reg, other)
        v = self.zval_monos(inK)
        if v: reg = self.emit('SHIFT', reg, v)
        self.memo[key] = reg; return reg
    def plan_row(self):
        p = self.p; h = ordtwo(p); Q = Qset(h); m = rule(p, h, Q)
        # register for kappa_h (m=0) so all translates are shifts of it
        top = self.Rad(p, 0 if not getattr(self,'full',False) else m)
        E = deg(self.S)
        trans = []
        for mm in range(m+1):
            trans.append((mm, self.zval_monos(nimber_monomials(mm))))
        return top, E, h, m, trans
    def text(self):
        top, E, h, m, trans = self.plan_row()
        lines = [f'K {self.degK} {self.PK:x}', f'ROW {self.p} {E} {h} {m}']
        for i, op in enumerate(self.ops):
            name = op[0]
            if name in ('BINOM',): lines.append(f'{i} BINOM {op[1]} {op[2]:x}')
            elif name == 'SPREAD': lines.append(f'{i} SPREAD {op[1]} {op[2]}')
            elif name == 'SUM': lines.append(f'{i} SUM {op[1]} {op[2]}')
            elif name == 'LIN': lines.append(f'{i} LIN {op[1]:x}')
            elif name == 'SHIFT': lines.append(f'{i} SHIFT {op[1]} {op[2]:x}')
        lines.append(f'TOP {top}')
        for mm, v in trans: lines.append(f'TRANS {mm} {v:x}')
        return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    full = sys.argv[1] == '--full'
    for p in map(int, sys.argv[1+full:]):
        pl = Planner(p); pl.full = full
        sys.stdout.write(pl.text())
