"""Reduced working degrees under the crossing descent, per census row."""
import sys, os, pickle, math, collections
sys.path.insert(0, '/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search')
N = int(sys.argv[1]) if len(sys.argv) > 1 else 10**5
import census  # computes for census.N (argv) -- we import functions only
from census import ordtwo, Qset, factor, b as bdeg, dq, lcm, arm, rule
from math import gcd

def vp(n, r):
    v = 0
    while n % r == 0: n //= r; v += 1
    return v

def tmin(r, bb, extra=1):
    """least t | bb with v_r(2^t-1)=v_r(2^bb-1) and extra | t (None if impossible)."""
    fr = ordtwo(r)
    base = lcm(fr * r ** vp(bb, r), extra)
    if bb % base: return None
    return base

def reduced(p, h, Q):
    """Return (E, Ered, details) for the best single/all crossing we model."""
    E = 1
    for q in Q: E = lcm(E, dq(q))
    odd = [q for q in Q if q % 2]
    even = [q for q in Q if q % 2 == 0]
    best = (E, 'direct')
    # cross every odd component; t_i grown until h | deg M
    from itertools import combinations
    for k in range(1, len(odd) + 1):
        for S in combinations(odd, k):
            rest = [q for q in Q if q not in S]
            t = {}
            ok = True
            for q in S:
                r = min(factor(q)); bb = bdeg(r)
                tt = tmin(r, bb)
                if tt is None: ok = False; break
                t[q] = tt
            if not ok: continue
            def degM():
                d = 1
                for q in S: d = lcm(d, q * t[q])
                for q in rest: d = lcm(d, dq(q))
                return d
            # repair divisibility h | deg M
            for (ell, e) in factor(h).items():
                if degM() % (ell ** e) == 0: continue
                fixed = False
                for q in S:
                    r = min(factor(q)); bb = bdeg(r)
                    cand = lcm(t[q], ell ** e)
                    if bb % cand == 0:
                        t[q] = cand; fixed = True; break
                if not fixed: ok = False; break
            if not ok: continue
            dM = degM()
            dK = 1
            for q in S: dK = lcm(dK, bdeg(min(factor(q))))
            for q in rest: dK = lcm(dK, dq(q))  # rest must live with K-side too (needed for charpoly coefficients over K cap M)
            # the norm-form needs the joint conjugates of the a_i over K_all cap M: work field K_all = lcm(b_i)
            dKall = 1
            for q in S: dKall = lcm(dKall, bdeg(min(factor(q))))
            cost = max(dM, dKall)
            if cost < best[0]:
                best = (cost, f'cross{tuple(S)} M={dM} K={dKall} t={t}')
    return E, best

if __name__ == '__main__':
    rows = pickle.load(open(f'/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/rows_1000000.pkl', 'rb'))
    rows = [r for r in rows if 727 < r[0] <= N]
    out = []
    for (p, h, Q, a, m, E) in rows:
        if a in ('C', 'D', 'ZF'):
            out.append((p, a, E, E, 'skip')); continue
        E2, (c, how) = reduced(p, h, Q)
        assert E2 == E or m == 4, (p, E, E2)
        out.append((p, a, E, c, how))
    pickle.dump(out, open(f'reduced_{N}.pkl', 'wb'))
    for (p, a, E, c, how) in out[:25]:
        print(p, a, E, c, how)
    for B in (10**4, 10**5, 10**6, 10**7, 10**8):
        s0 = sum(1 / r[0] for r in out if r[2] <= B)
        s1 = sum(1 / r[0] for r in out if r[3] <= B)
        n0 = sum(1 for r in out if r[2] <= B); n1 = sum(1 for r in out if r[3] <= B)
        print(f'B={B:>9}: direct rows {n0:5d} mass {s0:.4f} P={1-math.exp(-s0):.3f} | reduced rows {n1:5d} mass {s1:.4f} P={1-math.exp(-s1):.3f}')
    tot = sum(1 / r[0] for r in out); print('total mass', round(tot, 4), 'P', round(1 - math.exp(-tot), 3))
    for A in ('O', 'Z'):
        for B in (10**5, 10**6, 10**7):
            s0 = sum(1 / r[0] for r in out if r[1] == A and r[2] <= B)
            s1 = sum(1 / r[0] for r in out if r[1] == A and r[3] <= B)
            print(A, B, round(s0, 4), round(s1, 4), 'of', round(sum(1 / r[0] for r in out if r[1] == A), 4))
