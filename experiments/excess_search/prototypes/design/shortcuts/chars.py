"""Power-residue statistics of selected elements at all small primes ell | 2^E-1.

For each distinct selected element (by Q) with E <= EMAX, record for each prime
ell <= LMAX with f(ell) | E whether the element is an ell-th power.  Random
model: probability 1/ell each.  Rows (Q(f(ell)) == Q, ell != forced) are
flagged separately.
"""
import sys, pickle, time, math, collections
from tower import *
EMAX = int(sys.argv[1]); LMAX = int(sys.argv[2]); OUT = sys.argv[3]
rows = pickle.load(open('/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/rows_1000000.pkl', 'rb'))
primes = [r[0] for r in rows if r[0] <= LMAX]
fl = {r[0]: r[1] for r in rows}
Qof = {r[0]: r[2] for r in rows}
seen = {}
for (p, h, Q, a, m, E) in rows:
    if E > EMAX or a in ('ZF',): continue
    key = (Q, m)
    seen.setdefault(key, (a, E))
res = []
t0 = time.time()
for (Q, m), (a, E) in sorted(seen.items(), key=lambda kv: kv[1][1]):
    T = Tower(Q, extra=(4,) if m >= 4 else ())
    assert T.E == E, (Q, m, T.E, E)
    kap = T.kappa(Q)
    elems = {'sel': kap + T.nimber(m)}          # the rule element
    if m >= 1: elems['kap+0'] = kap             # forced translate (power at rows)
    elems['sel+1'] = kap + T.nimber(m ^ 1) if m != 1 else None
    if E % 2 == 0:
        elems['kap+w'] = kap + T.nimber(2)      # omega translate (non-selected)
    N = (1 << E) - 1
    for name, x in elems.items():
        if x is None: continue
        for ell in primes:
            if E % fl[ell]: continue
            isrow = (Qof[ell] == Q)
            pw = (x ** (N // ell) == T.one)
            res.append(dict(Q=Q, m=m, arm=a, E=E, elem=name, ell=ell, f=fl[ell], row=isrow, power=bool(pw)))
    print(Q, m, a, E, f'{time.time()-t0:.1f}s', flush=True)
pickle.dump(res, open(OUT, 'wb'))
