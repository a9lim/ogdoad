"""Parallel chunked version of chars.py: worker i of W, appends results per element."""
import sys, pickle, time
from tower import *
EMAX = int(sys.argv[1]); LMAX = int(sys.argv[2]); W = int(sys.argv[3]); I = int(sys.argv[4])
rows = pickle.load(open('/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/rows_1000000.pkl', 'rb'))
primes = [r[0] for r in rows if r[0] <= LMAX]
fl = {r[0]: r[1] for r in rows}
seen = {}
for (p, h, Q, a, m, E) in rows:
    if E > EMAX or a == 'ZF': continue
    seen.setdefault((Q, m), (a, E))
items = sorted(seen.items(), key=lambda kv: kv[1][1])
mine = items[I::W]
out = open(f'chars2_{EMAX}_{I}.pkl', 'ab')
t0 = time.time()
for (Q, m), (a, E) in mine:
    T = Tower(Q, extra=(4,) if m >= 4 else ())
    kap = T.kappa(Q)
    elems = {'sel': kap + T.nimber(m)}
    if m >= 1: elems['kap+0'] = kap
    if m != 1: elems['sel+1'] = kap + T.nimber(m ^ 1)
    if E % 2 == 0: elems['kap+w'] = kap + T.nimber(2)
    N = (1 << E) - 1
    res = []
    ells = [l for l in primes if E % fl[l] == 0]
    for name, x in elems.items():
        for ell in ells:
            res.append(dict(Q=Q, m=m, arm=a, E=E, elem=name, ell=ell, f=fl[ell], power=bool(x ** (N // ell) == T.one)))
    pickle.dump(res, out); out.flush()
    print(Q, m, a, E, f'{time.time()-t0:.1f}s', flush=True)
