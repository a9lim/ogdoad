import time, pickle, sys
from tower import *
rows = pickle.load(open('/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/rows_100000.pkl','rb'))
oeis = {}
odd_primes = [r[0] for r in rows]
for line in open('/Users/a9lim/Work/ogdoad/src/scalar/big/ordinal/b380496.txt'):
    n, v = line.split(); oeis[odd_primes[int(n)-1]] = int(v)
EMAX = int(sys.argv[1])
cache = {}
ok = bad = 0
for (p,h,Q,a,m,E) in rows:
    if p > 709 or E > EMAX: continue
    key = (Q, m >= 4)
    t0 = time.time()
    T = Tower(Q, extra=(4,) if m >= 4 else ())
    kap = T.kappa(Q)
    mm = 0
    while T.is_power(kap + T.nimber(mm), p): mm += 1
    res = 'OK' if mm == oeis[p] else 'MISMATCH'
    if mm == oeis[p]: ok += 1
    else: bad += 1
    print(p, h, Q, a, 'E', T.E, 'm', mm, 'oeis', oeis[p], res, f'{time.time()-t0:.2f}s', flush=True)
print('ok', ok, 'bad', bad)
