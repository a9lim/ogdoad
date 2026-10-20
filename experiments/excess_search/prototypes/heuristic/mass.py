"""Random-model masses from the million-row census (checked numerically)."""
import pickle, math, collections, sys
rows = pickle.load(open('../rows_1000000.pkl','rb'))
def divisors(n):
    return [d for d in range(1, n) if n % d == 0]
def degree_forced(p, h):
    # p-th powers of F_{2^h}^x lie in a proper subfield  <=>  (2^h-1)/p | 2^d-1, d|h, d<h
    N = (1 << h) - 1
    if N % (p*p) == 0: return False
    c = N // p
    return any(((1 << d) - 1) % c == 0 for d in divisors(h))
small = [r for r in rows if r[0] <= 727]
forced = [r[0] for r in small if r[1] <= 4000 and degree_forced(r[0], r[1])]
print('rows <= 727:', len(small), ' degree-forced:', forced)
S_all = sum(1/r[0] for r in small)
S_unf = sum(1/r[0] for r in small if r[0] not in forced)
P_all = math.prod(1-1/r[0] for r in small)
P_unf = math.prod(1-1/r[0] for r in small if r[0] not in forced)
print(f'sum 1/p (3..727) all={S_all:.4f} unforced={S_unf:.4f}')
print(f'P(all succeed | model): all rows={P_all:.4f}  unforced only={P_unf:.4f}')
print(f'with 719,727 certificates: S adds {1/719+1/727:.5f}')
# by arm, by window
wins = [(727,10**4),(10**4,10**5),(10**5,10**6)]
for lo,hi in wins:
    m = collections.Counter(); c = collections.Counter()
    for (p,h,Q,a,mm,E) in rows:
        if lo < p <= hi: m[a] += 1/p; c[a] += 1
    tot = sum(m.values())
    print(f'({lo},{hi}] total mass {tot:.4f}', {k:(c[k], round(v,4)) for k,v in sorted(m.items())})
# Mertens comparison
for X in (10**4,10**5,10**6):
    s = sum(1/r[0] for r in rows if 727 < r[0] <= X)
    print(f'X={X}: mass={s:.4f}  loglogX-loglog727={math.log(math.log(X))-math.log(math.log(727)):.4f}  P(>=1 fail | indep)={1-math.prod(1-1/r[0] for r in rows if 727<r[0]<=X):.3f}')
# mass carried by arms whose model sums converge: C, D, ZF
for a in ('C','D','ZF'):
    sel = [(r[0], r[1]) for r in rows if r[3]==a]
    print(a, 'rows', len(sel), 'mass all p<=1e6', round(sum(1/p for p,_ in sel),5), 'first', sel[:8])
