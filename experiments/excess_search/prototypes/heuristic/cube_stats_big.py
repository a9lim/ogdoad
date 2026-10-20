import sys, math, collections
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
L = int(sys.argv[1])
bins = [2*10**4, 10**5, 2*10**5]
C = collections.Counter()
for ell in pari.primes([13, L]):
    ell = int(ell)
    if ell % 8 != 5 or int(pari.znorder(pari.Mod(2, ell))) != ell - 1: continue
    idx = int(pari.quadunitindex(ell, 2)); h = int(pari.qfbclassno(ell))
    b = next(x for x in bins if ell <= x)
    C[(b,'N')] += 1; C[(b,'idx1')] += (idx == 1); C[(b,'h3')] += (h % 3 == 0)
    C[(b,'both')] += (idx == 1 and h % 3 == 0)
lo = 0
for b in bins:
    N = C[(b,'N')]
    if not N: continue
    print(f"({lo},{b}]: N={N} P(idx1)={C[(b,'idx1')]/N:.4f} P(3|h)={C[(b,'h3')]/N:.4f} P(both)={C[(b,'both')]/N:.4f} P(cube)={(C[(b,'idx1')]+C[(b,'h3')]-C[(b,'both')])/N:.4f}", flush=True)
    lo = b
