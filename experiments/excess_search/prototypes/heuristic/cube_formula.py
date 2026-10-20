"""Check: for prime ell = 5 mod 8 with 2 primitive, alpha = z+1/z is a cube in F_{2^n}
iff  eps in Z[sqrt ell]  (unit index 1)  or  3 | h(Q(sqrt ell)).   (derived; see notes)"""
import sys, pickle, math, collections
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
direct = pickle.load(open(sys.argv[1], 'rb')) if len(sys.argv) > 1 and sys.argv[1].endswith('.pkl') else {}
LF = int(sys.argv[2]) if len(sys.argv) > 2 else 0
bad = []; n = 0
for ell, res in sorted(direct.items()):
    if ell % 8 != 5: continue
    idx = int(pari.quadunitindex(ell, 2)); h = int(pari.qfbclassno(ell))
    pred = (idx == 1) or (h % 3 == 0)
    n += 1
    if pred != res[3]: bad.append((ell, idx, h, res[3]))
print('direct-vs-formula: checked', n, 'mismatches', bad[:10])
# formula-only statistics to LF
if LF:
    C = collections.Counter()
    for ell in pari.primes([13, LF]):
        ell = int(ell)
        if ell % 8 != 5 or int(pari.znorder(pari.Mod(2, ell))) != ell - 1: continue
        idx = int(pari.quadunitindex(ell, 2)); h = int(pari.qfbclassno(ell))
        C['N'] += 1; C['idx1'] += (idx == 1); C['h3'] += (h % 3 == 0)
        C['idx1&h3'] += (idx == 1 and h % 3 == 0); C['cube'] += (idx == 1 or h % 3 == 0)
    N = C['N']
    print(f"ell<= {LF}: N={N}  P(eps in Z[sqrt l])={C['idx1']/N:.4f}  P(3|h)={C['h3']/N:.4f}  P(both)={C['idx1&h3']/N:.4f}  P(cube)={C['cube']/N:.4f}  (naive 1/3; sd {math.sqrt(N*2/9)/N:.4f})")
