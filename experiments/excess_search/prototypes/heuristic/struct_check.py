"""Calibrate the per-conductor mass heuristic and the growth of sigma_{-1}(b_r)."""
import sys, math, numpy as np, collections
sys.argv = [sys.argv[0], '1e7']
import census_fast as C
d = np.load('census_100000000.npz'); p = d['p']; h = d['h']; arm = d['arm']
inv = 1.0 / p
# (1) per-h mass: actual sum_{f(p)=h, p<=1e8} 1/p vs heuristic H(h)
mass = collections.defaultdict(float)
for hh, iv in zip(h[h <= 20000], inv[h <= 20000]): mass[int(hh)] += iv
def heur(hh):
    # primes p == 1 mod lcm(2,h); P(ord=h | p == 1 mod h) ~ phi(h)/(p-1); sum ~ int_{h0}^inf dx/(x^2 ln x) with h0 = lcm(2,h)
    h0 = hh if hh % 2 == 0 else 2 * hh
    return 1.0 / (h0 * math.log(h0))
for lo, hi in [(2, 100), (100, 1000), (1000, 5000), (5000, 20000)]:
    A = sum(mass[x] for x in range(lo, hi)); H = sum(heur(x) for x in range(lo, hi))
    print(f'h in [{lo},{hi}): actual {A:.5f}  heuristic {H:.5f}  ratio {A/H:.3f}')
# (2) sigma_{-1}(b_r) by decade for primes r (O-cell bottoms), and divisibility of b_r by small g
def sigma_m1(n):
    f = C.factor(n); s = 1.0
    for q, e in f.items(): s *= sum(q ** -j for j in range(e + 1))
    return s
pr = [int(x) for x in C.primes if x > 2]
for k in range(1, 7):
    sel = [x for x in pr if 10 ** k < x <= 10 ** (k + 1)]
    if len(sel) > 20000: sel = sel[::len(sel) // 20000]
    sv = [sigma_m1(C.b(x)) for x in sel]
    bs = [C.b(x) for x in sel]
    frac = {g: sum(1 for b in bs if b % g == 0) / len(bs) for g in (2, 3, 4, 5, 8, 12, 16, 7)}
    lb = sorted(math.log10(b) for b in bs)
    print(f'r in (1e{k},1e{k+1}]: n={len(sel)} mean sigma_-1(b_r)={np.mean(sv):.3f} max={max(sv):.3f}  median log10 b_r={lb[len(lb)//2]:.2f}  P(g|b_r)=' + ' '.join(f'{g}:{v:.2f}' for g, v in frac.items()))
