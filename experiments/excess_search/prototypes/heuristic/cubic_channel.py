"""Global (class-group) channel at p=7 for type-II Gaussian periods: alpha is a 7th power in
F_{2^n} iff N_{n/3}(alpha)=1 in F_8, and N_{n/3}(alpha) is the reduction of the generator of the
cyclotomic units of the cyclic cubic field K_3 of conductor ell (index [E:C] = h(K_3)).
Prediction (derived): P(7th power | 7 does not divide h) ~ 1/7; P(.. | 7 | h) elevated."""
import sys, pickle, math, collections
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
D = pickle.load(open(sys.argv[1], 'rb'))
C = collections.Counter(); hits = []
for ell, res in sorted(D.items()):
    if 7 not in res: continue
    h = int(pari(f"bnfinit(polsubcyclo({ell},3),1).no"))
    k = '7|h' if h % 7 == 0 else '7!h'
    C[(k, 'N')] += 1; C[(k, 'pow')] += res[7]
    if h % 7 == 0: hits.append((ell, h, res[7]))
for k in ('7!h', '7|h'):
    N = C[(k, 'N')]
    if N: print(k, 'N', N, 'powers', C[(k, 'pow')], f'freq {C[(k,"pow")]/N:.3f}', 'naive 1/7=0.143')
print('7|h cases (ell, h, 7th power?):', hits)
# quadratic: cube formula over direct data
bad = []; n = 0
for ell, res in sorted(D.items()):
    if ell % 8 != 5: continue
    idx = int(pari.quadunitindex(ell, 2)); h = int(pari.qfbclassno(ell))
    n += 1
    if ((idx == 1) or (h % 3 == 0)) != res[3]: bad.append(ell)
print('cube formula checked on', n, 'direct cases; mismatches', bad)
