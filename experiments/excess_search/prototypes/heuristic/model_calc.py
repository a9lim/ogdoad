"""Exact random-model predictions from the arm census (see model.md).

usage: python model_calc.py census_<N>.npz
"""
import sys, math, numpy as np
d = np.load(sys.argv[1] if len(sys.argv) > 1 else 'census_100000000.npz')
p = d['p']; h = d['h']; arm = d['arm']; r = d['r']; a = d['a']
NAME = {0: 'Z', 1: 'ZF', 2: 'O', 3: 'C', 4: 'D'}
import re as _re
Ncen = int(_re.search(r'census_(\d+)', sys.argv[1] if len(sys.argv) > 1 else 'census_100000000').group(1))

# ---- settled rows (theorem or exact certificate) -------------------------
settled = np.zeros(len(p), bool)
why = {}
def mark(mask, tag):
    global settled
    settled |= mask
    for q in p[mask]: why[int(q)] = tag
mark((arm == 1) & (h <= 4096), 'Fermat cell n<=11 (exact, OPEN.md)')
mark(np.isin(p, [114689, 26017793, 63766529, 13631489]), 'published F_12..F_18 factor screen (exact)')
mark((arm == 3) & np.isin(h, [3, 9, 27, 81, 243]), 'C_1..C_5')
mark((arm == 4) & np.isin(h, [18, 54, 162, 486]), "D'_2..D'_5")
mark((arm == 0) & np.isin(h, [12, 15, 24, 36, 40]), 'Z tensor h=12,15,24,36,40')
mark(np.isin(p, [359, 719, 727]), 'local certificate')
cond = np.isin(p, [1433])  # Codex numeric check, conditional on 359 norm link
print('census N =', Ncen, ' rows =', len(p))
print('settled rows <= N:', int(settled.sum()))
for q in sorted(why):
    if q > 727: print('   settled', q, NAME[int(arm[p == q][0])], why[q])
print('conditional (not removed):', p[cond])
uns = ~settled
inv = 1.0 / p.astype(np.float64)
lg = np.log1p(-inv)

def block(lo, hi, extra_mask=None):
    m = (p > lo) & (p <= hi) & uns
    if extra_mask is not None: m &= extra_mask
    out = {}
    for k, nm in NAME.items():
        mk = m & (arm == k)
        out[nm] = (int(mk.sum()), float(inv[mk].sum()), float(lg[mk].sum()))
    out['all'] = (int(m.sum()), float(inv[m].sum()), float(lg[m].sum()))
    return out

def show(title, B):
    print(f'\n{title}')
    print('  arm    rows      E[fail]=sum 1/p    P(no fail)')
    for nm in ['Z', 'O', 'C', 'D', 'ZF', 'all']:
        n, s, l = B[nm]
        print(f'  {nm:4s} {n:8d}   {s:.6f}           {math.exp(l):.6f}')

show('OBSERVED RANGE 11 <= p <= 727 (likelihood of the data)', block(10, 727))
mm_all = (p >= 11) & (p <= 727)
print('\nDIAGNOSTIC 11<=p<=727 with theorem-settled rows NOT removed: rows %d, sum 1/p %.6f, prod %.6f' % (mm_all.sum(), inv[mm_all].sum(), math.exp(lg[mm_all].sum())))
print('theorem-settled rows in 11..727:', [int(x) for x in p[settled & mm_all]])
for X in [10**4, 10**5, 10**6, 10**7, 10**8]:
    if X <= Ncen: show(f'PREDICTION (727, {X:.0e}]', block(727, X))

# ---- decade shares ---------------------------------------------------------
print('\nDECADE MASS SHARES (unsettled rows)')
print('  decade        mass_all   Z share   O share   O mass')
dec = []
for k in range(3, int(math.log10(Ncen)) + 1):
    lo, hi = 10 ** k, 10 ** (k + 1)
    if hi > Ncen: break
    B = block(lo, hi)
    s = B['all'][1]
    dec.append((k, B['O'][1] / s, B['O'][1], s))
    print(f'  (1e{k},1e{k+1}]   {s:.5f}   {B["Z"][1]/s:.4f}   {B["O"][1]/s:.4f}   {B["O"][1]:.5f}')
# finer: half-decades
print('\n  half-decade O share')
xs = []; ys = []
edges = [10 ** (e / 2) for e in range(6, 2 * int(math.log10(Ncen)) + 1)]
for lo, hi in zip(edges[:-1], edges[1:]):
    B = block(lo, hi); s = B['all'][1]
    mid = math.sqrt(lo * hi)
    xs.append(math.log(mid)); ys.append(B['O'][1] / s)
    print(f'   ({lo:.2e},{hi:.2e}]  O share {B["O"][1]/s:.4f}  ln x={math.log(mid):.2f}  share*ln x={B["O"][1]/s*math.log(mid):.3f}  share*lnx/lnlnx={B["O"][1]/s*math.log(mid)/math.log(math.log(mid)):.3f}')
xs = np.array(xs); ys = np.array(ys)
# fits: share = c/ln x ; share = c lnln x/ln x ; share = c (ln x)^-beta
c1 = np.mean(ys * xs)
c2 = np.mean(ys * xs / np.log(xs))
beta, lc = np.polyfit(np.log(xs), np.log(ys), 1)
print(f'\n  fit c/ln x: c={c1:.3f}; fit c lnln/ln: c={c2:.3f}; power fit share = {math.exp(lc):.3f} (ln x)^{beta:.3f}')

# ---- tails beyond census ---------------------------------------------------
# exact totals (727, X] from recip_sum.py
TOT = {1e4: 0.3305530131378469, 1e5: 0.5527652449515505, 1e6: 0.734821165471959,
       1e7: 0.8889424471839968, 1e8: 1.0224682958248115, 1e9: 1.1402487847032576}
LTOT = {1e8: -1.022558688556566, 1e9: -1.1403391776700298}
sett_mass = {X: float(inv[settled & (p > 727) & (p <= X)].sum()) for X in TOT if X <= Ncen}
print('\nsettled mass beyond 727 inside census:', sett_mass)
B8 = block(727, Ncen)
O8 = B8['O'][1]; Z8 = B8['Z'][1]; small8 = B8['C'][1] + B8['D'][1] + B8['ZF'][1]

def mertens_tail(X, Y=1e9):
    return math.log(math.log(X)) - math.log(math.log(Y))
def RS_err(X, Y=1e9):
    return 1 / (2 * math.log(Y) ** 2) + 1 / (2 * math.log(X) ** 2)

def O_tail(X, Y=float(Ncen), model='c/ln'):
    lY, lX = math.log(Y), math.log(X)
    if model == 'c/ln':      # int share dx/(x ln x), share=c/ln x -> c(1/lY - 1/lX)
        return c1 * (1 / lY - 1 / lX)
    if model == 'lnln':      # share=c lnln x/ln x -> c[(1+ln u)/u] from lY to lX
        return c2 * ((1 + math.log(lY)) / lY - (1 + math.log(lX)) / lX)
    if model == 'pow':
        A = math.exp(lc)
        return A * (lY ** beta - lX ** beta) / (-beta)
print('\nO-arm tail beyond census to infinity: c/ln %.4f  lnln %.4f  pow %.4f' % (
    O_tail(1e300 ** 1e5 if False else 1e300, model='c/ln'), O_tail(1e300, model='lnln'), O_tail(1e300, model='pow')))

print('\nPREDICTIONS beyond the census (727, X]:')
print('  X        E[all]     +-RS      P(no fail)   E[O] (c/ln | lnln | pow)       E[Z]~')
for X in [1e9, 1e20, 1e100]:
    if X == 1e9:
        tot = TOT[1e9] - sett_mass.get(1e8, 0.0); err = 0.0
    else:
        tot = TOT[1e9] - sett_mass.get(1e8, 0.0) + mertens_tail(X); err = RS_err(X)
    Os = [O8 + O_tail(X, model=m) for m in ('c/ln', 'lnln', 'pow')]
    Pnf = math.exp(-tot - 9e-5)  # second-order term sum 1/(2p^2) over p>727 ~ 9e-5 (computed below)
    print(f'  {X:.0e}   {tot:.5f}  {err:.1e}   {Pnf:.5f}     {Os[0]:.4f} | {Os[1]:.4f} | {Os[2]:.4f}     {tot - Os[1] - small8:.4f}')

# second-order term and p^-2, p^-3 sums
m = (p > 727) & uns
s2 = float((inv[m] ** 2).sum()); s3 = float((inv[m] ** 3).sum())
print(f'\nsum_{{p>727 unsettled, <=N}} p^-2 = {s2:.6e} (+ tail ~{1/(Ncen*math.log(Ncen)):.1e});  p^-3 = {s3:.3e}')
print('sum (-log(1-1/p) - 1/p) over p>727 unsettled:', float((-lg[m] - inv[m]).sum()))

# ---- first failure distribution --------------------------------------------
print('\nFIRST FAILURE beyond 727: P(F > X)')
mm = (p > 727) & uns
cum = np.cumsum(lg[mm]); pp = p[mm]
def surv(X):
    if X <= Ncen:
        i = np.searchsorted(pp, X, side='right')
        return math.exp(cum[i - 1]) if i > 0 else 1.0
    # beyond census: exact totals to 1e9 then Mertens ratio
    S = math.exp(cum[-1])
    if Ncen < 1e9:
        S *= math.exp(-(TOT[1e9] - TOT[1e8]))
    return S * math.log(1e9) / math.log(X) if X > 1e9 else S
for X in [1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e12, 1e20, 1e50, 1e100]:
    print(f'  X={X:.0e}  P(F>X)={surv(X):.4f}')
# quantiles
def quant(q):
    target = 1 - q
    i = np.searchsorted(-cum, -math.log(target))
    if i < len(pp): return float(pp[i])
    S = surv(1e9)
    return math.exp(math.log(1e9) * S / target)  # ln X = ln(1e9) S / target
for q in [0.1, 0.25, 0.5, 0.75, 0.9, 0.99]:
    v = quant(q)
    print(f'  quantile {q:.2f}: X ~ {v:.3e}   (log10 = {math.log10(v):.2f})')

# ---- per-arm D / C / ZF residuals ------------------------------------------
print('\nunsettled C/D/ZF rows in census:')
for k in (3, 4, 1):
    mk = uns & (arm == k) & (p > 727)
    print('  ', NAME[k], [(int(x), int(y)) for x, y in zip(p[mk], h[mk])], 'mass %.3e' % inv[mk].sum())
