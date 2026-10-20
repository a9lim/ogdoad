"""Element-level schedule simulator with a measured (jobe, 1 P-core) cost model for the
generic dense-model route.  Elements = (Q, m) keys; rows sharing an element are tested together."""
import pickle, collections, math, sys
from math import log, log2, exp, sqrt, lcm
rows = pickle.load(open('../rows_1000000.pkl', 'rb'))
args=[a for a in sys.argv[1:] if not a.startswith('--')]
LIM = int(args[0]) if args else 10**6
EMAX = float(args[1]) if len(args)>1 else 1e9
def interp(pts, x):
    pts = sorted(pts)
    if x <= pts[0][0]:
        (x0, y0), (x1, y1) = pts[0], pts[1]
    elif x >= pts[-1][0]:
        (x0, y0), (x1, y1) = pts[-2], pts[-1]
    else:
        for (x0, y0), (x1, y1) in zip(pts, pts[1:]):
            if x0 <= x <= x1: break
    s = (log(y1) - log(y0)) / (log(x1) - log(x0))
    return exp(log(y0) + s * (log(x) - log(x0)))
# jobe (i9-12900K, gf2x+PCLMUL, NTL 11.5.1), CPU seconds
SQR = [(1e4, 1.02e-5), (1e5, 2.86e-4), (1e6, 5.27e-3), (1e7, 7.55e-2)]
MUL = [(1e4, 1.51e-5), (1e5, 4.17e-4), (1e6, 1.01e-2), (1e7, 1.133e-1)]
def sqrmod(E): return interp(SQR, E)
def mulmod(E): return interp(MUL, E)
def compmod(E): return 2 * sqrt(E) * mulmod(E) + E * E / 1e11
def build(E, d=4): return 1.1e-7 * E * d + 0.01
def cost_brute(E): return E * sqrmod(E)
FOUR_RUSSIANS = '--4r' in sys.argv
def compmod(E): return 2 * sqrt(E) * mulmod(E) + E * E / (8e11 if FOUR_RUSSIANS else 1e11)
def cost_norm(E, H):
    # x^(2^H) by binary composition chain, norm to F_(2^H) by Frobenius doubling, map to small model, small Euler
    n_comp = 2 * log2(max(H, 2)) + 3 * max(1.0, log2(E / H)) + 2
    return n_comp * compmod(E) + H * sqrmod(H) * 2
g = collections.defaultdict(list)
for (p, h, Q, a, m, E) in rows:
    if 727 < p <= LIM and E <= EMAX: g[(Q, m)].append((p, h, E))
els = []
for k, v in g.items():
    E = v[0][2]; H = 1
    for (_, h, _) in v: H = lcm(H, h)
    assert E % H == 0
    cb, cn = cost_brute(E), cost_norm(E, H)
    c = min(cb, cn) + build(E)
    mass = sum(1 / p for (p, _, _) in v)
    els.append((mass / c, mass, c, E, len(v), k, 'brute' if cb <= cn else 'norm'))
els.sort(reverse=True)
cum_c = cum_m = 0; marks = [0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40]; mi = 0
print(f'elements={len(els)} rows={sum(e[4] for e in els)} total mass={sum(e[1] for e in els):.4f}')
for e in els:
    cum_c += e[2]; cum_m += e[1]
    while mi < len(marks) and 1 - exp(-cum_m) >= marks[mi]:
        print(f'P(hit)>={marks[mi]:.2f}: CPU={cum_c/3600:9.1f} jobe-core-h  elements={els.index(e)+1}  last E={e[3]:.3g} method={e[6]}')
        mi += 1
print(f'all: CPU={cum_c/3600:.1f} h  P(hit)={1-exp(-cum_m):.3f}')
by = collections.Counter(e[6] for e in els); print('method counts', dict(by))
for B in (1e5, 1e6, 3e6, 1e7, 3e7, 1e8):
    sel = [e for e in els if e[3] <= B]
    print(f'E<={B:.0e}: elements={len(sel)} rows={sum(e[4] for e in sel)} mass={sum(e[1] for e in sel):.4f} '
          f'P={1-exp(-sum(e[1] for e in sel)):.3f} CPU={sum(e[2] for e in sel)/3600:.1f} h  maxCPU/element={max(e[2] for e in sel)/3600:.2f} h')
