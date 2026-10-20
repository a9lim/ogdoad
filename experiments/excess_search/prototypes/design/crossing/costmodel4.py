"""Cost model v4: crossing engine for singleton tops with the crossing degree t optimised.

Inputs measured on jobe (x86-64, PCLMUL, single thread, load ~10/24):
  P(b)  = gf2x_mul of two b-bit polynomials  (1e6: 3.05ms, 1e7: 42.5ms, 1e8: 0.506s, 1e9: 6.93s)
  mk(t) = one t-bit multiply-accumulate (lazy reduction), schoolbook PCLMUL
          (t=179: 4.9ns, 359: 12.6ns, 500: 26ns, 1000: 76ns, 2500: 411ns); for t > 4096 use P(t).
Derived (not measured): K-multiplication in the tensor representation K = k[y]/P_A(y)
  M(b) = 5 P(b) (packed Kronecker product of 2b-bit operands + Barrett over F_2[y]),
  doubled once more when the representation needs a third tensor tier (complement > LEAF).
Per distinct h (all rows p with f(p)=h share the work):
  root  = e * (0.4 f + 4 log2 D + 5) * M(b)       Hilbert-90 root (f squarings for z^A + doubling)
  bsgs  = 4 sqrt(2D) * M(b)                       baby/giant steps + transposed products
  inner = 2 D^2 mk(t) + 2D * 3P(t)                inner products (lazy) + one reduction each
  bm    = 30 D log2(D)^2 mk(t)                    half-gcd Berlekamp-Massey over k
  final = (2 log2(t/s) + 4) * 5 P(R t)            Itoh-Tsujii norm H -> F_{2^h}, monomial Frobenius
  build = 4 * M(b)                                tensor step chi_{R_2} = a_2 v_2 (a_2 cached)
"""
import pickle, math, sys, collections
sys.argv = [sys.argv[0], '100000']
from census import *

PTS = [(1e5, 0.142e-3), (1e6, 3.05e-3), (3e6, 10.47e-3), (1e7, 42.5e-3), (3e7, 130e-3),
       (1e8, 0.506), (3e8, 2.0), (1e9, 6.93)]
def P(b):
    b = max(b, 1e3)
    if b <= PTS[0][0]: return PTS[0][1] * (b / PTS[0][0])
    for (x0, y0), (x1, y1) in zip(PTS, PTS[1:]):
        if b <= x1:
            s = math.log(y1 / y0) / math.log(x1 / x0); return y0 * (b / x0) ** s
    x0, y0 = PTS[-2]; x1, y1 = PTS[-1]; s = math.log(y1 / y0) / math.log(x1 / x0)
    return y1 * (b / x1) ** s
LEAF = 3e4
def mk(t):
    if t > 4096: return P(t)
    w = math.ceil(t / 64); return (1.5 + 0.35 * w * w) * 1e-9
def vr(n, r):
    v = 0
    while n % r == 0: n //= r; v += 1
    return v
def divisors(n):
    f = factor(n); ds = [1]
    for q, e in f.items():
        ds = [d * q ** i for d in ds for i in range(e + 1)]
    return sorted(ds)

def cost_t(h, R, r, e, b1, f, s, t):
    D = b1 // t
    tiers = 1 if D <= LEAF else 2
    M = 5 * 2 ** (tiers - 1) * P(b1)
    lg = math.log2(max(D, 2))
    root = e * (0.4 * f + 4 * lg + 5) * M if D > 1 else e * (0.4 * f + 5) * 5 * P(R * t)
    bsgs = 4 * math.sqrt(2 * D) * M if D > 1 else 0
    inner = 2 * D * D * mk(t) + (2 * D * 3 * P(t) if D > 1 else 0)
    bm = 30 * D * lg ** 2 * mk(t) if D > 1 else 0
    final = (2 * math.log2(max(t // max(s, 1), 2)) + 4) * 5 * P(R * t) + 2 * h * mk(h)
    build = 4 * M if D > 1 else 0
    tot = root + bsgs + inner + bm + final + build
    return dict(t=t, D=D, Rt=R * t, M=M, root=root, bsgs=bsgs, inner=inner, bm=bm,
                final=final, total=tot, maxfield=max(b1, R * t))

def plan(h, R, tmode='opt', maxfield=None):
    (r, e), = factor(R).items(); b1 = b(r); s = h // R
    f = ordtwo(r)
    tmin = lcm(lcm(f, s), r ** vr(b1, r))
    cands = [t for t in divisors(b1) if t % tmin == 0 and vr(t, r) == vr(b1, r)]
    best = None
    for t in cands:
        if tmode == 'min' and t != tmin: continue
        c = cost_t(h, R, r, e, b1, f, s, t)
        if maxfield and c['maxfield'] > maxfield and t != tmin: continue
        if best is None or c['total'] < best['total']: best = c
    best.update(h=h, R=R, r=r, e=e, b=b1, f=f, tmin=tmin)
    return best

if __name__ == '__main__':
    rows = pickle.load(open('rows_100000.pkl', 'rb'))
    byh = collections.defaultdict(list)
    for (p, h, Q, a, m, E) in rows:
        if p > 727 and a in ('O', 'C', 'D'): byh[(h, Q[0])].append((p, E))
    for mode in ('min', 'opt'):
        plans = []
        for (h, R), lst in byh.items():
            x = plan(h, R, mode, maxfield=4e10); x['ps'] = [p for p, _ in lst]; x['E'] = lst[0][1]
            plans.append(x)
        pickle.dump(plans, open(f'plans4_{mode}.pkl', 'wb'))
        print(f'==== t mode: {mode} (max field 4e10 bits) ====')
        for PM in (10 ** 4, 10 ** 5):
            sel = [(x, sum(1 / p for p in x['ps'] if p <= PM)) for x in plans if min(x['ps']) <= PM]
            tot = sum(m for _, m in sel)
            print(f'p<={PM}: distinct h {len(sel)}  arm-O/C/D mass {tot:.4f}')
            sel.sort(key=lambda z: z[0]['total'])
            cum = 0; cm = 0; marks = [1, 60, 3600, 36000, 360000, 3.6e6]; i = 0
            for x, m in sel:
                while i < len(marks) and x['total'] > marks[i]:
                    print(f'   per-h <= {marks[i]:>9.0f}s : mass {cm:.4f} ({100*cm/tot:5.1f}%), '
                          f'cum. core-hours {cum/3600:10.1f}'); i += 1
                cum += x['total']; cm += m
            while i < len(marks):
                print(f'   per-h <= {marks[i]:>9.0f}s : mass {cm:.4f} ({100*cm/tot:5.1f}%), '
                      f'cum. core-hours {cum/3600:10.1f}'); i += 1
        for p in (733, 797, 839, 1019, 1433, 1439, 4507, 2879, 8629, 4079, 7559):
            xs = [x for x in plans if p in x['ps']]
            if xs:
                x = xs[0]
                print(p, {k: (f'{v:.3g}' if isinstance(v, float) else v) for k, v in x.items()
                          if k in ('h', 'R', 'b', 'tmin', 't', 'D', 'Rt', 'root', 'bsgs', 'inner',
                                   'final', 'total', 'maxfield')})
