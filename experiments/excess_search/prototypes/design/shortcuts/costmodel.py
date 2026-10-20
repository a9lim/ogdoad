"""Rough single-core cost model (idle M5 NTL timings from SPEC section 5)."""
import sys, math, re
sys.argv = ['x', '100000']
from reduce import *
pts = [1e4, 1e5, 1e6, 1e7]
T = {'sqr_s': [0.5e-6, 4e-6, 41e-6, 420e-6], 'mul_s': [26e-6, 0.9e-3, 11.8e-3, 424e-3],
     'mul_d': [77e-6, 2.7e-3, 36e-3, 1268e-3], 'sqr_d': [52e-6, 1.8e-3, 24e-3, 846e-3]}
def t(kind, E):
    E = max(E, 64); xs = [math.log(x) for x in pts]; ys = [math.log(y) for y in T[kind]]
    lx = math.log(E)
    if lx <= xs[0]: i = 0
    elif lx >= xs[-1]: i = 2
    else: i = max(j for j in range(3) if xs[j] <= lx)
    s = (ys[i+1]-ys[i])/(xs[i+1]-xs[i]); return math.exp(ys[i] + s*(lx-xs[i]))
def direct(E, ncomp):
    model = ncomp * (E * t('sqr_s', E) + E / 6 * t('mul_s', E))
    euler = E * t('sqr_s', E) + 30 * t('mul_s', E)
    return model + euler
def cross_O(R, b, t_, h):
    n = b // t_
    K = 2 * b * t('sqr_d', b) + b / 6 * t('mul_d', b) + n * n / 2 * t('mul_d', b)
    Hsq = R * t('mul_s', t_)          # one tower squaring in H = k[V]/(V^R-c)
    H = R * t_ * Hsq + 30 * R * R * t('mul_s', t_)
    return K + H
def fmt(s):
    return f'{s:.2g}s' if s < 120 else (f'{s/60:.1f}min' if s < 7200 else (f'{s/3600:.1f}h' if s < 172800 else f'{s/86400:.1f}d'))
for p in map(int, sys.argv[1:] if len(sys.argv) > 2 else (733, 743, 797, 1031, 1433, 4507, 839, 887, 9973)):
    h = ordtwo(p); Q = Qset(h); E, (c, how) = reduced(p, h, Q)
    nodd = sum(1 for q in Q if q % 2)
    d = direct(E, nodd)
    line = f'{p:6d} {arm(h,Q)} Q={Q} E={E} direct~{fmt(d)}'
    mm = re.match(r"cross\((\d+),\) M=(\d+) K=(\d+) t=\{\d+: (\d+)\}", how)
    if mm and len(Q) == 1:
        R, M, b, tt = map(int, mm.groups())
        line += f' | crossed (K={b}, H={M}, n={b//tt}) ~{fmt(cross_O(R, b, tt, h))}'
    elif how != 'direct':
        line += f' | {how}'
    print(line)
