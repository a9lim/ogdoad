# Lemma check: is Pi(zeta) ~ (1+zeta)^(2^e) at EVERY prime p | N/m, or only at
# primes with ord_p(2) = n?  (Tests whether Thm 3.5 is an exact identity.)
import math
exec(open('b3ratio.py').read().split("for (m, l) in")[0])
def factor(x):
    f = {}; d = 2
    while d*d <= x:
        while x % d == 0: f[d] = f.get(d,0)+1; x//=d
        d += 1
    if x > 1: f[x] = f.get(x,0)+1
    return f
for m in [9, 11, 19, 25, 27]:
    n = ordmod(2, m)//2; Q = 1 << (2*n); N = Q-1
    exp, log = field(2*n, polys[2*n]); mask = tracemask(2*n, exp, log, N)
    zeta = exp[N//m]
    DP = 0
    for e in range(0, N, m):
        if tr(mul(zeta, exp[e], exp, log, N), mask) == 0: DP += e
    D1 = log[1 ^ zeta]
    out = []
    for p, a in factor(N//m).items():
        pa = p**a; op = ordmod(2, p)
        if D1 % p == 0: out.append(f"{p}^{a}(ord{op}):D1=0"); continue
        r = DP * pow(D1, -1, pa) % pa
        es = [e for e in range(2*n) if pow(2, e, pa) == r]
        out.append(f"{p}^{a}(ord {op}): ratio={r} 2^e e={es}")
    print(f"m={m} n={n} N/m={N//m}:", "; ".join(out))
