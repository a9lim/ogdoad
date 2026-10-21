# Lemma check for Theorem 3.3/3.5 (NOT a search): for moduli m with 2 a primitive
# root, n = ord_m(2)/2, l prime with ord_l(2) = n: compare L(gamma) with
# F(zeta) = L(prod_{y in H, Tr(zeta*y)=0} y), H = m-th powers of F_{2^{2n}}^x.
import math
exec(open('b3check.py').read().split("polys =")[0])
polys = {4:0b10011, 6:0b1000011, 10:(1<<10)|0b1001, 18:(1<<18)|(1<<7)|1, 20:(1<<20)|0b1001}
def ordmod(a, m):
    o, x = 1, a % m
    while x != 1: x = x*a % m; o += 1
    return o
for (m, l) in [(5,3),(9,7),(11,31),(25,11),(19,73),(27,73)]:
    n = ordmod(2, m)//2; Q = 1 << (2*n); N = Q-1
    assert ordmod(2, l) == n and N % m == 0 and math.gcd(m, N//m) == 1
    T = field(2*n, polys[2*n]); assert T; exp, log = T
    mask = tracemask(2*n, exp, log, N)
    zeta = exp[N//m]; gam = zeta ^ exp[(N - N//m) % N]
    Lg = log[gam] % l
    Fx = {}
    for a in range(m):
        xi = exp[(a*(N//m)) % N]; s = 0
        for e in range(0, N, m):          # y = g^e in H
            y = exp[e]
            if tr(mul(xi, y, exp, log, N), mask) == 0: s += e
        Fx[a] = s % l
    prim = [a for a in range(m) if math.gcd(a, m) == 1]
    nonprim_zero = all(Fx[a] == 0 for a in range(m) if math.gcd(a, m) > 1)
    frob = all(Fx[(2*a) % m] == (2*Fx[a]) % l for a in prim)
    F1 = Fx[1]
    ratio = (Lg * pow(F1, -1, l)) % l if F1 else None
    print(f"m={m} n={n} l={l}: L(gamma)={Lg}, F(zeta)={F1}, F=0 off primitive: {nonprim_zero}, "
          f"F(xi^2)=2F(xi): {frob}, ratio L(gamma)/F(zeta) = {ratio}, "
          f"2^n mod l = {pow(2,n,l)}, -1/2 = {(-pow(2,-1,l))%l}, 1/2 = {pow(2,-1,l)}, -2={(-2)%l}")
