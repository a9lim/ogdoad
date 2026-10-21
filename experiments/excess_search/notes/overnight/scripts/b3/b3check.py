# Sanity checks for B3 lemmas (NOT a search): Lemma 3.1 (S=0), digit lemma 4.1,
# Singer relation 2.1, eigenline of twisted sum S'(1) (3.4), at k=1,2 only.
import sys
def field(n, poly):
    # poly: integer bitmask incl. x^n; returns exp/log tables if x is primitive
    N = (1<<n)-1
    exp = [0]*(2*N); log = [-1]*(1<<n)
    x = 1
    for i in range(N):
        exp[i] = x
        if log[x] != -1: return None
        log[x] = i
        x <<= 1
        if x >> n: x ^= poly
    for i in range(N, 2*N): exp[i] = exp[i-N]
    return exp, log
def mul(a,b,exp,log,N):
    if a==0 or b==0: return 0
    return exp[(log[a]+log[b])%N]
def pw(a,e,exp,log,N):
    if a==0: return 0
    return exp[(log[a]*e)%N]
def tracemask(n, exp, log, N):
    # Tr(alpha^i) for polynomial basis alpha^i, i<n
    mask = 0
    for i in range(n):
        x = 1<<i; t = 0; y = x
        for _ in range(n):
            t ^= y; y = mul(y,y,exp,log,N)
        assert t in (0,1)
        if t: mask |= (1<<i)
    return mask
def tr(x, mask): return bin(x & mask).count('1') & 1

polys = {3:0b1011, 6:0b1000011, 9:0b1000010001, 11:(1<<11)|0b101, 18:(1<<18)|(1<<7)|1}
# Lemma 3.1: S = sum_{x != 0} L(x)(-1)^Tr(x) = 0 mod l, and prod_{Tr x=0, x!=0} x = 1
for (n,l) in [(3,7),(9,73),(11,23),(11,89),(6,7),(18,73),(18,19)]:
    T = field(n, polys[n]); assert T, n
    exp,log = T; N=(1<<n)-1; mask = tracemask(n,exp,log,N)
    S = 0; P = 0
    for x in range(1,1<<n):
        e = log[x]; Lx = e % l
        S += Lx if tr(x,mask)==0 else -Lx
        if tr(x,mask)==0: P = (P + e) % N
    print(f"Lemma3.1 n={n} l={l}: S mod l = {S % l}, log(prod trace-0) mod N = {P}")
# Digit lemma 4.1
for (h,l) in [(3,7),(9,73),(27,262657),(11,23),(11,89),(18,19)]:
    d = ((1<<h)-1)//l; assert d*l == (1<<h)-1
    ok = all(((d>>i)&1) == (1 if 2*pow(2,h-1-i,l) >= l else 0) for i in range(h))
    print(f"Digit lemma h={h} l={l}: d={d}, ok={ok}")
# k=1 (n=3,l=7) and k=2 (n=9,l=73): Singer relation, gamma order, S'(1)
for (k,l) in [(1,7),(2,73)]:
    n = 3**k; m = 3**(k+1); exp,log = field(2*n, polys[2*n]); N=(1<<(2*n))-1
    mask = tracemask(2*n,exp,log,N)
    zeta = exp[N//m]
    gam = zeta ^ pw(zeta, N-1, exp, log, N)
    q = 1<<n
    assert pw(gam, q, exp, log, N) == gam  # gamma in F_q
    og = N//__import__('math').gcd(N, log[gam])
    qk = 1<<(3**(k-1)); eta = pw(gam, qk-1, exp, log, N)
    singer = pw(eta, qk+1, exp, log, N) == (eta ^ 1)
    Lg = log[gam] % l
    # twisted sum S'(1): coefficient vector c_j, j in Z/m
    c = [0]*m
    for x in range(1, N+1):
        e = log[x]; s = 1 if tr(x,mask)==0 else -1
        c[e % m] = (c[e % m] + s*(e % l)) % l
    def is_zero(v):  # zero in Z[zeta_m]/l iff constant on cosets mod 3^k
        return all(v[j]==v[(j+n)%m]==v[(j+2*n)%m] for j in range(m))
    inv2 = pow(2,-1,l)
    sig = [0]*m
    for j in range(m): sig[(2*j)%m] = (sig[(2*j)%m] + c[j]) % l
    diff = [(sig[j] - inv2*c[j]) % l for j in range(m)]
    print(f"k={k} l={l}: ord(gamma)={og} (2^n-1={q-1}), Singer eta^(q+1)=eta+1: {singer}, "
          f"L(gamma) mod l = {Lg}, S'(1)=0? {is_zero(c)}, sigma2 S' = S'/2? {is_zero(diff)}")
