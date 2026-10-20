"""T2: crossed-root extraction without a b-bit exponentiation.

Setting: K = F_{2^b}, k = F_{2^t} subfield, Q = 2^t, psi = phi^t generates Gal(K/k),
D = b/t, z in K^{xR}, R = r^e, gcd(R, S) = 1 with S = (2^b-1)/(2^t-1).

(a) digit structure of the norm-split exponent X = (yS-1)/R (y = S^{-1} mod R):
    base-Q digits q_j = A*rho_{j+1} + eps_j, rho_{j+1} = ((D-1-j) y) mod R   [R | Q-1]
(b) Hilbert-90 root for prime r | Q-1:  u = z^{-(Q-1)/r},
    w = sum_{i<D} N_i(u) psi^i(theta)  (doubling recursion, O(log D) mults + psi-powers),
    then psi(w) = w z^{(Q-1)/r}, omega = w^r / z in k, fix w <- w / omega^{1/r}.
    Iterate for R = r^e, adjusting by mu_r so the intermediate stays an r^{e-j}-th power.
Both checked exactly by a^R == z.
"""
import sys, os, time, math, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xlib import *
import flint

def lcm(a, b): return a * b // math.gcd(a, b)

# ---------------- (a) digit periodicity ----------------
def digits_check():
    cnt = 0
    for (b, t, R) in [(20, 10, 11), (220, 22, 89), (19580, 178, 179), (3504820, 179, 359),
                      (2436, 406, 59), (37620, 418, 419)]:
        Q = 2 ** t
        if (Q - 1) % R: continue
        S = (2 ** b - 1) // (Q - 1)
        D = b // t
        y = pow(S % R, -1, R)
        X = (y * S - 1) // R
        A = (Q - 1) // R
        # extract digits
        xx = X
        ok = True
        for j in range(D):
            qj = xx % Q; xx //= Q
            rho = ((D - 1 - j) * y) % R
            digit = y - 1 if j == 0 else y
            rho_j = ((D - j) * y - (1 if j == 0 else 0)) % R if j > 0 else 0
            eps = (rho + digit - rho_j) // R
            if qj != A * rho + eps:
                ok = False; break
        assert xx == 0 and ok, (b, t, R)
        cnt += 1
    print("digit formula q_j = A*((D-1-j)y mod R)+eps_j verified on", cnt, "(b,t,R) cases")

# ---------------- (b) Hilbert-90 roots in a flat model ----------------
class Flat:
    """K = F_2[x]/P  (python-flint fq_default), psi = phi^t by repeated squaring."""
    def __init__(self, P, t):
        self.K = field(P, 'x'); self.t = t; self.b = deg(P)
        self.one = self.K.one()
        self.frob_calls = 0
    def psi(self, x, m=1):
        m %= (self.b // self.t)
        self.frob_calls += 1
        for _ in range(self.t * m):
            x = x.square()
        return x

def h90_prime_root(Kf, z, r, rng):
    """an r-th root of z (z an r-th power in K), r prime, r | Q-1."""
    t, b = Kf.t, Kf.b
    Q = 2 ** t; D = b // t
    assert (Q - 1) % r == 0
    one = Kf.one
    ZA = z ** ((Q - 1) // r)
    u = ZA ** -1
    mults = 0
    while True:
        theta = Kf.K([rng.randrange(2) for _ in range(b)])
        # left-to-right binary over D:  (S_m, N_m)
        Sm, Nm, m = theta, u, 1          # S_1 = theta, N_1 = u
        for bit in bin(D)[3:]:
            # double
            Sm = Sm + Nm * Kf.psi(Sm, m); Nm = Nm * Kf.psi(Nm, m); m *= 2; mults += 2
            if bit == '1':
                Sm = theta + u * Kf.psi(Sm, 1); Nm = u * Kf.psi(Nm, 1); m += 1; mults += 2
        assert m == D
        assert Nm == one, "norm of u is not 1"
        if Sm != 0: break
    w = Sm
    assert Kf.psi(w) == w * ZA
    omega = w ** r / z                  # in k, omega^((Q-1)/r) = 1
    assert Kf.psi(omega) == omega
    # r-th root of omega inside k^x (order Q-1); omega in k^{x r}
    om_r = small_root(Kf, omega, r)
    a = w / om_r
    assert a ** r == z
    return a, mults

def small_root(Kf, x, r):
    """r-th root inside the subfield k (order Q-1) - small-group work."""
    Q1 = 2 ** Kf.t - 1
    S = (2 ** Kf.b - 1) // Q1
    e = 0; q = Q1
    while q % r == 0: q //= r; e += 1
    if e == 0:
        return x ** pow(r, -1, Q1)
    l = pow(r, -1, q)
    s0 = x ** l
    eps = x ** ((r * l - 1) % Q1)
    rng = random.Random(7)
    while True:
        cand = Kf.K([rng.randrange(2) for _ in range(Kf.b)]) ** S   # random element of k
        if cand == 0: continue
        gen = cand ** q
        if gen ** (r ** (e - 1)) != Kf.one: break
    re_ = r ** e
    target = eps ** -1
    gamma = gen ** (r ** (e - 1))
    table = {}; cur = Kf.one
    for i in range(r):
        table[str(cur)] = i; cur = cur * gamma
    j = 0
    for i in range(e):
        hh = (target * gen ** ((re_ - j) % re_)) ** (r ** (e - 1 - i))
        j += table[str(hh)] * r ** i
    assert j % r == 0
    root = s0 * gen ** (j // r)
    assert root ** r == x
    return root

def is_power_via_norm(Kf, x, rpow):
    """x in K^{x rpow} iff N_{K/k}(x) in k^{x rpow} (iso of quotients); test in k."""
    Q1 = 2 ** Kf.t - 1
    S = (2 ** Kf.b - 1) // Q1
    Nx = x ** S
    g = math.gcd(rpow, Q1)
    return Nx ** (Q1 // g) == Kf.one

def h90_root(Kf, z, R, rng):
    fac = []
    n = R; d = 2
    while n > 1:
        while n % d == 0: fac.append(d); n //= d
        d += 1
    cur = z; rem = R; mult = 0
    for r in fac:
        rem //= r
        a, mu = h90_prime_root(Kf, cur, r, rng); mult += mu
        if rem > 1 and not is_power_via_norm(Kf, a, rem):
            # adjust by an r-th root of unity in k
            zeta = small_root_unity(Kf, r)
            for _ in range(r):
                a = a * zeta
                if is_power_via_norm(Kf, a, rem): break
            assert is_power_via_norm(Kf, a, rem)
        cur = a
    assert cur ** R == z
    return cur, mult

def small_root_unity(Kf, r):
    Q1 = 2 ** Kf.t - 1
    S = (2 ** Kf.b - 1) // Q1
    rng = random.Random(3)
    while True:
        g = Kf.K([rng.randrange(2) for _ in range(Kf.b)]) ** (S * (Q1 // r))
        if g != Kf.one and g != 0: return g

def root_case(name, P_alpha, R, t):
    b = deg(P_alpha)
    Kf = Flat(P_alpha, t)
    alpha = Kf.K.gen()
    S = (2 ** b - 1) // (2 ** t - 1)
    gK = math.gcd(R, 2 ** b - 1)
    w = pow(S % gK, -1, gK)
    c = (alpha ** S) ** w
    assert Kf.psi(c) == c
    z = alpha / c
    t0 = time.time()
    a, mults = h90_root(Kf, z, R, random.Random(11))
    dt = time.time() - t0
    print(f"{name}: b={b} t={t} D={b//t} R={R}: H90 root ok (a^R==z), {mults} K-mults in doubling, "
          f"{Kf.frob_calls} psi-powers, {dt:.2f}s")

if __name__ == "__main__":
    digits_check()
    root_case("row 23/89 (alpha_11)", P_alpha11(), 11, 10)
    root_case("row 727 (alpha_11, R=121, 121 !| 2^10-1)", P_alpha11(), 121, 10)
    root_case("row 179 (alpha_89)", P_alpha89(), 89, 22)
    root_case("row 359/1433 (alpha_179)", P_alpha179(), 179, 178)
