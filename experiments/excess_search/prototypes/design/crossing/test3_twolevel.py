"""T3: two-level recursive crossing for the h=179 rows (p=359, 1433) at real scale.

No field of degree E = 3,504,820 is built.  Largest object: K_1 = F_2(alpha_179)
(19,580 bits) represented as H_2[Y]/g_2(Y), and M = H_2[V]/(V^179 - c_1)
(350,482 bits, only for the hybrid path).

Level 2 (chi_89 over K_2 = F_2(alpha_89), 220 bits):
    k_2 = F_{2^22}, K_2 = k_2[Y]/g_2, c_2 = g_2(0)^w2, a_2 = (Y/c_2)^{1/89},
    H_2 = k_2(v_2), v_2^89 = c_2  (flat: F_2[u]/M_c(u^89), u = v_2)
Representation of K_1 = F_2(chi_89) = K_2 (x)_{k_2} H_2 = H_2[Y]/g_2(Y), chi_89 = a_2(Y) u.
Level 1 (chi_179 over K_1): k_1 = F_{2^178} subset H_2, c_1, a_1 by Hilbert 90.
  path A (pure k_1):  f = charpoly_{k_1}(a_1) (deg 110), W = V^110 f(1/V) in H_1,
                      T_A = N_{H_1 / F_{2^179}}(W)
  path B (hybrid):    f = charpoly_{H_2}(a_1) (deg 10), W' = V^10 f(1/V) in M,
                      T_B = N_{M / F_{2^179}}(W')
Checks: T_A == T_B exactly; minpoly(T) == minpoly(theta) from the p=359 certificate.
"""
import sys, os, time, math, random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xlib import *
import flint

T0 = time.time()
def log(*a):
    print(f"[{time.time()-T0:7.1f}s]", *a, flush=True)

def lcm(a, b): return a * b // math.gcd(a, b)

def prime_factors(n):
    f = []; d = 2
    while d * d <= n:
        if n % d == 0:
            f.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: f.append(n)
    return f

# ---------- generic small-group r-th root (for elements of a subfield) ----------
def subgroup_root(x, r, N, one, sampler):
    """r-th root of x in the cyclic subgroup of order N (x in it, x an r-th power there)."""
    e = 0; q = N
    while q % r == 0: q //= r; e += 1
    if e == 0:
        return x ** pow(r, -1, N)
    l = pow(r, -1, q)
    s0 = x ** l
    eps = x ** ((r * l - 1) % N)
    while True:
        cand = sampler()
        if cand == 0: continue
        gen = cand ** q
        if gen ** (r ** (e - 1)) != one: break
    re_ = r ** e
    target = eps ** (N - 1)
    gamma = gen ** (r ** (e - 1))
    table = {}; cur = one
    for i in range(r):
        table[repr(cur)] = i; cur = cur * gamma
    j = 0
    for i in range(e):
        hh = (target * gen ** ((re_ - j) % re_)) ** (r ** (e - 1 - i))
        j += table[repr(hh)] * r ** i
    assert j % r == 0
    root = s0 * gen ** (j // r)
    assert root ** r == x
    return root

# ---------- quotient ring helper: A[Y]/(G) over a flint field ----------
class QR:
    def __init__(self, base, G):
        self.base = base; self.R = flint.fq_default_poly_ctx(base); self.G = self.R(G) if not hasattr(G, 'degree') else G
        self.d = self.G.degree()
    def one(self): return self.R.one()
    def mul(self, a, b): return a.mul_mod(b, self.G)
    def sqr(self, a): return a.mul_mod(a, self.G)
    def pow(self, a, e):
        if e < 0:
            a = a.inverse_mod(self.G); e = -e
        return a.pow_mod(e, self.G)
    def inv(self, a): return a.inverse_mod(self.G)
    def frob(self, a, m):
        """x -> x^(2^m) by m squarings (test-scale only)."""
        for _ in range(m):
            a = a.mul_mod(a, self.G)
        return a
    def rand(self, rng):
        return self.R([self.base([rng.randrange(2) for _ in range(self.base.degree())]) for _ in range(self.d)])

def h90_root(QRK, z, r, t, D, rng, sub_sampler, N_sub):
    """r-th root of z in K = QRK (z an r-th power), r | 2^t-1, psi = phi^t of order D."""
    Q = 2 ** t
    ZA = QRK.pow(z, (Q - 1) // r)
    u = QRK.inv(ZA)
    psi = lambda x, m: QRK.frob(x, t * m)
    while True:
        theta = QRK.rand(rng)
        Sm, Nm, m = theta, u, 1
        for bit in bin(D)[3:]:
            Sm = Sm + QRK.mul(Nm, psi(Sm, m)); Nm = QRK.mul(Nm, psi(Nm, m)); m *= 2
            if bit == '1':
                Sm = theta + QRK.mul(u, psi(Sm, 1)); Nm = QRK.mul(u, psi(Nm, 1)); m += 1
        assert m == D and Nm == QRK.one(), "N(u) != 1"
        if not Sm.is_zero(): break
    w = Sm
    assert psi(w, 1) == QRK.mul(w, ZA)
    omega = QRK.mul(QRK.pow(w, r), QRK.inv(z))
    assert omega.degree() == 0
    om = omega[0]
    om_r = subgroup_root(om, r, N_sub, om / om, sub_sampler)
    a = QRK.mul(w, QRK.R(om_r ** -1))
    assert QRK.pow(a, r) == z % QRK.G
    return a

def bm_charpoly(seq, one, zero, D):
    C, L = berlekamp_massey(seq, one, zero)
    assert L == D, (L, D)
    C = C + [zero] * (L + 1 - len(C))
    return [C[L - i] for i in range(L + 1)]      # f[i] = coeff of X^i, monic

def minpoly_bits_from_seq(bits_seq):
    C, L = berlekamp_massey([flint.nmod(b, 2) for b in bits_seq], flint.nmod(1, 2), flint.nmod(0, 2))
    C = C + [flint.nmod(0, 2)] * (L + 1 - len(C))
    out = 0
    for i in range(L + 1):
        if int(C[i]): out |= 1 << (L - i)
    return out

def main():
    rng = random.Random(2026)
    # ---------------- level 2 ----------------
    P89 = P_alpha89(); b2 = 220; t2 = 22; R2 = 89; D2 = b2 // t2
    k2 = flint.fq_default_ctx(2, t2, 'l')
    Rk2 = flint.fq_default_poly_ctx(k2)
    P89k = Rk2([k2((P89 >> i) & 1) for i in range(b2 + 1)])
    g2 = P89k.factor()[1][0][0].monic()
    assert g2.degree() == D2
    K2 = QR(k2, g2)
    Y2 = Rk2.gen()
    S2 = (2 ** b2 - 1) // (2 ** t2 - 1)
    assert vr(2 ** t2 - 1, R2) == vr(2 ** b2 - 1, R2) == 1
    w2 = pow(S2 % R2, -1, R2)
    c2 = g2[0] ** w2
    # make c2 a generator of k2 (multiply by an 89th power) so F_2(v_2) = k_2(v_2)
    def degF2(x):
        d = 1
        while x ** (2 ** d) != x: d += 1
        return d
    kap = k2.gen()
    while degF2(c2) != t2:
        c2 = c2 * kap ** R2; kap = kap * k2.gen()
    z2 = Y2 * Rk2(c2 ** -1)
    a2 = h90_root(K2, z2, R2, t2, D2, rng,
                  lambda: k2([rng.randrange(2) for _ in range(t2)]), 2 ** t2 - 1)
    log("level 2: a2^89 == alpha_89/c2 verified in K2 = k2[Y]/g2 (220 bits)")
    # ---------------- flat H_2 ----------------
    # min poly of c2 over F_2 (degree 22)
    seq = []; cur = k2.one()
    for i in range(2 * t2 + 2):
        lst = cur.to_list(); seq.append(int(lst[0]) & 1 if lst else 0); cur = cur * c2
    Mc = minpoly_bits_from_seq(seq); assert deg(Mc) == t2
    MH = inflate(Mc, R2)                       # min poly of v_2 over F_2, degree 1958
    H2 = field(MH, 'u'); u = H2.gen()
    nH = deg(MH); assert nH == R2 * t2
    for q in prime_factors(nH):
        assert u ** (2 ** (nH // q)) != u
    assert u ** (2 ** nH) == u
    # embed k2 -> H2: root lam of k2's modulus with C(lam) = u^89
    RH2 = flint.fq_default_poly_ctx(H2)
    ml = k2.modulus()
    mlH = RH2([H2(int(ml[i])) for i in range(ml.degree() + 1)])
    Cc = c2.to_list()
    def emb_with(lam):
        def f(x):
            lst = x.to_list(); acc = H2.zero(); pw = H2.one()
            for cf in lst:
                if int(cf) & 1: acc = acc + pw
                pw = pw * lam
            return acc
        return f
    lam = None
    for rt, _ in mlH.roots():
        if emb_with(rt)(c2) == u ** R2:
            lam = rt; break
    assert lam is not None
    emb = emb_with(lam)
    log("H_2 = F_2[u]/M_c(u^89) (1958 bits), k2 -> H2 embedding with c2 -> u^89")
    # ---------------- K_1 = H_2[Y]/g_2^lam ----------------
    G1 = RH2([emb(g2[i]) for i in range(D2 + 1)])
    K1 = QR(H2, G1)
    Y = RH2.gen()
    a2H = RH2([emb(a2[i]) if i <= a2.degree() else H2.zero() for i in range(D2)])
    chi89 = K1.mul(a2H, RH2(u))
    assert K1.pow(chi89, R2) == Y % G1, "chi_89^89 != alpha_89"
    alpha179 = chi89 + RH2.one()
    log("K_1 = H_2[Y]/g_2 (19580 bits): chi_89 = a_2 v_2, chi_89^89 == alpha_89 verified")
    # ---------------- level 1 crossing ----------------
    b1 = 19580; t1 = 178; R1 = 179; D1 = b1 // t1; h = 179
    assert vr(2 ** t1 - 1, R1) == vr(2 ** b1 - 1, R1)
    S1 = (2 ** b1 - 1) // (2 ** t1 - 1)
    w1 = pow(S1 % R1, -1, R1)
    Nal = K1.pow(alpha179, S1)
    assert Nal.degree() == 0
    c1 = Nal[0] ** w1
    assert c1 ** (2 ** t1) == c1, "c1 not in k1"
    log("c1 = N_{K1/k1}(alpha_179)^w1 in k1 (inside H2)")
    z1 = K1.mul(alpha179, RH2(c1 ** -1))
    sampler_k1 = lambda: H2([rng.randrange(2) for _ in range(nH)]) ** ((2 ** nH - 1) // (2 ** t1 - 1))
    a1 = h90_root(K1, z1, R1, t1, D1, rng, sampler_k1, 2 ** t1 - 1)
    log("a1^179 == alpha_179/c1 verified (Hilbert-90 root, O(log D) psi-powers)")
    # ---------------- M = H_2[V]/(V^179 - c1) and sigma = phi^179 ----------------
    Mmod = RH2.gen() ** R1 - RH2(c1)
    def frobH(x, m):
        for _ in range(m % nH): x = x.square()
        return x
    def sigma_pow(Wp, m):
        """sigma^m = phi^(179 m) on M: V -> V^rho c1^q with 2^(179m) = q*179 + rho."""
        e = pow(2, 179 * m, 179 * (2 ** t1 - 1))   # 2^(179m) mod 179(2^178-1)
        rho = e % 179
        q = (e - rho) // 179                         # exponent of c1 (c1 has order | 2^178-1)
        cq = c1 ** q
        out = RH2.zero()
        coeffs = [Wp[j] if j <= Wp.degree() else H2.zero() for j in range(R1)]
        mult = H2.one()
        for j in range(R1):
            if not coeffs[j].is_zero():
                term = frobH(coeffs[j], 179 * m)
                ej = rho * j
                # V^(rho j) = V^(ej mod 179) * c1^(ej // 179); plus c1^(q j)
                fac = (cq ** j) * (c1 ** (ej // 179))
                out = out + RH2([H2.zero()] * (ej % 179) + [term * fac])
            # nothing
        return out % Mmod
    def norm_to_179(Wp, n_conj):
        """prod_{j<n_conj} sigma^j(Wp) by binary doubling."""
        Nm, m = Wp, 1
        for bit in bin(n_conj)[3:]:
            Nm = Nm.mul_mod(sigma_pow(Nm, m), Mmod); m *= 2
            if bit == '1':
                Nm = Wp.mul_mod(sigma_pow(Nm, 1), Mmod); m += 1
        assert m == n_conj
        return Nm
    # sanity: sigma is a ring map consistent with phi^179 on a small element
    tst = RH2([H2.gen(), H2.one()])  # u + V
    # (u + V)^(2^179) computed directly in M vs sigma
    direct = tst
    for _ in range(179): direct = direct.mul_mod(direct, Mmod)
    assert direct == sigma_pow(tst, 1), "sigma formula wrong"
    log("sigma = phi^179 monomial formula on M verified against 179 squarings")
    # ---------------- path B (hybrid, charpoly over H_2, degree 10) ----------------
    seq = []; cur = K1.one()
    for i in range(2 * D2 + 2):
        seq.append(cur[0] if cur.degree() >= 0 else H2.zero()); cur = K1.mul(cur, a1)
    fH = bm_charpoly(seq, H2.one(), H2.zero(), D2)
    acc = RH2.zero()
    for i in range(D2, -1, -1): acc = K1.mul(acc, a1) + RH2(fH[i])
    assert acc.is_zero()
    Wp = RH2([fH[D2 - j] for j in range(D2 + 1)]) % Mmod
    TB = norm_to_179(Wp, nH)     # [M : F_{2^179}] = 1958
    assert sigma_pow(TB, 1) == TB, 'T_B not in F_{2^179}'
    # note: F_{2^179} sits in H_1 = k_1(V), so T is a polynomial in V, not an H_2-constant
    log("path B: charpoly over H_2 (deg 10), W' in M (350482 bits), T_B = N_{M/F_2^179}(W')")
    # ---------------- path A (pure k_1, degree 110) ----------------
    def tr_H2_k1(y):
        acc = H2.zero(); cur = y
        for j in range(nH // t1):
            acc = acc + cur; cur = frobH(cur, t1)
        return acc
    seq = []; cur = K1.one()
    for i in range(2 * D1 + 2):
        c0 = cur[0] if cur.degree() >= 0 else H2.zero()
        seq.append(tr_H2_k1(c0)); cur = K1.mul(cur, a1)
    fk = bm_charpoly(seq, H2.one(), H2.zero(), D1)
    for cf in fk: assert cf ** (2 ** t1) == cf
    acc = RH2.zero()
    for i in range(D1, -1, -1): acc = K1.mul(acc, a1) + RH2(fk[i])
    assert acc.is_zero()
    W = RH2([fk[D1 - j] for j in range(D1 + 1)]) % Mmod      # lies in H_1 = k_1[V]/(V^179-c1)
    TA = norm_to_179(W, t1)      # [H_1 : F_{2^179}] = 178
    log("path A: charpoly over k_1 (deg 110), W in H_1 (31862 bits), T_A = N_{H1/F_2^179}(W)")
    assert TA == TB, "paths A and B disagree"
    log("T_A == T_B exactly")
    T = TA
    # ---------------- compare with the p=359 certificate's theta ----------------
    kc = field((1 << 179) | 0b10111, 'z')
    THETA_MASK = 0x28494A54795638CF203B2404FE5133E2AE0E13C2CA4E6
    theta = kc([(THETA_MASK >> i) & 1 for i in range(179)])
    def mp_of(x, coordf):
        seq = []; cur = x / x
        for i in range(2 * 179 + 4): seq.append(coordf(cur)); cur = cur * x
        return minpoly_bits_from_seq(seq)
    cf = lambda e: (int(e.to_list()[0]) & 1) if e.to_list() else 0
    m_theta = mp_of(theta, cf)
    # minpoly of T (an element of M) via BM on a coordinate of its powers in M
    seq = []; cur = RH2.one()
    for i in range(2 * 179 + 4):
        c0 = cur[0] if cur.degree() >= 0 else H2.zero()
        lst = c0.to_list(); seq.append(int(lst[0]) & 1 if lst else 0)
        cur = cur.mul_mod(T, Mmod)
    m_T = minpoly_bits_from_seq(seq)
    acc = RH2.zero()
    for e_ in range(deg(m_T), -1, -1):
        acc = acc.mul_mod(T, Mmod)
        if (m_T >> e_) & 1: acc = acc + RH2.one()
    assert acc % Mmod == 0
    log("minpoly(T) == minpoly(theta_cert):", m_T == m_theta, " degree", deg(m_T))
    assert m_T == m_theta
    for p in (359, 1433):
        ph = T.pow_mod((2 ** 179 - 1) // p, Mmod)
        print(f"   p={p}: T^((2^179-1)/p) != 1 (rule m_p=1 holds): {ph != RH2.one()}")

if __name__ == "__main__":
    main()
