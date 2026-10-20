"""Small exact helpers for testing crossing / norm-descent identities.

Everything here is exact finite-field arithmetic (python-flint).  Singleton
chains are built from the term algebra's free minimal polynomials:
    P_{chi_R}(X) = P_{alpha_r}(X^R),   P_{alpha}(X) = P_{chi'}(X + m)  (m in {0,1}).
The flat model F_2[X]/P(X) with X = the top component is a canonical model:
every lower component is a polynomial in X (chi' = X^R + m, ...).
"""
from __future__ import annotations
import flint, math, sys, os
sys.path.insert(0, os.path.dirname(__file__))

Pc = flint.fmpz_mod_poly_ctx(2)

# ---------------- bit polynomials over F_2 -----------------
def mulb(a: int, b: int) -> int:
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        b >>= 1
    return r

def compose(p: int, inner: int) -> int:
    out = 0
    for e in range(p.bit_length() - 1, -1, -1):
        out = mulb(out, inner)
        if (p >> e) & 1:
            out ^= 1
    return out

def inflate(p: int, R: int) -> int:
    out = 0
    e = 0
    while p:
        if p & 1:
            out |= 1 << (e * R)
        p >>= 1
        e += 1
    return out

def shift1(p: int) -> int:
    """p(X+1)."""
    return compose(p, 0b11)

def deg(p: int) -> int:
    return p.bit_length() - 1

def to_fmpz(p: int):
    return Pc([(p >> i) & 1 for i in range(p.bit_length())])

# minimal polynomials of the bottom finite components
P_ALPHA = {3: 0b111,     # alpha_3 = chi_2 : x^2+x+1
           5: 0b10011}   # alpha_5 = chi_4 : x^4+x+1

def chain_alpha_minpoly(chain):
    """chain = [(r_bottom,...)...]; list of (R, m) from bottom up:
    alpha_{next} = chi_R + m, chi_R^R = alpha_prev.  Returns P_alpha of the top."""
    raise NotImplementedError

def p_chi(P_alpha: int, R: int) -> int:
    return inflate(P_alpha, R)

def p_alpha_from_chi(P_chi: int, m: int) -> int:
    assert m in (0, 1)
    return shift1(P_chi) if m == 1 else P_chi

# chains used in tests (singleton, m=1 at every odd level)
def P_alpha11():
    return p_alpha_from_chi(p_chi(P_ALPHA[5], 5), 1)        # deg 20
def P_alpha89():
    return p_alpha_from_chi(p_chi(P_alpha11(), 11), 1)      # deg 220
def P_alpha179():
    return p_alpha_from_chi(p_chi(P_alpha89(), 89), 1)      # deg 19580

# ---------------- fields -----------------
def field(P: int, var='x'):
    return flint.fq_default_ctx(modulus=to_fmpz(P), var=var, fq_type="FQ_NMOD",
                                check_modulus=False)

def ordtwo(p):
    o = 1
    x = 2 % p
    while x != 1:
        x = x * 2 % p
        o += 1
    return o

def vr(n, r):
    v = 0
    while n % r == 0:
        n //= r
        v += 1
    return v

# ---------------- Berlekamp-Massey over a field -----------------
def berlekamp_massey(seq, one, zero):
    """Return connection polynomial C (list, C[0]=1) of minimal LFSR for seq."""
    C = [one]; B = [one]; L = 0; m = 1; b = one
    for n in range(len(seq)):
        d = seq[n]
        for i in range(1, L + 1):
            d = d + C[i] * seq[n - i]
        if d == zero:
            m += 1
            continue
        coef = d / b
        T = C[:]
        need = len(B) + m
        if len(C) < need:
            C = C + [zero] * (need - len(C))
        for i in range(len(B)):
            C[i + m] = C[i + m] - coef * B[i]
        if 2 * L <= n:
            L = n + 1 - L
            B = T; b = d; m = 1
        else:
            m += 1
    return C[:L + 1], L

def minpoly_F2_of(x, coord):
    """Min poly over F_2 (as int bits) of element x, using linear form coord(.)
    and verified by evaluation.  coord must map field elements to 0/1."""
    seq = []
    y = x.__class__  # unused
    one = x / x
    cur = one
    # degree bound: field degree <= 4096 for our uses; take 2*bound terms lazily
    terms = []
    N = 2 * 400
    for i in range(N):
        terms.append(coord(cur))
        cur = cur * x
    C, L = berlekamp_massey([flint.nmod(t, 2) for t in terms], flint.nmod(1, 2), flint.nmod(0, 2))
    # connection poly C(z) -> min poly is reversed: m(X) = X^L C(1/X)
    bits = 0
    Cl = C + [flint.nmod(0, 2)] * (L + 1 - len(C))
    for i in range(L + 1):
        if int(Cl[i]):
            bits |= 1 << (L - i)
    # verify m(x) = 0
    acc = x * 0
    for e in range(L, -1, -1):
        acc = acc * x
        if (bits >> e) & 1:
            acc = acc + one
    assert acc == 0, "BM minpoly failed verification"
    return bits
