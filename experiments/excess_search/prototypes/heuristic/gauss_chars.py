"""Power-residue characters of type-II Gaussian periods alpha = z + 1/z in F_{2^n},
z a primitive ell-th root of unity, ell prime with 2 a primitive root mod ell
(so alpha is canonical up to Frobenius), n = (ell-1)/2.

For each small prime p with d = f(p) | n, test whether alpha is a p-th power,
via N_{n/d}(alpha) computed in F_2[x]/(x^ell - 1) (rotations), then the Euler
test inside F_{2^d}.  Arithmetic is exact; the check 'y == 1 mod Phi_ell' is
'y xor 1 in {0, all-ones}'.
"""
import sys, os, pickle, math
from multiprocessing import Pool
import cypari2
pari = cypari2.Pari()

SMALL = [int(x) for x in os.environ['SMALL'].split(',')] if os.environ.get('SMALL') else [3, 7, 5, 31, 127, 17, 73, 11, 23, 89, 13, 43, 151, 19, 41, 337, 29, 113, 37, 109, 61, 1321, 53, 157, 241, 71, 79, 103, 2731, 8191]
def ordtwo(p):
    return int(pari.znorder(pari.Mod(2, p)))
FP = {p: ordtwo(p) for p in SMALL}

import flint
def _to_poly(a):
    return flint.nmod_poly([int(ch) for ch in bin(a)[2:][::-1]], 2)
def _from_poly(P):
    cs = P.coeffs()
    return int(''.join(str(int(c)) for c in reversed(cs)), 2) if cs else 0
def clmul_mod(a, b, ell, mask):
    # carry-less product of two ell-bit ints mod x^ell - 1 (FLINT nmod_poly over F_2)
    P = _to_poly(a) * _to_poly(b)
    v = _from_poly(P)
    return (v & mask) ^ (v >> ell)

def is_one(y, ell, mask):
    t = y ^ 1
    return t == 0 or t == mask

def work(ell):
    n = (ell - 1) // 2
    mask = (1 << ell) - 1
    res = {}
    for p, d in FP.items():
        if n % d: continue
        # N_{n/d}(alpha) = prod_{j < n/d} (x^{a_j} + x^{-a_j}), a_j = 2^{d j} mod ell
        v = 1
        a = 1
        step = pow(2, d, ell)
        for j in range(n // d):
            v = (((v << a) | (v >> (ell - a))) ^ ((v << (ell - a)) | (v >> a))) & mask
            a = a * step % ell
        e = ((1 << d) - 1) // p
        # y = v^e  (square = coefficient permutation is overkill here; use clmul)
        y = 1; base = v
        while e:
            if e & 1: y = clmul_mod(y, base, ell, mask)
            e >>= 1
            if e: base = clmul_mod(base, base, ell, mask)
        res[p] = is_one(y, ell, mask)
    return ell, res

if __name__ == '__main__':
    L = int(sys.argv[1]); nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    ells = [int(l) for l in pari.primes([5, L]) if int(l) > 3 and int(pari.znorder(pari.Mod(2, l))) == int(l) - 1]
    print('ells', len(ells), flush=True)
    with Pool(nproc) as P:
        out = dict(P.imap_unordered(work, ells, chunksize=4))
    pickle.dump(out, open(f'gauss_chars_{L}_{os.environ.get("TAG","all")}.pkl', 'wb'))
    for p, d in FP.items():
        tests = [out[l][p] for l in out if p in out[l]]
        if not tests: continue
        obs = sum(tests); N = len(tests); exp = N / p
        sd = math.sqrt(N * (1/p) * (1 - 1/p))
        print(f'p={p:5d} f={d:3d} tests={N:5d} powers={obs:5d} expected={exp:8.2f} z={(obs-exp)/sd if sd else 0:+.2f}')
