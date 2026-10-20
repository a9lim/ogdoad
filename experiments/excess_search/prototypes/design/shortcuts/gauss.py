"""Analog test: selected cyclotomic elements gamma_N = zeta+zeta^-1 (and 1+zeta when
-1 not in <2> mod N) for primes N.  For each prime ell<=LMAX with f(ell) | n
(n = degree of the element), record whether the element is an ell-th power in
F_(2^n).  Random model: 1/ell.  'new' = f(ell) == n (row analog)."""
import sys, pickle, time
import cypari2
pari = cypari2.Pari(); pari.allocatemem(2*10**9)
sys.path.insert(0, '/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search')
NMAX, DMAX, LMAX, W, I = map(int, sys.argv[1:6])
def isprime(n): return n > 1 and all(n % d for d in range(2, int(n**0.5)+1))
def ordmod(a, n):
    return int(pari.znorder(pari.Mod(a, n)))
lprimes = [l for l in range(3, LMAX+1, 2) if isprime(l)] 
fl = {l: ordmod(2, l) for l in lprimes}
out = open(f'gauss_{I}.pkl', 'ab')
Ns = [N for N in range(5, NMAX+1) if isprime(N)][I::W]
for N in Ns:
    D = ordmod(2, N)
    if D > DMAX: continue
    g = pari(f"ffgen(ffinit(2,{D}),'t)")
    one = g**0
    zeta = g ** (((1 << D) - 1) // N)
    j = 1
    while zeta == one:
        j += 1; zeta = pari.random(g) ** (((1 << D) - 1) // N)
    elems = {}
    minus1 = pow(2, D//2, N) == N-1 if D % 2 == 0 else False
    n = D//2 if minus1 else D
    elems['gamma'] = (zeta + zeta**-1, n)
    if not minus1:
        elems['1+zeta'] = (one + zeta, D)
    res = []
    for name, (x, deg) in elems.items():
        assert x ** (1 << deg) == x
        M = (1 << deg) - 1
        for l in lprimes:
            if deg % fl[l]: continue
            res.append(dict(N=N, D=D, deg=deg, elem=name, ell=l, f=fl[l], new=(fl[l]==deg), power=bool(x**(M//l) == one)))
    pickle.dump(res, out); out.flush()
    print(N, D, n, flush=True)
