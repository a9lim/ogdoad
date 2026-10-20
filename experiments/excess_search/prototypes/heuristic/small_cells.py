import sys, math
sys.argv=[sys.argv[0],'1000000']; sys.path.insert(0,'..')
import census as C
C.armcode=lambda h,Q: C.arm(h,Q)
C.Qset=C.Qset
import cypari2; P=cypari2.Pari(); P.allocatemem(2*10**9)
# b_r parity for all odd primes r <= 1e7
odd=C.primes[1:]
print('b_r odd for primes r<=1e6:', [r for r in odd if C.b(r)%2])
print('b_r mod 4 != 0 count:', sum(1 for r in odd if C.b(r)%4))
# O cells (r,a) with small L: check primality / squarefreeness of L' = L / r^v
for r in [5,7,11,13,17,19,23,29,31,37,41,43,47]:
    b=C.b(r)
    for a in (1,2):
        if (r**a - r**(a-1))*b > 700: continue
        L=P.polcyclo(r**a, 2**b)
        L=int(L)
        while L % r == 0: L//=r
        f=P.factor(L)
        rows=[int(x) for x in f[0]]
        sq=all(int(e)==1 for e in f[1])
        print(f'cell ({r},{a}) b={b} log2L~{(r**a-r**(a-1))*b} rows={rows} squarefree={sq} prime={len(rows)==1 and sq}')
# Wieferich check: which known Wieferich primes fall in which cell
for w in (1093,3511):
    h=C.ordtwo(w); Q=C.Qset(h); print('Wieferich',w,'f=',h,'Q=',Q,'arm',C.armcode(h,Q))
