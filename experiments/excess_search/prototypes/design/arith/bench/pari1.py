import cypari2, time, sys
pari = cypari2.Pari(); pari.allocatemem(8*10**9)
print(pari.version())
t, n = int(sys.argv[1]), int(sys.argv[2])
pari(f"g = ffgen(ffinit(2,{t}),'a); setrand(1);")
pari(f"f = x^{n} + sum(i=0,{n-1}, random(g)*x^i); a = sum(i=0,{n-1}, random(g)*x^i); b = sum(i=0,{n-1}, random(g)*x^i);")
for name, cmd in [("mul","c=a*b;"),("mulmod","c=(a*b)%f;"),("resultant","r=polresultant(f,a);"),("gcd","r=gcd(f,a);")]:
    s=time.perf_counter(); pari(cmd); print(name, time.perf_counter()-s, flush=True)
