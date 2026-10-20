import time, sys, random
import flint
t, n = int(sys.argv[1]), int(sys.argv[2])
ring = flint.fq_default_poly_ctx(2, t)
F = ring.base_field()
print("fq type:", F, getattr(F,'type',None) if hasattr(F,'type') else '')
rnd = random.Random(1)
def relt(): return F([rnd.randrange(2) for _ in range(t)])
def rpoly(d, monic=False):
    cs = [relt() for _ in range(d)] + ([F.one()] if monic else [])
    return ring(cs)
f = rpoly(n, True); a = rpoly(n); b = rpoly(n)
def tm(fn, reps=1):
    best=1e9
    for _ in range(reps):
        s=time.perf_counter(); fn(); best=min(best,time.perf_counter()-s)
    return best
print("mul", tm(lambda: a*b))
print("mulmod", tm(lambda: a.mul_mod(b, f)))
print("pow359", tm(lambda: a.pow_mod(359, f)))
print("gcd", tm(lambda: a.gcd(f)))
