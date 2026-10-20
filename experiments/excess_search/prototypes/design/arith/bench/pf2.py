import time, random, flint
for n in (10**4, 10**5, 10**6, 10**7):
    r = random.Random(n)
    a = flint.nmod_poly([r.randrange(2) for _ in range(n)], 2)
    b = flint.nmod_poly([r.randrange(2) for _ in range(n)], 2)
    best = 1e9
    for _ in range(3):
        s = time.perf_counter(); c = a*b; best = min(best, time.perf_counter()-s)
    print(n, "nmod_poly mod2 mul s", best, flush=True)
