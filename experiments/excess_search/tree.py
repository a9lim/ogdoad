import pickle, sys
from census import *
def show(p, depth=0, seen=None):
    h=ordtwo(p); Q=Qset(h); a=arm(h,Q); m=rule(p,h,Q)
    E=lcm(dsum(Q), d_finite(m))
    print('  '*depth+f"p={p} h={h}={dict(factor(h))} Q={Q} arm={a} m={m} E={E} E/h={E//h}")
    for q in Q:
        r=min(factor(q))
        if r>2 and depth<6: show(r, depth+1)
for p in map(int, sys.argv[1:]): show(p); print()
