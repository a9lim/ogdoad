import sys
from closure import *
import collections, math
LIM=int(sys.argv[1])
def odd_nodes(S):
    return sorted({comp_prime(q)[0] for q in S if q%2==1})
rows=[]
for p in primes[1:]:
    if p<=727 or p>LIM: continue
    h=ordtwo(p); Q=Qset(h); a=arm(h,Q); m=rule(p,h,Q)
    S=closure_alpha(p); E=deg(S)
    rows.append((p,h,Q,a,m,E,S))
print('rows',len(rows))
# chain-ness: is the closure poset a chain of odd nodes over the 2-power bottom? define 'free' if every odd node r in S has singleton Q(f(r)) and the full closure is reachable by compositions
@lru_cache(None)
def free_alpha(r):
    """alpha_r min poly obtainable purely by compositions X^R, X+1 from 2-power bottom with a single chi_{2^k}"""
    h=ordtwo(r); Q=Qset(h); m=rule(r,h,Q)
    if len(Q)!=1: return False
    q=Q[0]; rr,k=comp_prime(q)
    if m>=2: return False   # m=4 adds chi_4 sum (not free)
    if rr==2: return True   # chi_{2^k} min poly is known small
    return free_alpha(rr)
cnt=collections.Counter(); mass=collections.Counter()
for (p,h,Q,a,m,E,S) in rows:
    if len(Q)==1:
        rr,k=comp_prime(Q[0])
        free = (rr==2) or (free_alpha(rr) and m<2)
        key=(a,'free-chain' if free else 'nonfree')
    else:
        key=(a,f'|Q|={len(Q)}')
    cnt[key]+=1; mass[key]+=1/p
for k in sorted(cnt): print(k,cnt[k],round(mass[k],4))
# closure-node reuse
use=collections.Counter()
for (p,h,Q,a,m,E,S) in rows:
    for r in odd_nodes(S): use[r]+=1
print('distinct odd closure nodes',len(use))
print('top reuse',use.most_common(15))
big=[r for r in use if r>727]
print('closure nodes >727:',len(big), 'max', max(big) if big else None)
# for multi-Q: pairwise shared degree
import itertools
sh=collections.Counter()
for (p,h,Q,a,m,E,S) in rows:
    if len(Q)>=2:
        cl=[closure_q(q) for q in Q]
        g=max(deg(x&y) for x,y in itertools.combinations(cl,2))
        sh[g]+=1
print('max pairwise shared degree among Q branches (multi-Q rows):',sorted(sh.items())[:30])
