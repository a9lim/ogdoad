import sys
from closure import *
import collections, itertools
LIM=int(sys.argv[1])
@lru_cache(None)
def sum_nodes_shared(r):
    """union of pairwise branch intersections over all Sum nodes in cl(alpha_r) incl. r itself"""
    h=ordtwo(r); Q=Qset(h); m=rule(r,h,Q)
    br=[closure_q(q) for q in Q]
    if m>=2:  # arm D: alpha = chi_q + chi_4
        br.append(frozenset({2,4}))
    C=set()
    for x,y in itertools.combinations(br,2): C|=x&y
    for q in Q:
        rr,k=comp_prime(q)
        if rr>2: C|=sum_nodes_shared(rr)
    return frozenset(C)
rows=[]
for p in primes[1:]:
    if p<=727 or p>LIM: continue
    rows.append(p)
dist=collections.Counter(); sets=collections.Counter(); massd=collections.Counter()
for p in rows:
    C=sum_nodes_shared(p); d=deg(C)
    dist[d]+=1; sets[C]+=1; massd[d]+=1/p
print('deg(C_glob) histogram', sorted(dist.items()))
print('mass by deg', {k:round(v,4) for k,v in sorted(massd.items())})
print('distinct C_glob sets',len(sets))
for C,n in sets.most_common(12): print(n, sorted(C), deg(C))
# nodes paired with C: distinct (node r, C restricted) pairs
pairs=set()
for p in rows:
    C=sum_nodes_shared(p)
    for q in closure_alpha(p):
        if q%2:
            r=comp_prime(q)[0]
            pairs.add((r, C & closure_alpha(r)))
print('distinct (node, C∩cl(node)) pairs', len(pairs))
