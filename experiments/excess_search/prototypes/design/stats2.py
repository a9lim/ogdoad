import sys
from closure import *
import collections, math, itertools
LIM=int(sys.argv[1])
rows=[]
for p in primes[1:]:
    if p<=727 or p>LIM: continue
    h=ordtwo(p); Q=Qset(h); a=arm(h,Q); m=rule(p,h,Q)
    rows.append((p,h,Q,a,m))
@lru_cache(None)
def b_of(r): return deg(closure_alpha(r))
@lru_cache(None)
def node_kind(r):
    h=ordtwo(r); Q=Qset(h); m=rule(r,h,Q)
    if len(Q)==1 and m<2: return 'chain'
    if len(Q)==1: return 'D'
    return 'multi%d'%len(Q)
@lru_cache(None)
def node_shared(r):
    h=ordtwo(r); Q=Qset(h)
    cl=[closure_q(q) for q in Q]
    C=frozenset().union(*[x&y for x,y in itertools.combinations(cl,2)]) if len(cl)>1 else frozenset()
    return deg(C)
# nodes needed: all odd r in closure of any row, plus the rows themselves as "nodes" (their top alpha)
nodes=collections.Counter()
for (p,h,Q,a,m) in rows:
    for q in closure_alpha(p):
        if q%2: nodes[comp_prime(q)[0]]+=1
print('distinct closure nodes',len(nodes))
kinds=collections.Counter(node_kind(r) for r in nodes)
print('node kinds',kinds)
nonfree=[(b_of(r),r,node_kind(r),node_shared(r),nodes[r]) for r in nodes if node_kind(r)!='chain']
nonfree.sort()
print('nonchain closure nodes: count',len(nonfree))
for qq in (0.5,0.9,0.99,1.0):
    print(' b quantile',qq,nonfree[min(len(nonfree)-1,int(qq*len(nonfree)))][:4])
print(' max shared degree at nonchain nodes',max(x[3] for x in nonfree))
allb=sorted(b_of(r) for r in nodes)
print('all closure-node b: median',allb[len(allb)//2],'max',allb[-1])
print('sum b over nodes (bits)',sum(allb))
# rows: E, and shared degree of top
Es=collections.Counter()
for (p,h,Q,a,m) in rows:
    E=b_of(p)
    for B in (1e4,1e5,1e6,1e7,1e8,1e9,1e10,1e12):
        if E<=B: Es[B]+=1; break
    else: Es['inf']+=1
print('row E histogram (<=bucket)',sorted(Es.items(),key=lambda t:float(t[0]) if t[0]!='inf' else 1e99))
