import sys; sys.argv=['x','1000']
from closure import *
import itertools
from cglob import sum_nodes_shared
out=[]
for p in primes[1:]:
    if p>727: break
    S=closure_alpha(p); E=deg(S)
    C=sum_nodes_shared(p) | {q for q in S if q%2==0}
    out.append((E,p,deg(frozenset(C))))
out.sort()
import collections
for B in (100,1000,3000,10000,30000,100000,300000,1e6):
    print(B, sum(1 for e in out if e[0]<=B))
print([o for o in out if o[0]<=30000][-10:])
print('max degK among E<=1e5', max(o[2] for o in out if o[0]<=1e5))
