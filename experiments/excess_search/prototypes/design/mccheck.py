import pickle, sys
from mcstruct import *
LIM=int(sys.argv[2])
out=pickle.load(open(f'mc_{LIM}.pkl','rb'))
shared_r=0; ex=[]
for o in out:
    cs=o['cs']
    for c in cs:
        if c['r']==2: continue
        for d in cs:
            if d is c: continue
            if d['D'] % c['r']==0:
                shared_r+=1; ex.append((o['p'],c['q'],d['q'],d['D']))
print('component prime r_i dividing another D_j:',shared_r, ex[:20])
# 3-big-comp at ex? number of big at ex
import collections
c=collections.Counter(sum(1 for x in o['cs'] if x['D']//gcd(x['D'],o['ex'])>1) for o in out)
print('num comps with n>1 at ex:',dict(c))
