import sys, math, pickle, collections
from mcstruct import *
LIM=int(sys.argv[2])
rows=pickle.load(open('../rows_1000000.pkl','rb'))
out=[]
for (p,h,Q,arm_,m,E) in rows:
    if not (727<p<=LIM and arm_=='Z'): continue
    I=row_info(p)
    cs=I['cs']; e0=I['e0']
    big=[c for c in cs if c['n']>1]
    ex=e0
    for c in big:
        if c['r']!=2: ex=lcm(ex,c['fr'])
    for c in big:
        c['t']=gcd(c['b'],ex) if c['r']!=2 else None
        c['nx']=c['D']//gcd(c['D'],ex)
    out.append(dict(p=p,h=h,Q=Q,E=E,e0=e0,ex=ex,big=big,cs=cs))
cnt=collections.Counter(len(o['big']) for o in out)
print('rows',len(out),'num big comps at e0:',dict(cnt))
# E vs ex
import statistics
def q(xs,f): xs=sorted(xs); return xs[int(f*(len(xs)-1))]
for key in ('E','e0','ex'):
    xs=[o[key] for o in out]
    print(key,[q(xs,f) for f in (0.1,0.25,0.5,0.75,0.9,0.99)], 'max',max(xs))
xs=[max([c['b'] for c in o['big']] or [0]) for o in out]
print('max big b',[q(xs,f) for f in (0.1,0.25,0.5,0.75,0.9,0.99)],max(xs))
xs=[max([c['D'] for c in o['big']] or [0]) for o in out]
print('max big D',[q(xs,f) for f in (0.1,0.25,0.5,0.75,0.9,0.99)],max(xs))
print('E==ex rows', sum(o['E']==o['ex'] for o in out), 'E==e0', sum(o['E']==o['e0'] for o in out))
print('big comps with a>=2', sum(1 for o in out for c in o['big'] if c['a']>=2 and c['r']!=2), 'even big', sum(1 for o in out for c in o['big'] if c['r']==2))
pickle.dump(out,open(f'mc_{LIM}.pkl','wb'))
for o in out[:40]:
    print(o['p'],o['h'],o['Q'],'E',o['E'],'e0',o['e0'],'ex',o['ex'],[(c['q'],c['b'],c['D'],c['n'],c.get('t'),c.get('nx')) for c in o['big']])
