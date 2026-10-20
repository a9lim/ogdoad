"""Emit the component tower (closure of Q(h)) for a row, in dependency order.

Line formats (ids are the prime powers q themselves):
  A q n id1..idn          y^2+y = prod(ids)             (2-power component)
  K q ell c n id1..idn    y^ell = c + sum(ids)          (odd Kummer layer)
Header: E h ; then Q-list; then per-component degree D.
"""
import sys
sys.argv=[sys.argv[0],'200000']+sys.argv[1:]
sys.path.insert(0,'..')
from census import *

def closure(Q):
    order=[]; seen=set()
    def visit(q):
        if q in seen: return
        f=factor(q); (r,a),=f.items()
        if r==2:
            for j in range(1,a): visit(2**j)
            seen.add(q); order.append(('A',q,[2**j for j in range(1,a)]))
            return
        if a>=2:
            visit(r**(a-1)); seen.add(q); order.append(('K',q,r,0,[r**(a-1)])); return
        fr=ordtwo(r); Qr=Qset(fr); m=rule(r,fr,Qr)
        ids=list(Qr); c=0
        if m==1: c=1
        elif m==4: ids=ids+[4]
        elif m!=0: raise ValueError(m)
        for x in ids: visit(x)
        seen.add(q); order.append(('K',q,r,c,ids))
    for q in Q: visit(q)
    return order
def D(q):
    f=factor(q); (r,a),=f.items()
    return q if r==2 else q*b(r)
def emit(p=None,h=None):
    if h is None: h=ordtwo(p)
    Q=Qset(h); E=dsum(Q)
    lines=[f"E {E} h {h}", "Q "+" ".join(map(str,Q))]
    for t in closure(Q):
        if t[0]=='A': lines.append(f"A {t[1]} {len(t[2])} "+" ".join(map(str,t[2])))
        else: lines.append(f"K {t[1]} {t[2]} {t[3]} {len(t[4])} "+" ".join(map(str,t[4])))
    lines.append("D "+" ".join(f"{t[1]}:{D(t[1])}" for t in closure(Q)))
    return "\n".join(lines)
if __name__=='__main__':
    for p in map(int,sys.argv[2:]):
        print(emit(p)); print('---')
