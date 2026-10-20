"""Structural statistics for multi-component arm-Z rows."""
import sys, math, pickle
sys.argv=[sys.argv[0], '200000'] + sys.argv[1:]
sys.path.insert(0,'..')
from census import *
from math import gcd

def comps(h):
    out=[]
    for q in Qset(h):
        f=factor(q); (r,a),=f.items()
        if r==2: out.append(dict(q=q,r=2,a=a,R=q,b=1,D=q))
        else: out.append(dict(q=q,r=r,a=a,R=q,b=b(r),D=q*b(r),fr=ordtwo(r)))
    return out
def vals(n):
    return factor(n) if n>1 else {}
def second_max_field(Ds):
    primes=set()
    for D in Ds: primes|=set(vals(D))
    G=1
    for l in primes:
        vs=sorted((vals(D).get(l,0) for D in Ds), reverse=True)+[0]
        G*=l**vs[1]
    return G
def row_info(p):
    h=ordtwo(p); Q=Qset(h); cs=comps(h)
    Ds=[c['D'] for c in cs]
    E=1
    for D in Ds: E=lcm(E,D)
    G=second_max_field(Ds)
    e0=lcm(h,G)
    for c in cs:
        c['n']=c['D']//gcd(c['D'],e0)
        c['cross']= (c['r']!=2 and e0 % c['fr']==0)
    return dict(p=p,h=h,Q=Q,E=E,G=G,e0=e0,cs=cs)
if __name__=='__main__':
    for p in map(int, sys.argv[2:]):
        I=row_info(p)
        print(p, 'h',I['h'],'E',I['E'],'G',I['G'],'e0',I['e0'],'E/e0',I['E']//I['e0'])
        for c in I['cs']: print('   ',c)
