"""Cost model for multi-component (and, for reference, singleton) rows.

Primitive timings: NTL on the M5 (SPEC.md table, sparse modulus), log-log
interpolated; seconds.  All costs are estimates of *operation counts* times
these unit costs, not measurements.
"""
import sys, math, pickle, itertools, collections
ARGS=sys.argv[1:]
from mcstruct import *
from gentower import closure
LS=[(1e3,5e-8),(1e4,5e-7),(1e5,4e-6),(1e6,4.1e-5),(1e7,4.2e-4)]
LM=[(1e3,1.0e-6),(1e4,2.6e-5),(1e5,9e-4),(1e6,1.18e-2),(1e7,0.424)]
def interp(T,n):
    n=max(n,2.0)
    if n<=T[0][0]:
        (x0,y0),(x1,y1)=T[0],T[1]
    elif n>=T[-1][0]:
        (x0,y0),(x1,y1)=T[-2],T[-1]
    else:
        for i in range(len(T)-1):
            if T[i][0]<=n<=T[i+1][0]: (x0,y0),(x1,y1)=T[i],T[i+1]; break
    s=math.log(y1/y0)/math.log(x1/x0)
    return y0*(n/x0)**s
S=lambda n: interp(LS,n)
M=lambda n: interp(LM,n)
lg=lambda x: math.log2(max(x,2))
def euler_poly(e,h): return 2*e*S(e)+(lg(e)+h/6+10)*M(e)
TENSOR=True
def euler(e,h,e0=None):
    # polynomial-model Euler test, or (TENSOR) descent in the tensor model F_A (x) F_t[V]/(V^R-c):
    # Frobenius acts factorwise (cheap), so only multiplications at size e are paid.
    c=euler_poly(e,h)
    if TENSOR and e0 is not None and e0<e:
        o=e//e0
        c=min(c, 2*(lg(e/h)+h/6+o+10)*M(e))
    return c
def build(Ds,n):   # build a model of F_n containing components with degrees Ds (crossed roots in F_n)
    return sum(5*D*S(n)+60*M(n) for D in Ds)
def croot(b,f): return 5*b*S(b)+(lg(b)**2+f/6+20)*M(b)
def fa(b,n1): return b*S(b)+(lg(n1+1)*M(b*n1) if n1>1 else 0)+n1*M(b)
def compdeg(q):
    f=factor(q); (r,a),=f.items(); return q if r==2 else q*b(r)
def closure_degs(qs):
    return [compdeg(t[1]) for t in closure(qs)]
def row_costs(p):
    I=row_info(p); h=I['h']; e0=I['e0']; cs=I['cs']; E=I['E']
    out={}
    out['D']=build(closure_degs(I['Q']),E)+euler(E,h)
    big=[c for c in cs if c['D']//gcd(c['D'],e0)>1]
    smalls=[c for c in cs if c not in big]
    A=1
    for c in smalls: A=lcm(A,c['D'])
    best=None
    for k in range(len(big)+1):
        for C in itertools.combinations(range(len(big)),k):
            if any(big[i]['r']==2 or big[i]['a']!=1 for i in C): continue
            exb=e0
            for i in C: exb=lcm(exb,big[i]['fr'])
            cands={exb}
            for i in C: cands.add(lcm(exb,big[i]['b']))
            for ex in cands:
                if E%ex: continue
                cost=0; ns=[]
                for i,c in enumerate(big):
                    if i in C:
                        bb=c['b']; t1=gcd(bb,ex); n1=bb//t1
                        cost+=build(closure_degs([c['r']])[:-1],bb)+croot(bb,c['fr'])+fa(bb,n1)
                        ns.append(n1)
                    else:
                        D=c['D']; n=D//gcd(D,ex)
                        cost+=build(closure_degs([c['q']]),D)+3*D*S(D)+(lg(n)*M(D*n) if n>1 else 0)
                        ns.append(n)
                if len(ns)==1: cost+=ns[0]*M(ex)
                elif len(ns)>=2: cost+=sum(ns)*lg(sum(ns))*2*M(ex)*(math.prod(ns[2:]) if len(ns)>2 else 1)
                cost+=euler(ex,h,e0)+(build(closure_degs([c['q'] for c in smalls]),max(c['D'] for c in smalls)) if smalls else 0)
                if best is None or cost<best[0]: best=(cost,C,ex)
    out['best']=best[0]; out['bestC']=best[1]; out['ex']=best[2]
    return I,out
def singleton_cost(p):
    # arm O/C/D style: beta = chi_R + m, crossed (719-style) vs direct
    I=row_info(p); h=I['h']; c=I['cs'][0]; E=I['E']
    if c['r']==2: return None
    R=c['R']; bb=c['b']; ex=lcm(h,R*c['fr']); t1=gcd(bb,ex); n1=bb//t1
    direct=build(closure_degs(I['Q']),E)+euler(E,h)
    crossed=build(closure_degs([c['r']])[:-1],bb)+croot(bb,c['fr'])+fa(bb,n1)+n1*M(ex)+euler(ex,h)
    return dict(E=E,ex=ex,b=bb,t=t1,n1=n1,direct=direct,crossed=crossed)
if __name__=='__main__':
    for p in map(int,ARGS):
        I=row_info(p)
        if len(I['Q'])>=2:
            I,o=row_costs(p)
            print(f"p={p} h={I['h']} Q={I['Q']} E={I['E']} e0={I['e0']} -> best ex={o['ex']} crossed={o['bestC']}  direct~{o['D']:.3g}s best~{o['best']:.3g}s")
        else:
            s=singleton_cost(p); print(f"p={p} h={I['h']} Q={I['Q']} singleton: {s}")

# ---------------------------------------------------------------------------
# Regime (b): coprime-tensor models F_n = F_2[x,y]/(P1(x),P2(y)), n1*n2=n coprime,
# n1~n2~sqrt(n).  Frobenius sigma^m = sx^(m mod n1) o sy^(m mod n2): <= n1+n2
# linear-time partial squarings, i.e. ~ n*(n1+n2)/64 word ops.  Multiplication via
# bivariate Kronecker ~ 6 M(n).
WORD=0.35e-9
def FrobT(n): return WORD*n*2*math.sqrt(n)/64+2*n*S(n)/max(1,math.sqrt(n))
def MT(n): return 6*M(n)
def eulerT(e,h): return lg(e/h+1)*(FrobT(e)+MT(e))+FrobT(e)
def crootT(bb,f): return 3*lg(bb)*FrobT(bb)+(lg(bb)**2+f/6+20)*MT(bb)
def buildT(Ds,n): return len(Ds)*crootT(n,50)
def faT(bb,n1): return n1*FrobT(bb)+(lg(n1+1)*MT(bb*n1) if n1>1 else 0)+n1*MT(bb)
def row_costs_T(p):
    I=row_info(p); h=I['h']; e0=I['e0']; cs=I['cs']; E=I['E']
    direct=buildT(closure_degs(I['Q']),E)+eulerT(E,h)
    big=[c for c in cs if c['D']//gcd(c['D'],e0)>1]
    smalls=[c for c in cs if c not in big]
    best=None
    for k in range(len(big)+1):
        for C in itertools.combinations(range(len(big)),k):
            if any(big[i]['r']==2 or big[i]['a']!=1 for i in C): continue
            exb=e0
            for i in C: exb=lcm(exb,big[i]['fr'])
            for ex in {exb}|{lcm(exb,big[i]['b']) for i in C}:
                if E%ex: continue
                cost=0; ns=[]
                for i,c in enumerate(big):
                    if i in C:
                        bb=c['b']; n1=bb//gcd(bb,ex)
                        cost+=buildT(closure_degs([c['r']])[:-1],bb)+crootT(bb,c['fr'])+faT(bb,n1); ns.append(n1)
                    else:
                        D=c['D']; n=D//gcd(D,ex)
                        cost+=buildT(closure_degs([c['q']]),D)+n*FrobT(D)+(lg(n)*MT(D*n) if n>1 else 0); ns.append(n)
                if len(ns)==1: cost+=ns[0]*MT(ex)
                elif len(ns)>=2: cost+=sum(ns)*lg(sum(ns))*2*MT(ex)*(math.prod(ns[2:]) if len(ns)>2 else 1)
                cost+=eulerT(ex,h)
                if best is None or cost<best[0]: best=(cost,C,ex)
    return dict(D=direct,best=best[0],ex=best[2],C=best[1])
def singleton_cost_T(p):
    I=row_info(p); h=I['h']; c=I['cs'][0]; E=I['E']
    if c['r']==2: return None
    R=c['R']; bb=c['b']; ex=lcm(h,R*c['fr']); n1=bb//gcd(bb,ex)
    direct=buildT(closure_degs(I['Q']),E)+eulerT(E,h)
    crossed=buildT(closure_degs([c['r']])[:-1],bb)+crootT(bb,c['fr'])+faT(bb,n1)+n1*MT(ex)+eulerT(ex,h)
    return dict(direct=direct,crossed=crossed,ex=ex,n1=n1)
