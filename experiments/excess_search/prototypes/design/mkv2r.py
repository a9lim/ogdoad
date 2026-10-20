import sys, re, pickle
ARGS=[int(x) for x in sys.argv[1:]]
from mcstruct import *
from gentower import closure
rows=pickle.load(open('../rows_1000000.pkl','rb'))
byh={}
for r in rows: byh.setdefault(r[1],[]).append(r[0])
def prime_of(q): return min(factor(q))
def clos(qs): return [t[1] for t in closure(qs)]
def deg(S):
    d=1
    for q in S: d*=prime_of(q)
    return d
def gpvec(L): return "["+",".join(map(str,L))+"]"
logs=open('v1_big.txt').read()+open('v1_known.txt').read()
for p in ARGS:
    blk=logs.split(f'=== p={p} ')[1]
    exps=list(map(int,re.search(r'minpoly_exps (.*)',blk).group(1).split()))
    I=row_info(p); h=I['h']; e0=I['e0']; cs=I['cs']; Q=I['Q']
    big=[c for c in cs if c['D']//gcd(c['D'],e0)>1 and c['r']!=2 and c['a']==1]
    y=max(big,key=lambda c:c['D']); r=y['q']
    smalls=[q for q in Q if q!=r]
    SA=clos(smalls); Sy=clos([r]); Sg=[q for q in SA if q in Sy]
    g=deg(Sg); A=deg(SA); b=y['b']; fr=y['fr']; ex=lcm(lcm(e0,fr),A)
    tw=[]
    for t in closure(Q):
        if t[0]=='A': tw.append(f"[1,{t[1]},2,0,{gpvec(t[2])}]")
        else: tw.append(f"[2,{t[1]},{t[2]},{t[3]},{gpvec(t[4])}]")
    v1poly=[0]*(max(exps)+1)
    for e in exps: v1poly[e]=1
    plist=byh.get(h,[p])
    open(f'v2r_{p}.gp','w').write(f"""default(parisizemax, 4000000000);
read("v2lib.gp");
tw={gpvec(tw)}; Sg=Set({gpvec(Sg)}); SA=Set({gpvec(SA)}); Sy=Set({gpvec(Sy)}); sm={gpvec(smalls)};
V1={gpvec(v1poly[::-1])};
cr=crossed(tw,Sg,SA,Sy,sm,{r},{g},{A},{b},{fr},{ex},{h},{gpvec(plist)});
print("p={p} crossed: n'=",cr[3]," t=",cr[4]," minpoly==V1: ", lift(cr[1])==V1, " euler: ", cr[2]);
rc=relcross(tw,Sg,SA,Sy,sm,{r},{g},{A},{b},{fr},{ex},{h},{gpvec(plist)});
print("p={p} relcross: n'=",rc[3]," t=",rc[4]," root ok=",rc[5]," N(alpha)=P(0) ok=",rc[6]," minpoly==V1: ", lift(rc[1])==V1, " euler: ", rc[2]);
""")
    print('wrote',p)
