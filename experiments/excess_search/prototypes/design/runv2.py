import sys, subprocess, pickle, re
ARGS=[int(x) for x in sys.argv[1:] if x!='--rel']
RELONLY='--rel' in sys.argv
from mcstruct import *
from gentower import emit, closure
rows=pickle.load(open('../rows_1000000.pkl','rb'))
byh={}
for r in rows: byh.setdefault(r[1],[]).append(r[0])
def prime_of(q): return min(factor(q))
def clos(qs):
    return [t[1] for t in closure(qs)]
def deg(S):
    d=1
    for q in S: d*=prime_of(q)
    return d
def gpvec(L): return "["+",".join(map(str,L))+"]"
def v1(p):
    out=subprocess.run(['./mcverify',f'tw_{p}.txt',f'tk_{p}.txt'],capture_output=True,text=True).stdout
    m=re.search(r'minpoly_exps (.*)',out); exps=list(map(int,m.group(1).split()))
    eul=re.findall(r'euler p=(\d+) f\(p\)=\d+ kappa_is_pth_power=(\d)',out)
    return exps,[int(b) for _,b in eul]
for p in ARGS:
    I=row_info(p); h=I['h']; e0=I['e0']; cs=I['cs']; Q=I['Q']
    big=[c for c in cs if c['D']//gcd(c['D'],e0)>1 and c['r']!=2 and c['a']==1]
    if not big: print(p,'no odd a=1 big component'); continue
    y=max(big,key=lambda c:c['D']); r=y['q']
    smalls=[q for q in Q if q!=r]
    SA=clos(smalls); Sy=clos([r]); Sg=[q for q in SA if q in Sy]
    g=deg(Sg); A=deg(SA); b=y['b']; fr=y['fr']
    ex=lcm(lcm(e0,fr),A)
    tw=[]
    for t in closure(Q):
        if t[0]=='A': tw.append(f"[1,{t[1]},2,0,{gpvec(t[2])}]")
        else: tw.append(f"[2,{t[1]},{t[2]},{t[3]},{gpvec(t[4])}]")
    plist=byh.get(h,[p])
    exps,eulv1=v1(p)
    v1poly=[0]*(max(exps)+1)
    for e in exps: v1poly[e]=1
    v1str=gpvec(v1poly[::-1])
    gp=f"""default(parisizemax, 4000000000);
read("v2lib.gp");
tw={gpvec(tw)}; Sg=Set({gpvec(Sg)}); SA=Set({gpvec(SA)}); Sy=Set({gpvec(Sy)}); sm={gpvec(smalls)};
V1={v1str};
cr=crossed(tw,Sg,SA,Sy,sm,{r},{g},{A},{b},{fr},{ex},{h},{gpvec(plist)});
print("crossed: n'=",cr[3]," t=",cr[4]," minpoly==V1: ", lift(cr[1])==V1, " euler: ", cr[2]);
ff=freefactor(tw,Sg,SA,Sy,sm,{r},{g},{A},{b},{e0},{h},{gpvec(plist)},0);
print("freefactor: #factors=",#ff," degs=",vector(#ff,i,ff[i][1])," minpoly==V1: ",vector(#ff,i,lift(ff[i][2])==V1), " euler: ", vector(#ff,i,ff[i][3]));
rc=relcross(tw,Sg,SA,Sy,sm,{r},{g},{A},{b},{fr},{ex},{h},{gpvec(plist)});
print("relcross: n'=",rc[3]," t=",rc[4]," root ok=",rc[5]," N(alpha)=P(0) ok=",rc[6]," minpoly==V1: ", lift(rc[1])==V1, " euler: ", rc[2]);
fb=freefactor(tw,Sg,SA,Sy,sm,{r},{g},{A},{b},{e0},{h},{gpvec(plist)},1);
print("unpinned (F_s' embedding twisted by Frobenius^1): minpoly==V1: ",vector(#fb,i,lift(fb[i][2])==V1));
"""
    open(f'v2_{p}.gp','w').write(gp)
    print(f"=== p={p} h={h} Q={Q} big=chi_{r} b={b} f(r)={fr} g={g} A={A} e0={e0} ex={ex} V1 euler={eulv1}",flush=True)
    res=subprocess.run(['/Users/a9lim/.local/micromamba/envs/excess/bin/gp','-q'],input=open(f'v2_{p}.gp').read(),capture_output=True,text=True,timeout=3000)
    print(res.stdout.strip(), res.stderr.strip()[-500:],flush=True)
