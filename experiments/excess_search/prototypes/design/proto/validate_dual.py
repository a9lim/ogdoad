"""Validate dual builder: P == term-algebra min poly of alpha_p (E<=EO); P == Norm_K(G) of the GF2EX builder (E<=EN);
Euler(alpha_p) and Euler(alpha_p+1) vs OEIS/structural values (all rows E<=EE)."""
import sys, subprocess, time
from terms import *
from plan import Planner
from tower import oracle_minpoly
EE,EN,EO=map(int,sys.argv[1:4])
oeis=[int(x) for x in open('/Users/a9lim/Work/ogdoad/src/scalar/big/ordinal/b380496.txt').read().split()[1::2]]
known=dict(zip(primes[1:],oeis)); known[719]=1; known[727]=1
cnt={'rows':0,'oracle':0,'norm':0,'bad':0}
for p in primes[1:]:
    if p>727: break
    E=deg(cl_alpha(p))
    if E>EE: continue
    h=ordtwo(p); Q=Qset(h); m=rule(p,h,Q)
    pl=Planner(p); pl.full=True; txt=pl.text(); fn=f'/tmp/fdual_{p}.txt'; open(fn,'w').write(txt)
    out=subprocess.run(['./dual',fn,'ne'],capture_output=True,text=True)
    if out.returncode: print('FAIL',p,out.stderr); cnt['bad']+=1; continue
    L=out.stdout.split('\n'); P=int([l for l in L if l.startswith('MINPOLY')][0].split()[1],16)
    e0=int([l for l in L if l.startswith('EULER ')][0].split('=')[1]); e1=int([l for l in L if l.startswith('EULER_PLUS1')][0].split('=')[1])
    # m_p = rule exactly iff alpha_p (=kappa+rule) not a p-th power; for rule 1, alpha_p+1 = kappa must be p-th power
    good = (e0==0)==(known[p]==m)
    if m==1: good = good and e1==1
    tags=[]
    if E<=EO:
        orc,Lo=oracle_minpoly(cl_alpha(p), alpha_monomials(p,m)); ok=(orc==P and Lo==E); tags.append(f'oracle={ok}'); good&=ok; cnt['oracle']+=1
    elif E<=EN:
        o2=subprocess.run(['./exec',fn,'2n'],capture_output=True,text=True).stdout
        nh=int([l for l in o2.split('\n') if l.startswith('NORM')][0].split()[1],16); ok=(nh==P); tags.append(f'norm={ok}'); good&=ok; cnt['norm']+=1
    cnt['rows']+=1; cnt['bad']+= (not good)
    print(f'p={p} E={E} m_rule={m} oeis={known[p]} alpha_pth={e0} alpha+1_pth={e1} {" ".join(tags)} {"OK" if good else "BAD"}',flush=True)
print(cnt)
