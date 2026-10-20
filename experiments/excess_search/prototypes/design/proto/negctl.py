"""Negative control: Frobenius-twist the K-constant of ONE branch's base relation (wrong relative phase).
The norm must then differ from the term-algebra min poly whenever the twist is not an automorphism of the whole."""
import subprocess, sys
from terms import *
from plan import Planner
from tower import oracle_minpoly
def pmulmod(a,b,m):
    r=0; d=m.bit_length()-1
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if (a>>d)&1: a^=m
    return r
for p in map(int, sys.argv[1:]):
    pl=Planner(p); txt=pl.text().split('\n')
    PK=pl.PK
    binoms=[i for i,l in enumerate(txt) if ' BINOM ' in l]
    sums=[l for l in txt if ' SUM ' in l]
    if not sums or not binoms: print(p,'no sum/binom'); continue
    i=binoms[0]; parts=txt[i].split(); z=int(parts[3],16); z2=pmulmod(z,z,PK)
    parts[3]=f'{z2:x}'; txt[i]=' '.join(parts)
    open(f'/tmp/neg{p}.txt','w').write('\n'.join(txt))
    open(f'/tmp/pos{p}.txt','w').write(pl.text())
    E=deg(cl_alpha(p)); orc,L=oracle_minpoly(cl_alpha(p), alpha_monomials(p,0))
    res=[]
    for f in (f'/tmp/pos{p}.txt', f'/tmp/neg{p}.txt'):
        out=subprocess.run(['./exec',f,'n'],capture_output=True,text=True)
        nh=[l.split()[1] for l in out.stdout.split('\n') if l.startswith('NORM')]
        res.append(bool(nh) and int(nh[0],16)==orc)
    print(f'p={p} E={E} degK={pl.degK} correct_phase_match={res[0]} twisted_phase_match={res[1]} (z {z:x}->{z2:x})')
