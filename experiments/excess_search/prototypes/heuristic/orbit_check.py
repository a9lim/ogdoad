import sys, time; sys.path.insert(0,'/Users/a9lim/Work/ogdoad/experiments')
from ordinal_excess_probe import TermAlgebra
def el(T, comps=(), const=()):
    s=set()
    for q in comps: s ^= {T.basis[T.index[q]]}
    for t in const: s ^= {t}
    return frozenset(s)
def nim(T, n):  # finite nimber n as element (only 2-power components 2,4,8 present)
    # nimber bits: basis for chi_2,chi_4,chi_8 components is index-based; build via products
    out=set()
    pw=[q for q in T.q_components if q&(q-1)==0]
    for bit in range(n.bit_length()):
        if n>>bit & 1:
            # bit b of a nimber = product of chi_{2^(i+1)} over set bits i of b
            t=0
            for i in range(bit.bit_length()):
                if bit>>i & 1: t += T.basis[T.index[2**(i+1)]]
            out ^= {t}
    return frozenset(out)
def conjugates(T, x, n):
    out=[x]; y=x
    for _ in range(n-1):
        y=T.square(y); out.append(y)
    return out
t0=time.time()
# (a) Z h=15, Q={3,5}: kappa = chi_3+chi_5, degree 60
T=TermAlgebra((2,4,3,5)); k=el(T,(3,5)); E=60
cj=conjugates(T,k,E)
print('h=15 orbit size', len(set(cj)), 'deg', E)
units=[nim(T,1),nim(T,2),nim(T,3)]
hits=[]
for j,c in enumerate(cj):
    for m in range(16):
        for u in units:
            if c==T.multiply(u, T.multiply(frozenset((0,)), k) ^ nim(T,m)) and (j,m,u)!=(0,0,units[0]):
                hits.append((j,m,sorted(u)))
print('h=15 conj = u*(kappa+m), u in F4*, m<16 (nontrivial):', hits)
# (b) O r=7: d(chi_7+2) should be 42
T=TermAlgebra((2,3,7)); x=el(T,(7,)); x2=x ^ nim(T,2)
print('r=7: orbit(chi_7+2) =', len(set(conjugates(T,x2,42))), ' orbit(chi_7)=', len(set(conjugates(T,x,42))))
# (c) Z h=24, Q={3,8}: Frob^12(kappa)=kappa+1, Frob^12(kappa+2)=kappa+3
T=TermAlgebra((2,4,8,3)); k=el(T,(3,8))
f12=lambda z: T.power(z, 2**12)
print('h=24: Frob^12(kappa)==kappa+1', f12(k)==k^nim(T,1), ' Frob^12(kappa+2)==kappa+3', f12(k^nim(T,2))==k^nim(T,3),
      ' Frob^12(kappa+4)==kappa+5', f12(k^nim(T,4))==k^nim(T,5))
print('secs', round(time.time()-t0,1))
