from functools import lru_cache
@lru_cache(None)
def nmul(a,b):
    if a<2 or b<2: return a*b
    # find largest Fermat 2-power F=2^(2^k) with F <= max(a,b)
    m=max(a,b); k=0
    while (1<<(1<<(k+1)))<=m: k+=1
    F=1<<(1<<k)
    a1,a0=divmod(a,F); b1,b0=divmod(b,F)
    c=nmul(a1,b1)
    hi = nmul(a1,b0)^nmul(a0,b1)^c
    lo = nmul(a0,b0)^nmul(c, F>>1)
    return hi*F ^ lo
def npow(a,e):
    r=1
    while e:
        if e&1: r=nmul(r,a)
        a=nmul(a,a); e>>=1
    return r
def order(a,grp):
    from sympy import factorint
    o=grp
    for q in factorint(grp):
        while o%q==0 and npow(a,o//q)==1: o//=q
    return o
print('nim 4 order', order(4,15), ' 2*2=',nmul(2,2), '4*4=',nmul(4,4))
print('nim 16 order in F256', order(16,255))
print('nim 256 order in F_2^16', order(256,65535))
print('nim 65536 order in F_2^32', order(65536,2**32-1))
