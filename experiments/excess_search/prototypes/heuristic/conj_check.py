import sys; sys.path.insert(0,'/Users/a9lim/Work/ogdoad/experiments')
from ordinal_excess_probe import TermAlgebra
def el(T,*qs_and_consts):
    s=set()
    for x in qs_and_consts:
        t = T.basis[T.index[x]] if isinstance(x,int) else x[1]
        s ^= {t}
    return frozenset(s)
ONE=('c',0)
# p=13: kappa_12 = chi_3 + chi_4 ; d(chi_3)=6
T=TermAlgebra((2,4,3)); k=el(T,3,4); k1=el(T,3,4,ONE)
print('Z h=12: Frob^6(kappa)==kappa+1 :', T.power(k,2**6)==k1)
# p=29: Q=(4,7)
T=TermAlgebra((2,4,3,7)); k=el(T,4,7); k1=el(T,4,7,ONE)
print('Z h=28: Frob^42(kappa)==kappa+1 :', T.power(k,2**42)==k1)
# D, k=2: zeta=chi_9, h=9 ; Frob^{2h}(zeta+4)==zeta+5
T=TermAlgebra((2,4,3,9)); z4=el(T,9,4); z5=el(T,9,4,ONE)
print('D k=2: Frob^18(zeta+4)==zeta+5 :', T.power(z4,2**18)==z5)
# C,k=2: zeta+2 == omega * Frob^j(zeta+1), j=4*3^(k-1)=12
w=el(T,2); z1=el(T,9,ONE); z2=el(T,9,2)
print('C k=2: zeta+2 == omega*Frob^12(zeta+1):', T.multiply(w,T.power(z1,2**12))==z2)
# D: zeta+8 == omega*Frob^12(zeta+4)   (8 = 2*4 nim)
z8=el(T,9,('c',T.basis[T.index[2]]+T.basis[T.index[4]]))
print('D k=2: zeta+8 == omega*Frob^12(zeta+4):', T.multiply(w,T.power(z4,2**12))==z8)
