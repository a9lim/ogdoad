from gf import F
import math
K=F(36); z=K.root(27); s5=K.root(5); c15=K.root(15)
th73=K.root(73); th19=K.root(19)
P1=K.kummer(1^z,73,th73)
Ps=[K.kummer(z^K.pw(s5,i),73,th73) for i in range(1,5)]
print("armC k=2 p=73: Phi(z+1)=",P1," Phi(z+s)=",Ps," predicted 26*Phi(z+1)=",26*P1%73)
F16o=[K.pw(c15,i) for i in range(15) if 15//math.gcd(i,15) in (5,15)]
print("  zero pattern over F16\\F4 equals that of z+1:", {K.kummer(z^c,73,th73)==0 for c in F16o}, "vs", P1==0)
F4=[1,K.pw(c15,5),K.pw(c15,10)]
print("armD k=2 p=19: F4 translates Phi=",[K.kummer(z^c,19,th19) for c in F4],
      " F16\\F4 zero-pattern:",{K.kummer(z^c,19,th19)==0 for c in F16o})
