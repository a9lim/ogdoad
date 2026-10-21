from gf import F
# (i) arm C, k=1: zeta order 9, s in mu_5\{1}, p=7 (h=3), field F_{2^12}.
K=F(12); z=K.root(9); s5=K.root(5); th=K.pw(K.root(7),1)
P1=K.kummer(1^z,7,th)
Ps=[K.kummer(z^K.pw(s5,i),7,th) for i in range(1,5)]
print("armC k=1: Phi(zeta+1)=",P1," Phi(zeta+s)=",Ps," predicted -Phi(zeta+1)=",(-P1)%7)
# all 12 c in F16\F4 : c of order 5 or 15
c15=K.root(15)
others=[K.pw(c15,i) for i in range(15) if (15//__import__('math').gcd(i,15)) in (5,15)]
print("  Phi(zeta+c), c in F16\\F4:",sorted(set(K.kummer(z^c,7,th)==0 for c in others)), "(False => all non-7th-powers)")
# (ii) arm O r=5 a=1: xi order 25, w order 3, field F_{2^20}; p=31 (h=5), 11 (h=10), 41 (h=20)
L=F(20); xi=L.root(25); w=L.root(3); w2=L.mul(w,w)
for p,expect in ((31,"prop"),(11,"prop"),(41,"CM")):
    th=L.root(p)
    a=L.kummer(1^xi,p,th); b=L.kummer(1^L.mul(w,xi),p,th); c=L.kummer(1^L.mul(w2,xi),p,th)
    print(f"armO r=5 p={p}: Phi(1+xi)={a} Phi(1+w xi)={b} Phi(1+w^2 xi)={c}", end=" ")
    if expect=="prop": print(" predicted Phi(1+w xi)=(2^7-1)/2*Phi(1+xi)=",(127*pow(2,-1,p)*a)%p)
    else: print(" predicted Phi(1+xi)=0, b+c=0:",a==0,(b+c)%p==0)
# (iii) Euler forcing N=183, F_{2^60}, p=7, plus contrast t of order 61.
M=F(60); t=M.root(183); th=M.root(7)
print("N=183: Phi_7(1+t)=",M.kummer(1^t,7,th), "(predicted 0); other primitive t^a:",
      sorted(set(M.kummer(1^M.pw(t,a),7,th) for a in range(1,183) if __import__('math').gcd(a,183)==1)))
u=M.root(61)
print("contrast N=61: Phi_7(1+u)=",M.kummer(1^u,7,th))
