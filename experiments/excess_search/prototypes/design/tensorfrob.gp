n1=7; n2=9; P1=Mod(1,2)*(x^7+x+1); P2=Mod(1,2)*(y^9+y^4+1);
print(polisirreducible(P1)," ",polisirreducible(P2));
red(f)=lift(Mod(lift(Mod(f,P1)),P2));
mulT(u,v)=red(u*v);
rnd()=sum(i=0,n1-1,sum(j=0,n2-1,random(2)*x^i*y^j))*Mod(1,2);
sx(f)=red(subst(f,x,x^2));
sy(f)=red(subst(f,y,y^2));
ok=1;
{for(trial=1,20, a=rnd(); b=rnd(); if(sx(mulT(a,b))!=mulT(sx(a),sx(b)), ok=0); if(sx(sy(a))!=red(a^2), ok=0); c=a; for(i=1,n1,c=sx(c)); if(c!=a, ok=0); c=a; for(i=1,3,c=sx(c)); if(c==a, ok=0));}
print("partial Frobenius is a ring map, sigma = sx sy, sx^n1 = id, sx^3 != id: ",ok);
{a=rnd(); e=2^(n1*n2)-1; r=Mod(1,2); bb=a; while(e, if(e%2, r=mulT(r,bb)); bb=mulT(bb,bb); e\=2); print("a^(2^63-1)==1 (field): ", r==1);}
