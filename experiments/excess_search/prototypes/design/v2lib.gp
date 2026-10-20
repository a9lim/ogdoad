\\ Independent-model (V2) pipelines: only small fields, pinned shared subfield.
\\ tower entries: [type, q, ell, c, ids]; type 1 = AS (y^2+y=prod ids), 2 = Kummer (y^ell = c + sum ids)
relval(V, e, F) = if(e[1]==1, my(s=F^0); for(i=1,#e[5], s*=mapget(V,e[5][i])); s, my(s=e[4]*F^0); for(i=1,#e[5], s+=mapget(V,e[5][i])); s);
build(F, tw, V, need) = {
  for(i=1,#tw, my(e=tw[i]); if(setsearch(need,e[2]) && !mapisdefined(V,e[2]),
     my(a=relval(V,e,F), P, rts);
     P = if(e[1]==1, 'X^2+'X+a, 'X^e[3]+a);
     rts = polrootsmod(P);
     if(#rts==0, error("no root for component ",e[2]));
     mapput(V, e[2], rts[#rts])));
  V
};
mapvals(m, V) = my(W=Map(), M=Mat(V)); for(i=1,#M~, mapput(W, M[i,1], ffmap(m, M[i,2]))); W;
\\ fix an embedding m0: K -> L so that m0 o sub == target on the generator of the subfield (sub: S -> K, target: S -> L)
fixemb(m0, K, sub, target, S) = {
  my(d=K.f, want=ffmap(target,S), fr=fffrobenius(K,1), m=m0);
  for(k=0,d-1, if(ffmap(ffcompomap(m,sub),S)==want, return(m)); m=ffcompomap(m,fr));
  error("fixemb failed")
};
condpoly(x, d, s, X) = my(P=1, c=x); for(j=1,d/s, P*=(X-c); c=c^(2^s)); P;
pullpoly(P, m) = my(mi=ffinvmap(m)); Pol(apply(c->ffmap(mi,c), Vec(P)), variable(P));
pushpoly(P, m) = Pol(apply(c->ffmap(m,c), Vec(P)), variable(P));
mp2(T) = Vec(minpoly(T)); 
euler(T, h, plist) = vector(#plist, i, T^((2^h-1)/plist[i])==1);
\\ common setup: returns [Mg, Vg, MA, mgA, VA, z, Mb, mgb, Vb, alpha]
setup(tw, Sg, SA, Sy, smalls, r, g, A, b) = {
  my(Mg=ffgen(ffinit(2,g),'g), Vg=build(Mg,tw,Map(),Sg));
  my(MA=ffgen(ffinit(2,A),'w), mgA=ffembed(Mg,MA), VA=build(MA,tw,mapvals(mgA,Vg),SA));
  my(z=0*MA); for(i=1,#smalls, z+=mapget(VA,smalls[i]));
  my(Mb=ffgen(ffinit(2,b),'u), mgb=ffembed(Mg,Mb), Vb=build(Mb,tw,mapvals(mgb,Vg),setminus(Sy,[r])));
  my(er); for(i=1,#tw, if(tw[i][2]==r, er=tw[i]));
  my(alpha=relval(Vb,er,Mb));
  [Mg,Vg,MA,mgA,VA,z,Mb,mgb,Vb,alpha]
};
crossed(tw, Sg, SA, Sy, smalls, r, g, A, b, fr, ex, h, plist) = {
  my(S=setup(tw,Sg,SA,Sy,smalls,r,g,A,b), Mg=S[1], MA=S[3], mgA=S[4], z=S[6], Mb=S[7], mgb=S[8], alpha=S[10]);
  my(M=(2^b-1)/(2^fr-1), w=lift(Mod(M,r)^-1), c=(alpha^M)^w);
  my(aa=sqrtn(alpha/c, r));
  my(t=gcd(b,ex), n1=b/t, u=gcd(t,A));
  my(Mt=ffgen(ffinit(2,t),'t), mtb=ffembed(Mt,Mb));
  my(Mu=ffgen(ffinit(2,u),'s), mug=ffembed(Mu,Mg), mub=ffcompomap(mgb,mug), mua=ffcompomap(mgA,mug));
  my(mut=ffcompomap(ffinvmap(mtb),mub));
  my(Mex=ffgen(ffinit(2,ex),'e), mAex=ffembed(MA,Mex));
  my(mtex=fixemb(ffembed(Mt,Mex), Mt, mut, ffcompomap(mAex,mua), Mu));
  my(cex=ffmap(mtex, ffmap(ffinvmap(mtb), c)));
  my(v=sqrtn(cex, r));
  my(fa=pushpoly(pullpoly(condpoly(aa,b,t,'X), mtb), mtex));
  my(zex=ffmap(mAex,z));
  my(W=v^n1*subst(fa,'X,zex/v));
  my(T=W^((2^ex-1)/(2^h-1)));
  [mp2(T), euler(T,h,plist), n1, t]
};
freefactor(tw, Sg, SA, Sy, smalls, r, g, A, b, e0, h, plist, badk) = {
  my(S=setup(tw,Sg,SA,Sy,smalls,r,g,A,b), Mg=S[1], MA=S[3], mgA=S[4], z=S[6], Mb=S[7], mgb=S[8], alpha=S[10]);
  my(sp=gcd(b,e0), n=b/sp);
  my(Ms=ffgen(ffinit(2,sp),'t), msb=ffembed(Ms,Mb), mgs=ffcompomap(ffinvmap(msb),mgb));
  my(Pa=pullpoly(condpoly(alpha,b,sp,'X), msb));
  my(Me=ffgen(ffinit(2,e0),'e), mAe=ffembed(MA,Me));
  my(mse=fixemb(ffembed(Ms,Me), Ms, mgs, ffcompomap(mAe,mgA), Mg));
  if(badk, mse=ffcompomap(mse, fffrobenius(Ms,badk)));
  my(Fp=subst(pushpoly(Pa,mse),'X,'X^r), fac=factor(Fp)[,1], ze=ffmap(mAe,z), out=List());
  for(i=1,#fac, my(Q=fac[i], N=subst(Q,'X,ze), T=N^((2^e0-1)/(2^h-1))); listput(out, [poldegree(Q), mp2(T), euler(T,h,plist)]));
  Vec(out)
};
\\ Relative-model crossing: only P = charpoly(alpha_r / F_t) is used; F_b is modelled as
\\ K = F_t[W]/(P(W)) with alpha = W.  The crossed r-th root is computed with Frobenius
\\ sigma^t realised as W -> W^(2^t) (coefficients in F_t are fixed).
relcross(tw, Sg, SA, Sy, smalls, r, g, A, b, fr, ex, h, plist) = {
  my(S=setup(tw,Sg,SA,Sy,smalls,r,g,A,b), Mg=S[1], MA=S[3], mgA=S[4], z=S[6], Mb=S[7], mgb=S[8], alpha0=S[10]);
  my(t=gcd(b,ex), n1=b/t, u=gcd(t,A));
  my(Mt=ffgen(ffinit(2,t),'t), mtb=ffembed(Mt,Mb));
  my(P=pullpoly(condpoly(alpha0,b,t,'W), mtb));   \\ the only datum taken from F_b
  my(one=Mt^0, al=Mod('W*one, P));
  my(Mx=(2^b-1)/(2^t-1), wq=lift(Mod(Mx,r)^-1), Nal=polcoef(P,0), c=Nal^wq);
  my(Wq=lift(al^(2^t)));                            \\ sigma^t(W)
  my(frobm=(x,m)->my(y=lift(x)); for(i=1,m, y=lift(Mod(subst(y,'W,Wq),P))); Mod(y,P));
  my(Nm=Mod(one,P), Am=Mod(one,P), m=0, bits=binary(n1));
  for(i=1,#bits,
     if(m, my(fA=frobm(Am,m), fN=frobm(Nm,m)); Am=Am*Nm^m*fA; Nm=Nm*fN; m*=2);
     if(bits[i], Am=Am*Nm; Nm=Nm*frobm(al,m); m+=1));
  my(L=(2^t-1)/r, k0=(wq*n1-1)/r);
  my(a=1/(Am^(wq*L)*al^k0));
  my(okroot=(a^r==al/c), okN=(Nm==Mod(Nal,P)));
  my(fa=charpoly(a,'X));
  my(Mu=ffgen(ffinit(2,u),'s), mug=ffembed(Mu,Mg), mub=ffcompomap(mgb,mug), mua=ffcompomap(mgA,mug));
  my(mut=ffcompomap(ffinvmap(mtb),mub));
  my(Mex=ffgen(ffinit(2,ex),'e), mAex=ffembed(MA,Mex));
  my(mtex=fixemb(ffembed(Mt,Mex), Mt, mut, ffcompomap(mAex,mua), Mu));
  my(v=sqrtn(ffmap(mtex,c), r));
  my(fae=pushpoly(fa, mtex), zex=ffmap(mAex,z));
  my(Wv=v^n1*subst(fae,'X,zex/v), T=Wv^((2^ex-1)/(2^h-1)));
  [mp2(T), euler(T,h,plist), n1, t, okroot, okN]
};
