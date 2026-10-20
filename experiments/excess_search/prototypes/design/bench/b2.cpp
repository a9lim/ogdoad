#include <NTL/GF2X.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/GF2EX.h>
#include <NTL/vec_GF2.h>
#include <sys/resource.h>
#include <iostream>
#include <string>
using namespace NTL; using namespace std;
double cpu(){ struct rusage u; getrusage(RUSAGE_SELF,&u); return u.ru_utime.tv_sec+u.ru_utime.tv_usec*1e-6; }
template<class F> double timeit(F f, double minT=0.3){ int reps=0; double t0=cpu(), t; do { f(); reps++; t=cpu()-t0; } while(t<minT); return t/reps; }
void taylor1(GF2X& f, long n){
  f.xrep.SetLength((n+63)/64); _ntl_ulong* w=f.xrep.elts(); long W=f.xrep.length();
  static const _ntl_ulong M[6]={0x5555555555555555UL,0x3333333333333333UL,0x0F0F0F0F0F0F0F0FUL,0x00FF00FF00FF00FFUL,0x0000FFFF0000FFFFUL,0x00000000FFFFFFFFUL};
  for(int k=0;k<6;k++){ int s=1<<k; for(long i=0;i<W;i++) w[i]^=(w[i]>>s)&M[k]; }
  for(long s=1; s<W; s<<=1) for(long i=0;i<W;i++) if(i & s) w[i^s]^=w[i];
  f.normalize();
}
int main(int argc, char** argv){
  string which = argc>1? argv[1] : "abcdefg";
  cout.precision(4);
  if(which.find('a')!=string::npos){
  cout<<"== [a] GF2X: mul sqr | MulMod/SqrMod dense | SqrMod/MulMod pentanomial | taylor1   (ms, CPU)\n";
  for(long n: {10000L,100000L,1000000L,10000000L}){
    GF2X a,b,c; random(a,n); random(b,n);
    double tm=timeit([&]{ mul(c,a,b); }), ts=timeit([&]{ sqr(c,a); });
    GF2X P; random(P,n); SetCoeff(P,n); GF2XModulus F(P);
    double tmm=timeit([&]{ MulMod(c,a,b,F); }), tsm=timeit([&]{ SqrMod(c,a,F); });
    GF2X S; SetCoeff(S,n); SetCoeff(S,7); SetCoeff(S,3); SetCoeff(S,2); SetCoeff(S,0); GF2XModulus FS(S);
    double tss=timeit([&]{ SqrMod(c,a,FS); }), tms=timeit([&]{ MulMod(c,a,b,FS); });
    GF2X f=a; double tt=timeit([&]{ taylor1(f,n); });
    cout<<"n="<<n<<" mul="<<tm*1e3<<" sqr="<<ts*1e3<<" | MulMod="<<tmm*1e3<<" SqrMod="<<tsm*1e3<<" | SqrModPenta="<<tss*1e3<<" MulModPenta="<<tms*1e3<<" | taylor1="<<tt*1e3<<endl;
  }}
  if(which.find('b')!=string::npos){
  cout<<"== [b] MinPolySeq over GF2, length 2n (s, CPU) -- random LFSR of degree n\n";
  for(long n: {10000L,100000L,1000000L}){
    GF2X P; random(P,n); SetCoeff(P,n); SetCoeff(P,0);
    GF2X rP; reverse(rP,P,n); GF2X inv; InvTrunc(inv,rP,2*n);
    vec_GF2 s; s.SetLength(2*n); for(long i=0;i<2*n;i++){ long t=i-(n-1); s[i]= t>=0? coeff(inv,t):GF2(0);} 
    GF2X h; double t0=cpu(); MinPolySeq(h,s,n); double t=cpu()-t0;
    cout<<"n="<<n<<" MinPolySeq="<<t<<" ok="<<(h==P)<<endl;
  }}
  if(which.find('c')!=string::npos){
  cout<<"== [c] GF2EX over K=GF(2^d), total E bits: mul, MulMod, (ms CPU) vs GF2X mul(E)\n";
  for(long d: {2L,4L,12L,20L,60L,220L}){
    GF2X PK; BuildIrred(PK,d); GF2E::init(PK);
    for(long E: {100000L,1000000L}){
      long D=E/d; GF2EX a,b,c; random(a,D); random(b,D);
      double tm=timeit([&]{ mul(c,a,b); });
      GF2EX G; random(G,D); SetCoeff(G,D); GF2EXModulus FG(G);
      double tmm=timeit([&]{ MulMod(c,a,b,FG); });
      cout<<"d="<<d<<" E="<<E<<" D="<<D<<" mul="<<tm*1e3<<" MulMod="<<tmm*1e3<<endl;
    }
  }}
  if(which.find('d')!=string::npos){
  cout<<"== [d] MinPolySeq over GF2E length 2D, GCD over GF2E degree D (s CPU)\n";
  for(long d: {4L,12L,60L}){
    GF2X PK; BuildIrred(PK,d); GF2E::init(PK);
    for(long D: {10000L,100000L}){
      GF2EX G; random(G,D); SetCoeff(G,D);
      GF2EX rG; reverse(rG,G,D); GF2EX inv; InvTrunc(inv,rG,2*D);
      vec_GF2E s; s.SetLength(2*D); for(long i=0;i<2*D;i++){ long t=i-(D-1); if(t>=0) s[i]=coeff(inv,t); }
      GF2EX h; double t0=cpu(); MinPolySeq(h,s,D); double t=cpu()-t0;
      GF2EX A,B,g; random(A,D); SetCoeff(A,D); random(B,D-1); t0=cpu(); GCD(g,A,B); double tg=cpu()-t0;
      cout<<"d="<<d<<" D="<<D<<" MinPolySeq="<<t<<" ok="<<(h==G)<<" GCD="<<tg<<endl;
    }
  }}
  if(which.find('e')!=string::npos){
  cout<<"== [e] GF2X CompMod / MinPolyMod / PowerXMod(2^n) frobenius (s CPU)\n";
  for(long n: {10000L,30000L,100000L}){
    GF2X P; BuildSparseIrred(P,n); GF2XModulus F(P); GF2X g,h,x; random(g,n); random(h,n);
    double t0=cpu(); CompMod(x,g,h,F); double tc=cpu()-t0;
    t0=cpu(); GF2X mp; MinPolyMod(mp,h,F); double tmp=cpu()-t0;
    cout<<"n="<<n<<" CompMod="<<tc<<" MinPolyMod="<<tmp<<" deg="<<deg(mp)<<endl;
  }}
}
