// Norm-first (Itoh-Tsujii) Euler test vs plain PowerMod, sparse irreducible modulus.
#include <NTL/GF2X.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <chrono>
#include <iostream>
using namespace NTL; using namespace std;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
static long nsq=0, nmul=0;
static void frobk(GF2X& z, long k, const GF2XModulus& F){ for(long i=0;i<k;i++){ SqrMod(z,z,F); nsq++; } }
// y_n = x^{(2^{nh}-1)/(2^h-1)} by left-to-right binary on n
static GF2X relnorm(const GF2X& x, long n, long h, const GF2XModulus& F){
  long top=0; while((1L<<(top+1))<=n) top++;
  GF2X y=x; long k=1;
  for(long bit=top-1; bit>=0; bit--){
    GF2X t=y; frobk(t,k*h,F); MulMod(y,t,y,F); nmul++; k*=2;          // y_{2k}
    if((n>>bit)&1){ GF2X t2=y; frobk(t2,h,F); MulMod(y,t2,x,F); nmul++; k+=1; } // y_{k+1}
  }
  if(k!=n){ cerr<<"chain error\n"; exit(1);} return y;
}
int main(int argc,char**argv){
  long E=atol(argv[1]), h=atol(argv[2]), p=atol(argv[3]); int check=atoi(argv[4]);
  GF2X P; double t=now(); if(check>=0) BuildSparseIrred(P,E); else { SetCoeff(P,E); SetCoeff(P,7); SetCoeff(P,3); SetCoeff(P,2); SetCoeff(P,0);} GF2XModulus F(P);
  cout<<"E="<<E<<" modulus weight="<<weight(P)<<" build "<<now()-t<<"s\n";
  GF2X x; random(x,E);
  ZZ N=power2_ZZ(E)-1; if(N%p!=0){cerr<<"p does not divide 2^E-1\n";return 1;}
  t=now(); GF2X T=relnorm(x,E/h,h,F); double tn=now()-t;
  ZZ e2=(power2_ZZ(h)-1)/p; GF2X ph; t=now(); PowerMod(ph,T,e2,F); double te=now()-t;
  cout<<"norm-first: relnorm "<<tn<<"s ("<<nsq<<" sqr, "<<nmul<<" mul) + small pow "<<te<<"s; phase==1? "<<IsOne(ph)<<"\n";
  if(check>0){ GF2X d; t=now(); PowerMod(d,x,N/p,F); cout<<"plain PowerMod "<<now()-t<<"s; equal="<<(d==ph)<<"\n"; }
}
