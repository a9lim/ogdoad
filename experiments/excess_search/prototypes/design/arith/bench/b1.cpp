// Benchmark: GF2X mul/sqr, sparse/dense MulMod/SqrMod, custom sparse squaring, CompMod.
#include <NTL/GF2X.h>
#include <NTL/GF2XFactoring.h>
#include <chrono>
#include <iostream>
#include <cstdlib>
#include "sqrk.h"
using namespace NTL; using namespace std;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
template<class F> double timeit(F f, double budget=0.3){ int reps=0; double t0=now(), t; do { f(); reps++; t=now()-t0; } while(t<budget && reps<100000); return t/reps; }
int main(int argc,char**argv){
  bool comp = argc>1 && atoi(argv[1]);
  long Es[] = {1000, 3000, 10000, 30000, 100000, 300000, 1000000, 3000000, 10000000, 30000000, 100000000};
  printf("%10s %10s %10s %10s %10s %10s %10s %10s %10s\n","E","mul_ms","sqr_ms","sqrmodS_ms","mysqrS_ms","mulmodS_ms","mulmodD_ms","sqrmodD_ms","compD_ms");
  for(long E: Es){
    GF2X a,b,c,d; random(a,E); random(b,E);
    double tmul = timeit([&]{ mul(c,a,b); });
    double tsqr = timeit([&]{ sqr(c,a); });
    GF2X S; SetCoeff(S,E); SetCoeff(S,7); SetCoeff(S,3); SetCoeff(S,2); SetCoeff(S,0);
    GF2XModulus FS(S);
    double tss = timeit([&]{ SqrMod(c,a,FS); });
    double tms = E<=30000000 ? timeit([&]{ MulMod(c,a,b,FS); }) : -1;
    // custom
    SparseSq K(E, {7,3,2});
    long nw=(E+63)/64; vector<uint64_t> A(nw+2,0), R(nw+2,0);
    { // load a
      for(long i=0;i<=deg(a);i++) if(IsOne(coeff(a,i))) A[i>>6] |= 1ULL<<(i&63); }
    K.sqr(R.data(), A.data());
    // verify
    SqrMod(c,a,FS); bool ok=true; for(long i=0;i<E;i++){ bool bit=(R[i>>6]>>(i&63))&1; if(bit!=IsOne(coeff(c,i))){ok=false;break;} }
    // verify iterated 5 squarings
    { vector<uint64_t> X(A), Y(nw+2); GF2X cc=a; for(int t=0;t<5;t++){ K.sqr(Y.data(),X.data()); swap(X,Y); SqrMod(cc,cc,FS);} for(long i=0;i<E;i++){ bool bit=(X[i>>6]>>(i&63))&1; if(bit!=IsOne(coeff(cc,i))){ok=false;break;} } }
    double tmy = timeit([&]{ K.sqr(R.data(), A.data()); });
    double tmd=-1, tsd=-1, tcd=-1;
    if(E<=10000000){
      GF2X P; random(P,E); SetCoeff(P,E); GF2XModulus F(P);
      tmd = timeit([&]{ MulMod(c,a,b,F); });
      tsd = timeit([&]{ SqrMod(c,a,F); });
      if(comp && E<=1000000){ GF2X g,h; random(g,E); random(h,E); tcd = timeit([&]{ CompMod(c,g,h,F); }, 1.0); }
    }
    printf("%10ld %10.4f %10.4f %10.5f %10.5f %10.4f %10.4f %10.4f %10.2f %s\n",E,tmul*1e3,tsqr*1e3,tss*1e3,tmy*1e3,tms*1e3,tmd*1e3,tsd*1e3,tcd*1e3, ok?"ok":"MISMATCH");
    fflush(stdout);
  }
}
