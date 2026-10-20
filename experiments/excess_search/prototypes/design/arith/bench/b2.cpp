// GF2EX benchmarks: polys over F_{2^t} of degree n (Kronecker to gf2x).
#include <NTL/GF2EX.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/GF2EXFactoring.h>
#include <chrono>
#include <cstdio>
using namespace NTL; using namespace std;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
template<class F> double tmin(F f, int reps=3){ double best=1e99; for(int r=0;r<reps;r++){ double t=now(); f(); best=min(best,now()-t);} return best; }
int main(int argc,char**argv){
  long t=atol(argv[1]), n=atol(argv[2]); int comp = argc>3 ? atoi(argv[3]) : 0;
  GF2X P; BuildSparseIrred(P,t); GF2E::init(P);
  GF2EX f,a,b,c; random(f,n); SetCoeff(f,n); random(a,n); random(b,n);
  GF2EXModulus F(f);
  double tm = tmin([&]{ mul(c,a,b); });
  double tmm = tmin([&]{ MulMod(c,a,b,F); });
  double tsm = tmin([&]{ SqrMod(c,a,F); });
  ZZ e; e = 359;
  double tpw = tmin([&]{ PowerMod(c,a,e,F); },1);
  double tg = tmin([&]{ GF2EX g; GCD(g,a,f); },1);
  double tcomp = -1;
  if(comp){ tcomp = tmin([&]{ CompMod(c,a,b,F); },1); }
  printf("t=%ld n=%ld bits=%ld  mul=%.4fs mulmod=%.4fs sqrmod=%.4fs pow359=%.3fs gcd=%.3fs compmod=%.3fs\n",t,n,t*n,tm,tmm,tsm,tpw,tg,tcomp);
}
