#include <NTL/GF2XFactoring.h>
#include <NTL/GF2EX.h>
#include <chrono>
#include <cstdio>
using namespace NTL; using namespace std;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
int main(int argc,char**argv){
  if(argv[1][0]=='i'){ // irreducible search
    for(int i=2;i<argc;i++){ long n=atol(argv[i]); double t=now(); GF2X f; BuildSparseIrred(f,n); double dt=now()-t;
      printf("BuildSparseIrred n=%ld weight=%ld time=%.3fs  terms:",n,weight(f),dt); for(long j=deg(f);j>=0;j--) if(IsOne(coeff(f,j))) printf(" %ld",j); printf("\n"); fflush(stdout);
      t=now(); long ok=IterIrredTest(f); printf("   IterIrredTest=%ld %.3fs\n",ok,now()-t); fflush(stdout);}
  } else { // minpoly over GF2E
    long t=atol(argv[2]);
    GF2X P; BuildSparseIrred(P,t); GF2E::init(P);
    for(int i=3;i<argc;i++){ long n=atol(argv[i]); GF2EX f,a,m; random(f,n); SetCoeff(f,n); random(a,n); GF2EXModulus F(f);
      double t0=now(); ProbMinPolyMod(m,a,F); double t1=now(); 
      printf("t=%ld n=%ld ProbMinPolyMod deg=%ld %.3fs\n",t,n,deg(m),t1-t0); fflush(stdout);}
  }
}
