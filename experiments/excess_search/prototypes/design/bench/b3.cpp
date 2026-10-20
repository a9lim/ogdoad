// MinPolySeq on a generic (non-impulse) sequence: s_i = <lambda, x^i mod P> with random lambda.
#include <NTL/GF2X.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/GF2EX.h>
#include <NTL/vec_GF2.h>
#include <sys/resource.h>
#include <iostream>
using namespace NTL; using namespace std;
double cpu(){ struct rusage u; getrusage(RUSAGE_SELF,&u); return u.ru_utime.tv_sec+u.ru_utime.tv_usec*1e-6; }
int main(){
  for(long n: {10000L,100000L,1000000L,4000000L}){
    GF2X P; BuildSparseIrred(P,n); GF2XModulus F(P);
    // generic sequence via power projection: s_i = <lambda, h^i> for random h (h generates)
    GF2X h; random(h,n); vec_GF2 lam; random(lam,n);
    double t0=cpu(); vec_GF2 s; ProjectPowers(s, lam, 2*n, h, F); double tp=cpu()-t0;
    GF2X mp; t0=cpu(); MinPolySeq(mp,s,n); double tb=cpu()-t0;
    cout<<"n="<<n<<" ProjectPowers(2n)="<<tp<<"s MinPolySeq="<<tb<<"s deg="<<deg(mp)<<endl;
    // check
    GF2X ev; CompMod(ev, mp, h, F); cout<<"  minpoly(h)==0: "<<IsZero(ev)<<endl;
    if(n>=1000000) break;
  }
}
