#include <NTL/GF2E.h>
#include <NTL/GF2XFactoring.h>
#include <chrono>
#include <iostream>
using namespace NTL; using namespace std;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
int main(int argc,char**argv){ long B=atol(argv[1]);
 GF2X P; BuildSparseIrred(P,B); cout<<"weight "<<weight(P)<<endl; GF2E::init(P);
 GF2E a; random(a); GF2E b; random(b);
 double t=now(); for(int i=0;i<1000;i++) sqr(a,a); cout<<"GF2E sqr ms "<<(now()-t)<<endl;
 t=now(); for(int i=0;i<100;i++) a=a*b; cout<<"GF2E mul ms "<<(now()-t)*10<<endl;
 GF2X x=rep(a); GF2XModulus F(P); t=now(); for(int i=0;i<1000;i++) SqrMod(x,x,F); cout<<"SqrMod ms "<<(now()-t)<<endl;
}
