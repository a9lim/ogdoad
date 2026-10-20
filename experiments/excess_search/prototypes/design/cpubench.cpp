#include <NTL/GF2E.h>
#include <ctime>
#include <iostream>
using namespace NTL; using namespace std;
int main(int argc,char**argv){ long B=atol(argv[1]);
 GF2X P; SetCoeff(P,B); SetCoeff(P,7); SetCoeff(P,3); SetCoeff(P,2); SetCoeff(P,0); GF2E::init(P);
 GF2E a,b; random(a); random(b);
 clock_t t=clock(); for(int i=0;i<2000;i++) sqr(a,a); double ts=double(clock()-t)/CLOCKS_PER_SEC/2000;
 t=clock(); for(int i=0;i<20;i++) a=a*b; double tm=double(clock()-t)/CLOCKS_PER_SEC/20;
 cout<<"n="<<B<<" CPU sqr "<<ts*1e3<<" ms  mul "<<tm*1e3<<" ms"<<endl; }
