#include <NTL/GF2X.h>
#include <chrono>
#include <cstdio>
using namespace NTL;
static double now(){return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();}
int main(int argc,char**argv){ long E=atol(argv[1]); GF2X a,b,c; random(a,E); random(b,E);
 for(int r=0;r<8;r++){ double t=now(); int n=0; while(now()-t<0.25){ mul(c,a,b); n++;} printf("%.3f ms\n",(now()-t)/n*1e3);} }
