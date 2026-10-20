#include <NTL/GF2X.h>
#include <chrono>
#include <iostream>
using namespace NTL; using namespace std;
double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
int main(){
  for(long E: {100000L,1000000L,3000000L,10000000L,30000000L,100000000L}){
    GF2X a,b,c; random(a,E); random(b,E);
    int reps = E<=1000000?10:(E<=10000000?3:1);
    double t=now(); for(int i=0;i<reps;i++) mul(c,a,b); double tm=(now()-t)/reps;
    t=now(); for(int i=0;i<reps;i++) sqr(c,a); double ts=(now()-t)/reps;
    cout<<"bits="<<E<<" mul="<<tm*1e3<<"ms sqr="<<ts*1e3<<"ms"<<endl;
  }
}
