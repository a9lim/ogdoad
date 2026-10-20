// Frobenius-structured r-th root ("crossed root") vs generic exponentiation in F_{2^b}.
// a := alpha^{-k'} with k' = (wM-1)/r, M = (2^b-1)/(2^t-1), w = n^{-1} mod r, n = b/t,
// computed with O(log n) Frobenius sweeps and O(log^2 n + t) multiplications.
// Check: a^r == alpha / N_{b/t}(alpha)^w.   Usage: droot b r t
#include <NTL/GF2E.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <chrono>
#include <iostream>
using namespace NTL; using namespace std;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
long B; long nsq = 0, nmul = 0;
GF2E frob(const GF2E& x, long k){ k%=B; GF2E y=x; for(long i=0;i<k;i++){ sqr(y,y);} nsq+=k; return y; }
GF2E mul(const GF2E&a,const GF2E&b){ nmul++; return a*b; }
GF2E pw(const GF2E& a, long e){ GF2E r; set(r); GF2E x=a; while(e){ if(e&1) r=mul(r,x); e>>=1; if(e) x=mul(x,x);} return r; }
int main(int argc,char**argv){
  B=atol(argv[1]); long r=atol(argv[2]); long t=atol(argv[3]);
  long n=B/t; if(B%t||n%r==0){cerr<<"bad params\n";return 1;}
  GF2X P; if(argc>4){ SetCoeff(P,B); SetCoeff(P,7); SetCoeff(P,3); SetCoeff(P,2); SetCoeff(P,0);} else BuildSparseIrred(P,B); GF2E::init(P);
  SetSeed(ZZ(7)); GF2E alpha; random(alpha);
  double t0=now();
  // N(m) = prod_{i<m} sigma^{ti}(alpha),  A(m) = prod_{j<m} N(j)   (binary method, MSB first)
  GF2E Nm, Am; set(Nm); set(Am); long m=0;
  for(long bit=63-__builtin_clzl(n); bit>=0; bit--){
    if(m){ // double: A(2m)=A(m) N(m)^m sigma^{tm}(A(m)),  N(2m)=N(m) sigma^{tm}(N(m))
      GF2E fA=frob(Am,t*m), fN=frob(Nm,t*m);
      Am=mul(mul(Am,pw(Nm,m)),fA); Nm=mul(Nm,fN); m*=2;
    }
    if((n>>bit)&1){ // +1: A(m+1)=A(m) N(m), N(m+1)=N(m) sigma^{tm}(alpha)
      Am=mul(Am,Nm); Nm=mul(Nm,frob(alpha,t*m)); m+=1;
    }
  }
  // now Nm = N_{b/t}(alpha), Am = alpha^S
  long w=1; while((w*(n%r))%r!=1) w++;
  GF2E c=pw(Nm,w);
  ZZ L=(power2_ZZ(t)-1)/r;  // t-bit exponent
  GF2E AL; power(AL,Am,L*w); nmul+=2*t; // count approx
  long k0=(w*n-1)/r;
  GF2E a=inv(mul(AL,pw(alpha,k0)));
  double t1=now();
  GF2E ar; power(ar,a,r);
  bool ok=(ar==alpha/c);
  // c in F_t ?
  bool cin=(argc>4)?false:(frob(c,t)==c); long sq0=nsq;
  cout<<"b="<<B<<" r="<<r<<" t="<<t<<" n="<<n<<" crossed-root ok="<<ok<<" c in F_t="<<cin
      <<" time="<<t1-t0<<"s squarings="<<nsq<<" mults~"<<nmul<<endl;
  // generic: one b-bit exponentiation (lower bound for AMM)
  ZZ u=power2_ZZ(B)-1; u/=r; u+=12345; // a dense b-bit exponent
  double t2=now(); GF2E g; power(g,alpha,u); double t3=now();
  cout<<"  generic b-bit exponentiation time="<<t3-t2<<"s"<<endl;
}
