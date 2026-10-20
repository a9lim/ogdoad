// K-relative model executor: builds min poly of kappa_h over K = F(C') from a plan,
// then (optionally) its norm to F_2 and the Euler tests of the translates.
#include <NTL/GF2EX.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/GF2EXFactoring.h>
#include <NTL/ZZ.h>
#include <iostream>
#include <sstream>
#include <fstream>
#include <vector>
#include <map>
#include <chrono>
#include "sum2.h"
using namespace NTL; using namespace std;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
static long degK;
GF2X hex2poly(const string& h){ GF2X f; long n=h.size(); for(long i=0;i<n;i++){ char c=h[n-1-i]; int v=(c>='a')?c-'a'+10:c-'0'; for(int b=0;b<4;b++) if(v>>b&1) SetCoeff(f,4*i+b);} return f;}
string poly2hex(const GF2X& f){ long d=deg(f); if(d<0) return "0"; string s; for(long i=0;i<=d/4;i++){int v=0; for(int b=0;b<4;b++) if(4*i+b<=d && IsOne(coeff(f,4*i+b))) v|=1<<b; s.push_back("0123456789abcdef"[v]);} while(s.size()>1&&s.back()=='0') s.pop_back(); return string(s.rbegin(),s.rend());}
GF2E kval(const string& h){ GF2E e; conv(e, hex2poly(h)); return e; }

// a_j = coefficient of W^{d-1} in W^j mod G, j<n : series T^{d-1}/rev(G)(T)
vec_GF2E impulse(const GF2EX& G, long n){
  long d=deg(G); GF2EX rG; reverse(rG,G,d); GF2EX inv; InvTrunc(inv, rG, n);
  vec_GF2E a; a.SetLength(n);
  for(long j=0;j<n;j++){ long t=j-(d-1); if(t>=0) a[j]=coeff(inv,t); else clear(a[j]); }
  return a;
}
// subset convolution over GF2E (char 2: Moebius = zeta)
vec_GF2E subsetconv(const vec_GF2E& a, const vec_GF2E& b, long n){
  long k=0; while((1L<<k)<n) k++; long N=1L<<k;
  vector<vector<GF2E>> fa(k+1, vector<GF2E>(N)), fb(k+1, vector<GF2E>(N));
  for(long S=0;S<N;S++){ int r=__builtin_popcountl(S); if(S<a.length()) fa[r][S]=a[S]; if(S<b.length()) fb[r][S]=b[S]; }
  auto zeta=[&](vector<GF2E>& f){ for(long bit=1;bit<N;bit<<=1) for(long S=0;S<N;S++) if(S&bit) f[S]+=f[S^bit]; };
  for(long r=0;r<=k;r++){ zeta(fa[r]); zeta(fb[r]); }
  vector<vector<GF2E>> h(k+1, vector<GF2E>(N)); GF2E t;
  for(long r=0;r<=k;r++) for(long S=0;S<N;S++){ GF2E acc; clear(acc); for(long r1=0;r1<=r;r1++){ mul(t,fa[r1][S],fb[r-r1][S]); acc+=t;} h[r][S]=acc; }
  for(long r=0;r<=k;r++) zeta(h[r]);
  vec_GF2E s; s.SetLength(n); for(long S=0;S<n;S++) s[S]=h[__builtin_popcountl(S)][S];
  return s;
}
GF2EX composed_sum(const GF2EX& GA, const GF2EX& GB){
  long dA=deg(GA), dB=deg(GB), D=dA*dB, n=2*D;
  vec_GF2E a=impulse(GA,n), b=impulse(GB,n);
  vec_GF2E s=subsetconv(a,b,n);
  GF2EX CS; MinPolySeq(CS, s, D);
  if(deg(CS)!=D){ cerr<<"composed sum degree "<<deg(CS)<<" != "<<D<<endl; exit(2);} 
  return CS;
}
GF2EX spread(const GF2EX& G, long r){ GF2EX H; long d=deg(G); for(long i=0;i<=d;i++) SetCoeff(H, i*r, coeff(G,i)); return H; }
// G(Y+v), v in K: f(Y+v) via scaling + binary Taylor shift by 1 when v!=0
GF2EX shift(const GF2EX& G, const GF2E& v){
  long d=deg(G); vector<GF2E> c(d+1); GF2E vp; set(vp);
  for(long i=0;i<=d;i++){ mul(c[i], coeff(G,i), vp); vp*=v; }      // f(vT)
  for(long step=1; step<=d; step<<=1)                                // Taylor shift T->T+1
    for(long i=0;i<=d;i++) if(i & step) c[i^step]+=c[i];
  GF2E vinv; inv(vinv,v); vp=vinv; GF2EX H;                           // back T = Y/v
  for(long i=0;i<=d;i++){ GF2E t; if(i==0) t=c[0]; else { mul(t,c[i],vp); vp*=vinv; } SetCoeff(H,i,t);} 
  return H;
}

static long dK(){ return GF2E::degree(); }
// trace-form weights: w_u (as GF2X bitmask over coefficient index v) with  Tr(lam z^u x) = <w_u, bits(x)>
static std::vector<GF2X> trace_weights(const GF2E& lam){
  long d=dK(); std::vector<GF2X> w(d); GF2E zu; set(zu); GF2E z; conv(z, GF2X(1,1)); if(d==1) clear(z);
  for(long u=0;u<d;u++){ GF2E zv; set(zv); for(long v=0;v<d;v++){ GF2E t=lam*zu*zv; if(IsOne(trace(t))) SetCoeff(w[u],v); zv*=z; } zu*=z; }
  return w;
}
static inline int dotbits(const GF2X& w, const GF2X& x){ int s=0; long m=std::min(deg(w),deg(x)); for(long v=0;v<=m;v++) s^= (IsOne(coeff(w,v)) & IsOne(coeff(x,v))); return s; }
static GF2X fromSeqPoly(const bits& s, long len){ GF2X f; for(long i=0;i<len;i++) if(s[i>>6]>>(i&63)&1) SetCoeff(f,i); return f; }
// numerator for trace-dual formula: N = (P * S_rev) >> E, S_rev = sum_{i<E} s_i X^{E-1-i}
static GF2X numer(const GF2X& P, const bits& s, long E){ GF2X Sr; for(long i=0;i<E;i++) if(s[i>>6]>>(i&63)&1) SetCoeff(Sr,E-1-i); GF2X t=P*Sr; GF2X N; RightShift(N,t,E); trunc(N,N,E); return N; }
GF2EX composed_sum2(const GF2EX& GA, const GF2EX& GB, double* tstat){
  long d=dK(), dA=deg(GA), dB=deg(GB), D=dA*dB, E=D*d, n=2*E;
  int k=0; while((1L<<k)<n) k++;
  GF2E z; if(d>1) conv(z, GF2X(1,1)); else set(z);
  GF2E lam; set(lam);
  for(int attempt=0; attempt<8; attempt++){
    GF2E kappa; if(d>1){ kappa=power(z,attempt+1); } else clear(kappa);
    double t0=now();
    GF2EX GAk=shift(GA,kappa);
    vec_GF2E a=impulse(GAk,n), b=impulse(GB,n);
    std::vector<GF2X> wl=trace_weights(lam), wz=trace_weights(lam*z);
    SubsetConvF2 SCs(k), SCt(k);
    for(long u=0;u<d;u++){
      bits A((1L<<k)/64+1,0), Bs((1L<<k)/64+1,0), Bt((1L<<k)/64+1,0);
      A.resize(SCs.W); Bs.resize(SCs.W); Bt.resize(SCs.W);
      for(long j=0;j<n;j++){ const GF2X& aj=rep(a[j]); if(IsOne(coeff(aj,u))) A[j>>6]|=1ULL<<(j&63);
        const GF2X& bj=rep(b[j]); if(dotbits(wl[u],bj)) Bs[j>>6]|=1ULL<<(j&63); if(dotbits(wz[u],bj)) Bt[j>>6]|=1ULL<<(j&63); }
      SCs.accumulate(A,Bs); SCt.accumulate(A,Bt);
    }
    bits sig=SCs.finish(), tau=SCt.finish(); double t1=now();
    vec_GF2 sv; sv.SetLength(n); for(long i=0;i<n;i++) sv[i]= (sig[i>>6]>>(i&63))&1;
    GF2X P; MinPolySeq(P, sv, E); double t2=now();
    if(deg(P)!=E){ cerr<<"  [sum2] kappa attempt "<<attempt<<" gives degree "<<deg(P)<<" < "<<E<<", retry"<<endl; continue; }
    GF2XModulus F(P);
    GF2X Ns=numer(P,sig,E), Nt=numer(P,tau,E); GF2X Ninv; InvMod(Ninv, Ns, P); GF2X zeta; MulMod(zeta, Nt, Ninv, F);
    // exact check: P_K(zeta) == 0 mod P
    GF2X PK=GF2E::modulus(); GF2X chk; CompMod(chk, PK, zeta, F); if(!IsZero(chk)){ cerr<<"zeta check failed"<<endl; exit(7);} 
    double t3=now();
    GF2EX PW; for(long i=0;i<=E;i++) if(IsOne(coeff(P,i))) SetCoeff(PW,i);
    GF2EX ZW; for(long i=0;i<=deg(zeta);i++) if(IsOne(coeff(zeta,i))) SetCoeff(ZW,i); ZW -= GF2EX(0,z);
    GF2EX Gw; GCD(Gw, PW, ZW); double t4=now();
    if(deg(Gw)!=D){ cerr<<"GCD degree "<<deg(Gw)<<" != "<<D<<endl; exit(8);} 
    GF2EX CS=shift(Gw,kappa); // Y = omega - kappa
    if(tstat){ tstat[0]+=t1-t0; tstat[1]+=t2-t1; tstat[2]+=t3-t2; tstat[3]+=t4-t3; }
    return CS;
  }
  cerr<<"no kappa worked"<<endl; exit(9);
}
GF2EX frob(const GF2EX& G){ GF2EX H=G; for(long i=0;i<=deg(G);i++){ GF2E t=coeff(G,i); sqr(t,t); SetCoeff(H,i,t);} return H; }
int main(int argc,char**argv){
  ifstream in(argv[1]); bool do_norm = argc>2 && string(argv[2]).find('n')!=string::npos; bool do_euler = argc>2 && string(argv[2]).find('e')!=string::npos;
  bool use2 = argc>2 && string(argv[2]).find('2')!=string::npos; bool check2 = argc>2 && string(argv[2]).find('c')!=string::npos; double tst[4]={0,0,0,0};
  string tok; map<long,GF2EX> reg; long p=0,E=0,h=0,m=0, top=-1; vector<pair<long,string>> trans;
  string line; double t0=now();
  while(getline(in,line)){
    if(line.empty()) continue; istringstream ss(line); string a; ss>>a;
    if(a=="K"){ string hx; ss>>degK>>hx; GF2X PK=hex2poly(hx); GF2E::init(PK); if(degK>1 && !IterIrredTest(PK)){cerr<<"PK reducible"<<endl; return 3;} continue; }
    if(a=="ROW"){ ss>>p>>E>>h>>m; continue; }
    if(a=="TOP"){ ss>>top; continue; }
    if(a=="TRANS"){ long mm; string hx; ss>>mm>>hx; trans.push_back({mm,hx}); continue; }
    long id=stol(a); string op; ss>>op; GF2EX G;
    if(op=="BINOM"){ long r; string hx; ss>>r>>hx; SetCoeff(G,r); SetCoeff(G,0,kval(hx)); }
    else if(op=="LIN"){ string hx; ss>>hx; SetX(G); G+=GF2EX(0,kval(hx)); }
    else if(op=="SPREAD"){ long s,r; ss>>s>>r; G=spread(reg[s],r); }
    else if(op=="SHIFT"){ long s; string hx; ss>>s>>hx; G=shift(reg[s],kval(hx)); }
    else if(op=="SUM"){ long x,y; ss>>x>>y;
      if(use2){ G=composed_sum2(reg[x],reg[y],tst); if(check2){ GF2EX G1=composed_sum(reg[x],reg[y]); if(G1!=G){cerr<<"SUM2 != SUM"<<endl; return 11;} } }
      else G=composed_sum(reg[x],reg[y]); }
    reg[id]=G;
  }
  GF2EX G=reg[top]; double tb=now()-t0;
  cout<<"p="<<p<<" E="<<E<<" degK="<<degK<<" relDeg="<<deg(G)<<" build="<<tb<<"s";
  if(use2) cout<<" [sum2: seq="<<tst[0]<<" bm="<<tst[1]<<" zeta="<<tst[2]<<" gcd="<<tst[3]<<"]"; cout<<endl;
  if(deg(G)*degK!=E){ cerr<<"degree mismatch"<<endl; return 4; }
  if(do_norm){ // Norm_{K/F2}(G) -> F_2 polynomial
    GF2EX acc=G, Gi=G; for(long i=1;i<degK;i++){ Gi=frob(Gi); acc*=Gi; }
    GF2X P; for(long i=0;i<=deg(acc);i++){ GF2X c=rep(coeff(acc,i)); if(deg(c)>0){cerr<<"norm not over F2"<<endl; return 5;} SetCoeff(P,i,coeff(c,0)); }
    cout<<"NORM "<<poly2hex(P)<<endl;
  }
  if(do_euler){
    ZZ N = (power2_ZZ(E)-1); if(N%p!=0){cerr<<"p does not divide 2^E-1"<<endl; return 6;} N/=p;
    GF2EXModulus F(G); double t1=now();
    for(auto& tr: trans){ GF2EX beta; SetX(beta); beta+=GF2EX(0,kval(tr.second)) ; GF2EX r; PowerMod(r, beta%F, N, F);
      cout<<"EULER m="<<tr.first<<" pth_power="<<(IsOne(r)?1:0)<<endl; }
    cout<<"euler_time="<<now()-t1<<"s"<<endl;
  }
}
