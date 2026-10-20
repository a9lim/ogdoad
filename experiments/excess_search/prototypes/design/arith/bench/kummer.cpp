// Euler test in a Kummer field H = k[V]/(V^R - c), k = F_2[x]/(P_t), [H:F_2] = D = R t.
// Method A: reference  beta^((2^D-1)/p)  by NTL PowerMod (D squarings).
// Method B: Itoh-Tsujii norm to F_{2^h} with structured Frobenius sigma^m
//           (V^(2^m) = gamma_m V^(r_m)), then the small exponent u=(2^h-1)/p.
#include <NTL/GF2EX.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <chrono>
#include <cstdio>
#include <map>
#include <vector>
using namespace NTL; using namespace std;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
static long R; static GF2E cc; static long t;
static long stat_mul=0, stat_sqr=0, stat_frob=0;
// reduce a polynomial of degree < 2R-1 modulo V^R - c
static void redH(GF2EX& x){ long d=deg(x); if(d<R) return; GF2E tmp;
  for(long i=d;i>=R;i--){ mul(tmp,coeff(x,i),cc); add(tmp,tmp,coeff(x,i-R)); SetCoeff(x,i-R,tmp); }
  trunc(x,x,R); }
static void mulH(GF2EX& z,const GF2EX& a,const GF2EX& b){ mul(z,a,b); redH(z); stat_mul++; }
static void sqrH(GF2EX& z,const GF2EX& a){ // linear: coefficientwise squaring, V^{2i}
  GF2EX r; r.SetLength(2*R-1); for(long i=0;i<=deg(a);i++){ GF2E s; sqr(s,coeff(a,i)); r[2*i]=s; } r.normalize(); redH(r); z=r; stat_sqr++; }
// k-Frobenius power on a GF2E: j squarings (j < t)
static inline void frobK(GF2E& y,const GF2E& x,long j){ y=x; for(long i=0;i<j;i++) sqr(y,y); }
struct Frob { long m, r; vector<GF2E> mult; vector<long> dst; long jk; };
static map<long,Frob> cache;
static const Frob& getFrob(long m){ // sigma^m, m >= 0
  auto it=cache.find(m); if(it!=cache.end()) return it->second;
  Frob F; F.m=m; F.jk = m % t;
  // gamma_m, r_m via V^(2^m) = gamma V^r : use 2^m mod (R) and gamma = c^{floor(2^m/R)} computed by recurrence on m (O(m) k-ops)
  GF2E g; set(g); long r=1; // V^1
  for(long s=0;s<m;s++){ sqr(g,g); r*=2; if(r>=R){ r-=R; mul(g,g,cc);} }
  F.r=r; F.mult.resize(R); F.dst.resize(R);
  GF2E gi; set(gi);
  for(long i=0;i<R;i++){ long e=i*r; long q=e/R, j=e%R; GF2E w=gi; for(long u=0;u<q;u++) mul(w,w,cc); F.mult[i]=w; F.dst[i]=j; mul(gi,gi,g); }
  return cache[m]=F; }
static void frobH(GF2EX& z,const GF2EX& a,long m){ const Frob& F=getFrob(m); GF2EX r; r.SetLength(R);
  for(long i=0;i<=deg(a);i++){ GF2E y; frobK(y,coeff(a,i),F.jk); mul(y,y,F.mult[i]); r[F.dst[i]]=y; } r.normalize(); z=r; stat_frob++; }
static long ordtwo(long p){ long o=1; long v=2%p; while(v!=1){ v=(2*v)%p; o++; } return o; }
static void powH(GF2EX& z,const GF2EX& a,const ZZ& e){ // left-to-right sliding window, w=5
  long w=5; vector<GF2EX> tab(1<<(w-1)); tab[0]=a; GF2EX a2; sqrH(a2,a); for(long i=1;i<(1<<(w-1));i++) mulH(tab[i],tab[i-1],a2);
  GF2EX r; set(r); long i=NumBits(e)-1;
  while(i>=0){ if(!bit(e,i)){ sqrH(r,r); i--; continue; }
    long l=max(i-w+1,0L); while(!bit(e,l)) l++; long val=0; for(long j=i;j>=l;j--) val=2*val+bit(e,j);
    for(long j=0;j<i-l+1;j++) sqrH(r,r); mulH(r,r,tab[(val-1)/2]); i=l-1; }
  z=r; }

static vector<long> primefac(long n){ vector<long> f; for(long q=2;q*q<=n;q++) if(n%q==0){ f.push_back(q); while(n%q==0) n/=q; } if(n>1) f.push_back(n); return f; }
// x^(2^d - 1) by Itoh-Tsujii using squarings in H
static void pow2m1(GF2EX& z, const GF2EX& x, long d){ // z = x^(2^d-1)
  GF2EX r=x; long k=1; long nb=NumBits(ZZ(d));
  for(long i=nb-2;i>=0;i--){ GF2EX s=r; for(long j=0;j<k;j++) sqrH(s,s); mulH(r,r,s); k*=2; if((d>>i)&1){ sqrH(r,r); mulH(r,r,x); k++; } }
  z=r; }
int main(int argc,char**argv){
  t=atol(argv[1]); R=atol(argv[2]); long p=atol(argv[3]); int ref=atoi(argv[4]); int trials=argc>5?atoi(argv[5]):1;
  GF2X P; BuildSparseIrred(P,t); GF2E::init(P);
  long D=R*t, h=ordtwo(p); if(D%h){ printf("h=%ld does not divide D=%ld\n",h,D); return 1; }
  ZZ Q = power2_ZZ(t)-1; if(Q%R!=0){ printf("R does not divide 2^t-1\n"); return 1;}
  // pick c a non-R-th power
  do { random(cc); } while(IsZero(cc) || IsOne(power(cc,Q/R)));
  long n=D/h; ZZ u=(power2_ZZ(h)-1)/p;
  GF2EX mod; SetCoeff(mod,R); SetCoeff(mod,0,cc); GF2EXModulus MF(mod);
  long agree=0, nontriv=0;
  for(int tr=0;tr<trials;tr++){
    GF2EX beta; random(beta,R);
    stat_mul=stat_sqr=stat_frob=0;
    double t0=now();
    // Itoh-Tsujii: N_k = prod_{j<k} sigma^{hj}(beta)
    GF2EX N=beta, T; long k=1; long nb=NumBits(ZZ(n));
    for(long i=nb-2;i>=0;i--){ frobH(T,N,h*k); mulH(N,N,T); k*=2; if((n>>i)&1){ frobH(T,beta,h*k); mulH(N,N,T); k++; } }
    double t1=now();
    GF2EX zB; powH(zB,N,u); double t2=now();
    bool one = IsOne(zB);
    printf("trial %d: D=%ld h=%ld n=%ld  norm %.4fs (%ld mul %ld frob)  u-exp %.4fs  total %.4fs  phase==1? %d\n",tr,D,h,n,t1-t0,stat_mul,stat_frob,t2-t1,t2-t0,(int)one);

    // Method C: test (N^{P-})^{Phi_h(2)/p} == 1, P- = prod_{d|h, mu(h/d)=-1} (2^d-1)
    double t5=now(); long smul0=stat_mul;
    vector<long> pf=primefac(h); long np=pf.size();
    GF2EX Mx=N; ZZ Phi; Phi=1; ZZ Pminus; Pminus=1; ZZ Pplus; Pplus=1;
    for(long mask=0; mask<(1L<<np); mask++){ long q=1; int bits=0; for(long i=0;i<np;i++) if(mask>>i&1){ q*=pf[i]; bits++; }
      long d=h/q; ZZ term=power2_ZZ(d)-1; if(bits%2==0) Pplus*=term; else { Pminus*=term; if(d>1) pow2m1(Mx,Mx,d); } }
    Phi = Pplus/Pminus; if(Phi*Pminus!=Pplus || Phi%p!=0){ printf("cyclotomic bookkeeping error\n"); return 1; }
    ZZ e2=Phi/p; GF2EX zC; powH(zC,Mx,e2); double t6=now();
    printf("   methodC: phi-exponent bits=%ld (u bits=%ld) mults=%ld time %.4fs  phase==1? %d  consistent=%d\n", NumBits(e2), NumBits(u), stat_mul-smul0, t6-t5, (int)IsOne(zC), (int)(IsOne(zC)==one));
    if(!(IsOne(zC)==one)) { printf("METHOD C DISAGREES\n"); return 2; }
    if(!one) nontriv++;
    if(ref){ double t3=now(); GF2EX zA; ZZ e=(power2_ZZ(D)-1)/p; PowerMod(zA,beta,e,MF); double t4=now();
      printf("   reference PowerMod %.3fs  agree=%d\n",t4-t3,(int)(zA==zB)); if(zA==zB) agree++; }
    fflush(stdout);
  }
  printf("summary trials=%d nontrivial=%ld agree=%ld\n",trials,nontriv,agree);
}
