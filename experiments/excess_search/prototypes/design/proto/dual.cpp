// Dual (power-projection) model calculus: every register is the K-valued sequence a_i = ell(theta^i)
// for a nonzero K-linear functional ell; ops act on sequences:
//   BINOM y^r=z : a_i = z^{i/r} [r|i]        SPREAD r : a'_i = a_{i/r} [r|i]
//   SHIFT c     : a'_i = sum_{j subset i} c^{i^j} a_j  (= c^i * zeta(c^{-j} a_j))
//   SUM         : s_i  = sum_{j subset i} a_j b_{i^j}  (Lucas: binom(i,j) odd iff j subset i)
// Final: sigma_i = Tr(lambda s_i) (F_2), BM -> F_2 min poly of the top element (degree checked).
#include <NTL/GF2EX.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <iostream>
#include <sstream>
#include <fstream>
#include <vector>
#include <map>
#include <chrono>
#include <sys/resource.h>
using namespace NTL; using namespace std;
typedef vector<uint64_t> bits;
static double now(){return chrono::duration<double>(chrono::steady_clock::now().time_since_epoch()).count();}
static double cpu(){ struct rusage u; getrusage(RUSAGE_SELF,&u); return u.ru_utime.tv_sec+u.ru_utime.tv_usec*1e-6; }
GF2X hex2poly(const string& h){ GF2X f; long n=h.size(); for(long i=0;i<n;i++){ char c=h[n-1-i]; int v=(c>='a')?c-'a'+10:c-'0'; for(int b=0;b<4;b++) if(v>>b&1) SetCoeff(f,4*i+b);} return f;}
string poly2hex(const GF2X& f){ long d=deg(f); if(d<0) return "0"; string s; for(long i=0;i<=d/4;i++){int v=0; for(int b=0;b<4;b++) if(4*i+b<=d && IsOne(coeff(f,4*i+b))) v|=1<<b; s.push_back("0123456789abcdef"[v]);} while(s.size()>1&&s.back()=='0') s.pop_back(); return string(s.rbegin(),s.rend());}
static long d; static long Nbits, Wn; static int K2; // sequence length = 2^K2 bits
static GF2X PK;
struct Seq { vector<bits> pl; }; // d planes
static inline bool getb(const bits& b, long i){ return (b[i>>6]>>(i&63))&1; }
static inline void setb(bits& b, long i){ b[i>>6]|=1ULL<<(i&63); }
static void zeta_bits(bits& w, int k){
  static const uint64_t HM[6]={0xAAAAAAAAAAAAAAAAULL,0xCCCCCCCCCCCCCCCCULL,0xF0F0F0F0F0F0F0F0ULL,0xFF00FF00FF00FF00ULL,0xFFFF0000FFFF0000ULL,0xFFFFFFFF00000000ULL};
  long W=w.size();
  for(int b=0;b<6 && b<k;b++){ int s=1<<b; for(long i=0;i<W;i++) w[i]^=(w[i]<<s)&HM[b]; }
  for(int b=6;b<k;b++){ long s=1L<<(b-6); for(long i=0;i<W;i++) if(i&s) w[i]^=w[i^s]; }
}
static vector<bits> pm; // popcount masks
Seq zeroSeq(){ Seq s; s.pl.assign(d,bits(Wn,0)); return s; }
GF2E getK(const Seq& s, long i){ GF2X f; for(long u=0;u<d;u++) if(getb(s.pl[u],i)) SetCoeff(f,u); GF2E e; conv(e,f); return e; }
void putK(Seq& s, long i, const GF2E& e){ const GF2X& f=rep(e); for(long u=0;u<=deg(f);u++) if(IsOne(coeff(f,u))) setb(s.pl[u],i); }
Seq binom(long r, const GF2E& z){ Seq s=zeroSeq(); GF2E zp; set(zp); for(long i=0;i<Nbits;i+=r){ putK(s,i,zp); zp*=z; } return s; }
Seq lin(const GF2E& v){ Seq s=zeroSeq(); GF2E vp; set(vp); for(long i=0;i<Nbits;i++){ putK(s,i,vp); vp*=v; } return s; }
Seq spread(const Seq& c, long r){ Seq s=zeroSeq(); for(long u=0;u<d;u++) for(long j=0;j*r<Nbits;j++) if(getb(c.pl[u],j)) setb(s.pl[u],j*r); return s; }
Seq shiftK(const Seq& c, const GF2E& v){
  Seq s=c;
  if(IsOne(v)){ for(long u=0;u<d;u++) zeta_bits(s.pl[u],K2); return s; }
  // a'_i = v^i * zeta( v^{-j} a_j )_i   (exact since c^{i^j}=c^i c^{-j} for j subset i)
  GF2E vi; inv(vi,v); GF2E p; set(p); Seq t=zeroSeq();
  for(long j=0;j<Nbits;j++){ GF2E a=getK(c,j); if(!IsZero(a)) putK(t,j,a*p); p*=vi; }
  for(long u=0;u<d;u++) zeta_bits(t.pl[u],K2);
  Seq o=zeroSeq(); set(p); for(long i=0;i<Nbits;i++){ GF2E a=getK(t,i); if(!IsZero(a)) putK(o,i,a*p); p*=v; }
  return o;
}
// bitsliced K-multiply-accumulate: H (d planes) += A (d planes) * B (d planes) mod PK, over word range
static vector<long> PKlow; // exponents j<d with coefficient 1 in PK
static void kmac(uint64_t** H, uint64_t** A, uint64_t** B, long W, vector<bits>& tmp){
  long D2=2*d-1; for(long w=0;w<D2;w++) std::fill(tmp[w].begin(), tmp[w].begin()+W, 0);
  for(long u=0;u<d;u++) for(long v=0;v<d;v++){ uint64_t* t=tmp[u+v].data(); const uint64_t* x=A[u]; const uint64_t* y=B[v]; for(long i=0;i<W;i++) t[i]^=x[i]&y[i]; }
  for(long w=D2-1; w>=d; w--) for(long j: PKlow){ uint64_t* t=tmp[w-d+j].data(); const uint64_t* x=tmp[w].data(); for(long i=0;i<W;i++) t[i]^=x[i]; }
  for(long u=0;u<d;u++){ uint64_t* h=H[u]; const uint64_t* t=tmp[u].data(); for(long i=0;i<W;i++) h[i]^=t[i]; }
}
Seq sumK(const Seq& a, const Seq& b){
  int k=K2; vector<vector<bits>> Ar(k+1, vector<bits>(d, bits(Wn))), Br=Ar, Hr(k+1, vector<bits>(d, bits(Wn,0)));
  for(int r=0;r<=k;r++) for(long u=0;u<d;u++){ for(long i=0;i<Wn;i++){ Ar[r][u][i]=a.pl[u][i]&pm[r][i]; Br[r][u][i]=b.pl[u][i]&pm[r][i]; } zeta_bits(Ar[r][u],k); zeta_bits(Br[r][u],k); }
  vector<bits> tmp(2*d-1, bits(Wn));
  // blocked over words to keep tmp small in cache
  const long BLK=4096;
  for(long w0=0; w0<Wn; w0+=BLK){ long W=min(BLK,Wn-w0);
    for(int r=0;r<=k;r++) for(int r1=0;r1<=r;r1++){
      vector<uint64_t*> H(d),A(d),B(d); for(long u=0;u<d;u++){ H[u]=Hr[r][u].data()+w0; A[u]=Ar[r1][u].data()+w0; B[u]=Br[r-r1][u].data()+w0; }
      kmac(H.data(),A.data(),B.data(),W,tmp);
    }
  }
  Seq s=zeroSeq();
  for(int r=0;r<=k;r++) for(long u=0;u<d;u++){ zeta_bits(Hr[r][u],k); for(long i=0;i<Wn;i++) s.pl[u][i]^=Hr[r][u][i]&pm[r][i]; }
  return s;
}
int main(int argc,char**argv){
  ifstream in(argv[1]); string mode=argc>2?argv[2]:""; string line;
  long p=0,E=0,h=0,m=0,top=-1; vector<vector<string>> ops; string PKhex;
  while(getline(in,line)){ if(line.empty()) continue; istringstream ss(line); vector<string> t; string x; while(ss>>x) t.push_back(x); ops.push_back(t); }
  for(auto& t: ops){ if(t[0]=="K"){ d=stol(t[1]); PKhex=t[2]; } if(t[0]=="ROW"){ p=stol(t[1]); E=stol(t[2]); h=stol(t[3]); m=stol(t[4]); } if(t[0]=="TOP") top=stol(t[1]); }
  PK=hex2poly(PKhex); GF2E::init(PK); for(long j=0;j<d;j++) if(IsOne(coeff(PK,j))) PKlow.push_back(j);
  long n=2*E; K2=0; while((1L<<K2)<n) K2++; Nbits=1L<<K2; Wn=max(1L,Nbits/64);
  pm.assign(K2+1,bits(Wn,0)); for(long S=0;S<Nbits;S++) setb(pm[__builtin_popcountl(S)],S);
  double t0=now(), c0=cpu();
  // registers computed at full length (simple version)
  map<long,Seq> reg;
  for(auto& t: ops){ if(t[0]=="K"||t[0]=="ROW"||t[0]=="TOP"||t[0]=="TRANS") continue; long id=stol(t[0]); const string& op=t[1];
    if(op=="BINOM") reg[id]=binom(stol(t[2]), [&]{GF2E e; conv(e,hex2poly(t[3])); return e;}());
    else if(op=="LIN") reg[id]=lin([&]{GF2E e; conv(e,hex2poly(t[2])); return e;}());
    else if(op=="SPREAD") reg[id]=spread(reg[stol(t[2])], stol(t[3]));
    else if(op=="SHIFT") reg[id]=shiftK(reg[stol(t[2])], [&]{GF2E e; conv(e,hex2poly(t[3])); return e;}());
    else if(op=="SUM") reg[id]=sumK(reg[stol(t[2])], reg[stol(t[3])]);
  }
  Seq& S=reg[top];
  // trace functional lambda=1: sigma_i = sum_u Tr(z^u) * plane_u[i]
  vector<int> tr(d); for(long u=0;u<d;u++){ GF2E zu; if(d==1) set(zu); else { GF2X x; SetCoeff(x,u); conv(zu,x);} tr[u]= IsOne(trace(zu)); }
  vec_GF2 sv; sv.SetLength(n); for(long i=0;i<n;i++){ int b=0; for(long u=0;u<d;u++) if(tr[u]) b^=getb(S.pl[u],i); sv[i]=b; }
  double t1=now(); GF2X P; MinPolySeq(P,sv,E); double t2=now();
  cout<<"p="<<p<<" E="<<E<<" d="<<d<<" seqs="<<t1-t0<<"s bm="<<t2-t1<<"s cpu="<<cpu()-c0<<" degP="<<deg(P)<<endl;
  if(deg(P)!=E){ cerr<<"BM degree "<<deg(P)<<" != E"<<endl; return 4; }
  if(mode.find('n')!=string::npos) cout<<"MINPOLY "<<poly2hex(P)<<endl;
  if(mode.find('e')!=string::npos){ ZZ N=(power2_ZZ(E)-1); N/=p; GF2XModulus F(P); GF2X r; PowerXMod(r,N,F); cout<<"EULER pth_power="<<(IsOne(r)?1:0)<<endl;
    GF2X b1; SetX(b1); b1+=1; GF2X r1; PowerMod(r1,b1,N,F); cout<<"EULER_PLUS1 pth_power="<<(IsOne(r1)?1:0)<<endl; }
}
