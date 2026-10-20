// Production-style composed sum over K = GF(2^d) (char 2), F_2 route:
//   omega = theta_A + kappa + theta_B  (kappa in K chosen so that F_2(omega) = whole field)
//   s_i = L(omega^i), L = ell_A (x) ell_B  (K-bilinear impulse functionals)
//   binomial theorem mod 2 (Lucas): s_i = sum_{j subset i} a_j b_{i^j}  -> subset convolution
//   sigma_i = Tr(lambda s_i) = XOR_u alpha_u(a) * beta_u(b)  (d bitsliced F_2 subset convolutions)
//   P_omega = MinPolySeq_F2(sigma)          (half-gcd BM over F_2)
//   zeta = image of z (generator of K) in F_2[W]/P_omega by the trace-dual formula u = M N^{-1} mod P
//   G_omega = GCD_K(P_omega(W), zeta(W) - z);  CS(Y) = G_omega(Y + kappa)
#include <vector>
#include <cstdint>
typedef std::vector<uint64_t> bits;
static inline void zeta_bits(bits& w, int k){ // subset-sum transform over F_2 on 2^k bits
  static const uint64_t HM[6]={0xAAAAAAAAAAAAAAAAULL,0xCCCCCCCCCCCCCCCCULL,0xF0F0F0F0F0F0F0F0ULL,0xFF00FF00FF00FF00ULL,0xFFFF0000FFFF0000ULL,0xFFFFFFFF00000000ULL};
  long W=w.size();
  for(int b=0;b<6 && b<k;b++){ int s=1<<b; for(long i=0;i<W;i++) w[i]^=(w[i]<<s)&HM[b]; }
  for(int b=6;b<k;b++){ long s=1L<<(b-6); for(long i=0;i<W;i++) if(i&s) w[i]^=w[i^s]; }
}
struct SubsetConvF2 {
  int k; long N, W; std::vector<bits> pm; std::vector<bits> H;
  SubsetConvF2(int k_):k(k_),N(1L<<k_),W(std::max(1L,(1L<<k_)/64)){
    pm.assign(k+1,bits(W,0)); for(long S=0;S<N;S++){ int r=__builtin_popcountl(S); pm[r][S>>6]|=1ULL<<(S&63); }
    H.assign(k+1,bits(W,0));
  }
  void accumulate(const bits& a, const bits& b){ // H_r += sum_{r1} zeta(a_r1) & zeta(b_{r-r1})
    std::vector<bits> A(k+1,bits(W)), B(k+1,bits(W));
    for(int r=0;r<=k;r++){ for(long i=0;i<W;i++){ A[r][i]=a[i]&pm[r][i]; B[r][i]=b[i]&pm[r][i]; } zeta_bits(A[r],k); zeta_bits(B[r],k); }
    for(int r=0;r<=k;r++) for(int r1=0;r1<=r;r1++){ const uint64_t* x=A[r1].data(); const uint64_t* y=B[r-r1].data(); uint64_t* h=H[r].data(); for(long i=0;i<W;i++) h[i]^=x[i]&y[i]; }
  }
  bits finish(){ bits out(W,0); for(int r=0;r<=k;r++){ zeta_bits(H[r],k); for(long i=0;i<W;i++) out[i]^=H[r][i]&pm[r][i]; } return out; }
};
