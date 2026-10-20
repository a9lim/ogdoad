#include <arm_neon.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>
#include <sys/resource.h>
#include <gf2x.h>
static double cpu(){ struct rusage u; getrusage(RUSAGE_SELF,&u); return u.ru_utime.tv_sec+u.ru_utime.tv_usec*1e-6; }
// n-word schoolbook/Karatsuba-free product using PMULL, for comparing against gf2x_mul at small sizes
static inline void pm1(uint64_t a, uint64_t b, uint64_t* lo, uint64_t* hi){
  poly128_t r = vmull_p64((poly64_t)a, (poly64_t)b);
  uint64x2_t v = vreinterpretq_u64_p128(r); *lo = vgetq_lane_u64(v,0); *hi = vgetq_lane_u64(v,1);
}
static void school(uint64_t* c, const uint64_t* a, const uint64_t* b, int n){
  for(int i=0;i<2*n;i++) c[i]=0;
  for(int i=0;i<n;i++) for(int j=0;j<n;j++){ uint64_t lo,hi; pm1(a[i],b[j],&lo,&hi); c[i+j]^=lo; c[i+j+1]^=hi; }
}
int main(){
  enum{MAXN=64}; uint64_t a[MAXN],b[MAXN],c[2*MAXN],d[2*MAXN];
  uint64_t s=88172645463325252ULL; for(int i=0;i<MAXN;i++){ s^=s<<13; s^=s>>7; s^=s<<17; a[i]=s; s^=s<<13; s^=s>>7; s^=s<<17; b[i]=s; }
  int sizes[]={1,2,4,8,16,32,64};
  for(int k=0;k<7;k++){ int n=sizes[k]; long reps=20000000/(n*n)+1000;
    double t0=cpu(); for(long r=0;r<reps;r++){ gf2x_mul(c,a,n,b,n); a[0]^=c[0]&1; } double tg=(cpu()-t0)/reps;
    t0=cpu(); for(long r=0;r<reps;r++){ school(d,a,b,n); a[0]^=d[0]&1; } double tp=(cpu()-t0)/reps;
    gf2x_mul(c,a,n,b,n); school(d,a,b,n); int ok=1; for(int i=0;i<2*n;i++) ok&=(c[i]==d[i]);
    printf("words=%d gf2x_mul=%.1f ns  pmull_schoolbook=%.1f ns  agree=%d\n", n, tg*1e9, tp*1e9, ok);
  }
}
