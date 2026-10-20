/* inner-product kernel: sum_i x_i*y_i in F_2[l] (unreduced, accumulate), reduce once.
   Measures the cost per k-multiply-accumulate for t-bit k (w = ceil(t/64) words). */
#include <immintrin.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <time.h>
static double now(){struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec;}
static inline void clmul_acc(__m128i *acc, const uint64_t *x, const uint64_t *y, int w){
  for(int i=0;i<w;i++){ __m128i a=_mm_set_epi64x(0,x[i]);
    for(int j=0;j<w;j++){ __m128i b=_mm_set_epi64x(0,y[j]);
      acc[i+j]=_mm_xor_si128(acc[i+j],_mm_clmulepi64_si128(a,b,0)); } }
}
int main(){
  int ts[]={179,359,500,1000,2500};
  for(int k=0;k<5;k++){
    int t=ts[k], w=(t+63)/64; long D=200000; 
    uint64_t *X=malloc(8*w*D),*Y=malloc(8*w*D);
    for(long i=0;i<w*D;i++){X[i]=((uint64_t)rand()<<33)^rand(); Y[i]=X[i]*0x9E3779B97F4A7C15ULL;}
    __m128i acc[128]; for(int i=0;i<128;i++) acc[i]=_mm_setzero_si128();
    double t0=now();
    for(long i=0;i<D;i++) clmul_acc(acc,X+i*w,Y+i*w,w);
    double dt=(now()-t0)/D;
    uint64_t s=0; for(int i=0;i<2*w;i++) s^=_mm_extract_epi64(acc[i],0)^_mm_extract_epi64(acc[i],1);
    printf("t=%d words=%d  mul-acc per k-term = %.2f ns (chk %llx)\n",t,w,dt*1e9,(unsigned long long)s);
    free(X);free(Y);
  }
}
