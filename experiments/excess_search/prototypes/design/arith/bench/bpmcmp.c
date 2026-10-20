#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include "gf2x.h"
#include "bitpolymul.h"
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
static uint64_t rng=88172645463325252ULL; static uint64_t xr(void){ rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; return rng; }
int main(void){
  for(int lg=10; lg<=21; lg++){
    unsigned n=1u<<lg;
    uint64_t *a=aligned_alloc(32,n*8),*b=aligned_alloc(32,n*8),*c=aligned_alloc(32,2*n*8),*d=aligned_alloc(32,2*n*8);
    for(unsigned i=0;i<n;i++){a[i]=xr();b[i]=xr();}
    gf2x_mul((unsigned long*)c,(unsigned long*)a,n,(unsigned long*)b,n);
    bitpolymul_2_128(d,a,b,n);
    int ok=!memcmp(c,d,2*n*8);
    double tg=1e9,tb=1e9;
    for(int r=0;r<5;r++){ double t=now(); gf2x_mul((unsigned long*)c,(unsigned long*)a,n,(unsigned long*)b,n); t=now()-t; if(t<tg)tg=t;
      t=now(); bitpolymul_2_128(d,a,b,n); t=now()-t; if(t<tb)tb=t; }
    double tb64=1e9; for(int r=0;r<3;r++){ double t=now(); bitpolymul_2_64(d,a,b,n); t=now()-t; if(t<tb64)tb64=t; }
    int ok64=!memcmp(c,d,2*n*8);
    printf("words=2^%d bits=%.3g gf2x=%.4fs bitpolymul128=%.4fs (%s) bitpolymul64=%.4fs (%s) ratio=%.2f\n",lg,(double)n*64,tg,tb,ok?"ok":"BAD",tb64,ok64?"ok":"BAD",tg/(tb<tb64?tb:tb64));
    fflush(stdout); free(a);free(b);free(c);free(d);
  }
}
