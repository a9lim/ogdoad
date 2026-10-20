/* M(n) curve for a gf2x build: default gf2x_mul, toom, and fft(K) variants; best of. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "gf2x.h"
#include "gf2x/gf2x-impl-export.h"
#include "gf2x/gf2x-impl.h"
#ifndef GF2X_FFT_ADJUST_DEPTH
#define GF2X_FFT_ADJUST_DEPTH 1
#endif
static int okK(long n,long K){ long a=K<0?-K:K; gf2x_ternary_fft_info_t o; if(gf2x_ternary_fft_info_init(o,n*64,n*64)<0) return 0; int sp=o->split; gf2x_ternary_fft_info_clear(o); if((sp||K<0) && a<64) return 0; return 1; }
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
static unsigned long rng=88172645463325252UL; static unsigned long xr(void){ rng^=rng<<13; rng^=rng>>7; rng^=rng<<17; return rng; }
#define TIMEIT(res, stmt) do{ double best=1e99; double tot0=now(); int reps=0; while(1){ double t0=now(); int inner=0; double t1; do { stmt; inner++; t1=now(); } while(t1-t0<0.02); double per=(t1-t0)/inner; if(per<best) best=per; reps++; if(reps>=9 || now()-tot0>2.5) break;} res=best; }while(0)
int main(int argc, char**argv){
  long maxw = argc>1 ? atol(argv[1]) : 1600000;
  long Ks[] = {9,27,81,243,729,2187,6561,19683};
  printf("%9s %12s %10s %10s %10s %8s\n","words","bits","default_s","toom_s","bestfft_s","bestK");
  for(double nf=16; nf<=maxw; nf*=1.5){
    long n=(long)nf;
    unsigned long *a=malloc(n*8), *b=malloc(n*8), *c=malloc(2*n*8), *c2=malloc(2*n*8);
    for(long i=0;i<n;i++){a[i]=xr(); b[i]=xr();}
    double td, tt=-1, tf=1e99; long bk=0;
    TIMEIT(td, gf2x_mul(c,a,n,b,n));
    if(n<=200000){ unsigned long *stk=malloc(gf2x_toomspace(n)*8); TIMEIT(tt, gf2x_mul_toom(c2,a,b,n,stk)); if(memcmp(c,c2,2*n*8)){printf("TOOM MISMATCH\n");} free(stk);}
    if(n>=200) for(int s=-1;s<=1;s+=2) for(int i=0;i<8;i++){ long K=s*Ks[i]; if(!okK(n,K)) continue; if(Ks[i]*Ks[i] > 64*n*4) continue; if(Ks[i]*8 > 64*n) continue;
        double tk; int r=gf2x_mul_fft(c2,a,n,b,n,K); if(r) continue; if(memcmp(c,c2,2*n*8)){printf("FFT MISMATCH K=%ld\n",K); continue;}
        TIMEIT(tk, r=gf2x_mul_fft(c2,a,n,b,n,K)); if(tk<tf){tf=tk;bk=K;} }
    printf("%9ld %12ld %10.3e %10.3e %10.3e %8ld\n",n,n*64,td,tt,tf<1e98?tf:-1,bk); fflush(stdout);
    free(a);free(b);free(c);free(c2);
  }
}
