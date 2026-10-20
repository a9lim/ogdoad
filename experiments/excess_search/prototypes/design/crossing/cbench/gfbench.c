#include <gf2x.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
static double now(){struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec;}
int main(){
  long sizes[]={100000,1000000,3000000,10000000,30000000,100000000,300000000,1000000000};
  for(int s=0;s<8;s++){
    long bits=sizes[s]; long n=(bits+63)/64;
    unsigned long *a=malloc(8*n),*b=malloc(8*n),*c=malloc(16*n);
    for(long i=0;i<n;i++){a[i]=random()*2654435761UL^((unsigned long)random()<<32);b[i]=a[i]*31+7;}
    int reps = bits<=1000000?20:(bits<=30000000?3:1);
    double t=now(); for(int r=0;r<reps;r++) gf2x_mul(c,a,n,b,n); t=(now()-t)/reps;
    printf("bits=%ld gf2x_mul=%.3f ms\n",bits,t*1e3); fflush(stdout);
    free(a);free(b);free(c);
  }
}
