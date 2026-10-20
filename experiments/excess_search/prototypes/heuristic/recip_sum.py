"""Exact sum of 1/p and log(1-1/p) over primes in (A, X] by segmented numpy sieve."""
import sys, numpy as np, math
X=int(float(sys.argv[1])); A=int(float(sys.argv[2])) if len(sys.argv)>2 else 727
r=int(X**0.5)+1
s=np.ones(r+1,bool); s[:2]=False
for i in range(2,int(r**0.5)+1):
    if s[i]: s[i*i::i]=False
base=np.nonzero(s)[0]
S=0.0; L=0.0; C=0; seg=10**7
lo=A+1
# checkpoints
cps=sorted(set(int(float(c)) for c in sys.argv[3:]))+[X]
out=[]
while lo<=X:
    hi=min(lo+seg,X+1)
    m=np.ones(hi-lo,bool)
    for p in base:
        if p*p>=hi: break
        st=max(p*p,((lo+p-1)//p)*p)
        m[st-lo::p]=False
    pr=np.nonzero(m)[0]+lo
    pr=pr[pr>=2]
    while cps and cps[0]<hi:
        c=cps.pop(0); sub=pr[pr<=c]
        out.append((c,S+np.sum(1.0/sub),L+np.sum(np.log1p(-1.0/sub)),C+len(sub)))
    S+=np.sum(1.0/pr); L+=np.sum(np.log1p(-1.0/pr)); C+=len(pr)
    lo=hi
for c,s_,l_,n_ in out: print(c, repr(s_), repr(l_), n_)
