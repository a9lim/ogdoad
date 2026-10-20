import sys, math
sys.argv=['x', sys.argv[1]]
exec(open('critic/cf_lib.py').read())
edges=[727,1e3,1e4,1e5,1e6,1e7,1e8]
tot=[0.0]*7; z=[0.0]*7; z2=[0.0]*7; zf=[0.0]*7
for p in primes[1:]:
    p=int(p)
    if p<=727: continue
    h=ordtwo(p); Q=Qset(h); ac=armcode(h,Q)
    i=next(j for j in range(1,7) if p<=edges[j])
    tot[i]+=1/p
    if ac==0:
        z[i]+=1/p
        if any(q&(q-1)==0 for q in Q): z2[i]+=1/p
    if ac==1: zf[i]+=1/p
for i in range(1,7):
    if tot[i]>0: print(f"({edges[i-1]:.0e},{edges[i]:.0e}] tot {tot[i]:.5f} Z {z[i]:.5f} Z2pow {z2[i]:.5f} share {z2[i]/tot[i]:.4f} share*lnx {z2[i]/tot[i]*math.log(math.sqrt(edges[i-1]*edges[i])):.3f} ZF {zf[i]:.2e}", flush=True)
print('Z2pow total', sum(z2))
