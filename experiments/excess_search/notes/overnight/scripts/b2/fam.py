# Sanity check of family facts (orders, decomposition index m, -1 in <2>, Q(h)) -- no rows.
import sys; sys.argv=['x','3000']
sys.path.insert(0,'/Users/a9lim/Work/ogdoad/experiments/excess_search')
sys.path.insert(0,'/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/0d823db5-514b-4211-b6ff-3cb614bd36e4/scratchpad/me')
import census
from nim import order
from sympy import totient, n_order
def info(N):
    f=n_order(2,N); neg=any(pow(2,j,N)==N-1 for j in range(f))
    fp=f//2 if neg else f
    return f,neg,fp,totient(N)//(2*fp)
print("h=4*3^k family")
for k in range(1,8):
    h=4*3**k; N=5*3**(k+1); print(k,h,census.Qset(h),census.dsum(census.Qset(h)),info(N))
print("3^b 5^c family")
for b in range(1,4):
  for c in range(1,3):
    N=3**(b+1)*5**(c+1)
    hs=[3**b*5**c,2*3**b*5**c,4*3**b*5**c]
    print(b,c,[(h,census.Qset(h),census.dsum(census.Qset(h))) for h in hs],info(N))
print("2^a 3^b family (b=1,2)")
for a in range(2,6):
    ca=1<<(1<<(a-2)) if a>=2 else 2   # kappa_{2^a}=c_{a-1}=2^(2^(a-1)); careful
    ca=1<<(1<<(a-1))
    oa=order(ca,(1<<(1<<a))-1)
    for b in (1,2):
        h=2**a*3**b; N=oa*3**(b+1)//__import__('math').gcd(oa,3**(b+1))
        print(a,b,h,census.Qset(h),'ord c',oa,'N',N,info(N))
print("3^b 7^c (b=2,c=1)", census.Qset(9*7), info(27*49))
