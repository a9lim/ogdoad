import pickle
from tower import *
rows = pickle.load(open('/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/rows_1000000.pkl','rb'))
cyc = {2,3,5,17,257,65537}
seen=set(); hits=0; n=0
for (p,h,Q,a,m,E) in rows:
    if a!='Z' or len(Q)!=2 or E>6000 or E%2 or Q in seen: continue
    if not all(min(factor(q)) in cyc for q in Q): continue
    seen.add(Q)
    T=Tower(Q); q=1<<(E//2)
    c1,c2=T.chi[Q[0]],T.chi[Q[1]]
    inT=[(c1/c2)**(q+1)==T.one, (c1*c2)**(q+1)==T.one]
    n+=1; hits+=any(inT)
    print(Q,E,inT,flush=True)
print('pairs',n,'torus hits',hits)
