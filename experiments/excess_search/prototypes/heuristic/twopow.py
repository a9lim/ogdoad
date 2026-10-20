import pickle, math
rows=pickle.load(open('rows_1000000.pkl','rb'))
def is2pow(q): return q>1 and q&(q-1)==0
dec=[(727,1e4),(1e4,1e5),(1e5,1e6)]
tot={}
for lo,hi in dec:
    mz=0; m2=0; mall=0; n2=0; ks={}
    for (p,h,Q,arm,rule,E) in rows:
        if not (lo<p<=hi): continue
        mall+=1/p
        if arm=='Z':
            mz+=1/p
            tw=[q for q in Q if is2pow(q)]
            if tw:
                m2+=1/p; n2+=1; k=tw[0].bit_length()-1; ks[k]=ks.get(k,0)+1/p
    print(f"({lo:.0e},{hi:.0e}] all {mall:.4f} Z {mz:.4f} Z-with-2^k {m2:.4f} share-of-Z {m2/mz:.3f} rows {n2} by k {dict((k,round(v,4)) for k,v in sorted(ks.items()))}")
# observed range
m=0;lst=[]
for (p,h,Q,arm,rule,E) in rows:
    if p<=727 and arm=='Z' and any(is2pow(q) for q in Q): m+=1/p; lst.append(p)
print('obs <=727 Z with 2-power comp:', len(lst), round(m,4), lst[:30])
