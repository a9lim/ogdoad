import sys, json, subprocess, pickle, os
from concurrent.futures import ThreadPoolExecutor
sys.path.insert(0, '..')
import census as C
from rowprog import row_program
oeis=[int(x) for x in open('/Users/a9lim/Work/ogdoad/src/scalar/big/ordinal/b380496.txt').read().split()[1::2]]
odd=[p for p in C.primes if p>2]
known={p:m for p,m in zip(odd,oeis)}; known[719]=1; known[727]=1
LIMIT=int(sys.argv[1]) if len(sys.argv)>1 else 60000
rows=pickle.load(open('../rows_1000000.pkl','rb'))
todo=[r for r in rows if r[0] in known and r[5]<=LIMIT]
def run(r):
    p,h,Q,arm,rule,E=r
    trans=list(range(0,rule+1))
    prog=row_program(p, known, trans)
    out=subprocess.run(['./refengine'],input=prog,capture_output=True,text=True)
    if out.returncode!=0: return (p,'ERROR',out.stderr[-300:])
    res=[(int(l.split('m=')[1].split()[0]), int(l.split('pth_power=')[1].split()[0])) for l in out.stdout.splitlines() if l.startswith('p=')]
    m=next((mm for mm,pw in res if pw==0), None)
    return (p, m, known[p])
with ThreadPoolExecutor(16) as ex:
    results=list(ex.map(run, todo))
bad=[x for x in results if x[1]!=x[2]]
print('rows checked', len(results), 'mismatches', bad)
