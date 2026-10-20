import sys; _argv = sys.argv[:]; sys.argv = ["x", "100000"]
import pickle, sys
from tower import closure, factor
rows = pickle.load(open('/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/rows_1000000.pkl','rb'))
mof = {r[0]: r[4] for r in rows}; Qof = {r[0]: r[2] for r in rows}; Eof={r[0]:r[5] for r in rows}; armof={r[0]:r[3] for r in rows}
res = pickle.load(open(_argv[1], 'rb'))
extra = [int(x) for x in _argv[2:]]
ver = {}
for r in res:
    if r['elem'] != 'sel': continue
    l = r['ell']
    if Qof[l] == r['Q'] and mof[l] == r['m'] and l > 727:
        ver[l] = ver.get(l, True) and (not r['power'])
for p in extra: ver[p] = True
fails = [p for p, ok in ver.items() if not ok]
def ancestors(Q):
    comps = closure(Q); return sorted({min(factor(q)) for q in comps if q % 2})
cond = [p for p in ver if any(a > 709 for a in ancestors(Qof[p]))]
print('verified new rows', len(ver), 'failures', fails, 'conditional (ancestor>709):', cond)
print('mass', round(sum(1/p for p in ver), 4))
ps = sorted(ver)
print(', '.join(f'{p}' for p in ps))
print('by arm', {a: sum(1 for p in ps if armof[p]==a) for a in set(armof[p] for p in ps)})
