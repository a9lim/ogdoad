import pickle, sys, collections, math
res = pickle.load(open(sys.argv[1], 'rb'))
rows = pickle.load(open('/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/rows_1000000.pkl', 'rb'))
mof = {r[0]: r[4] for r in rows}; Qof = {r[0]: r[2] for r in rows}
for r in res:
    r['row'] = (Qof[r['ell']] == r['Q'] and mof[r['ell']] == r['m'])
    r['sibrow'] = (Qof[r['ell']] == r['Q'] and mof[r['ell']] != r['m'])
def summarize(sel, label):
    n = len(sel); obs = sum(r['power'] for r in sel); exp = sum(1/r['ell'] for r in sel)
    var = sum((1/r['ell'])*(1-1/r['ell']) for r in sel)
    z = (obs-exp)/math.sqrt(var) if var else float('nan')
    print(f'{label:45s} n={n:6d} obs={obs:5d} exp={exp:8.2f} z={z:+.2f}')
    return obs
verbose = len(sys.argv) > 2
for arm in ('Z','O','C','D'):
    for elem in ('sel','kap+0','sel+1','kap+w'):
        sel=[r for r in res if r['arm']==arm and r['elem']==elem]
        if not sel: continue
        o = summarize([r for r in sel if r['row']], f'{arm} {elem} ROW')
        if o and elem != 'kap+0':
            print('     ', [(r['Q'], r['ell']) for r in sel if r['row'] and r['power']])
        summarize([r for r in sel if r['sibrow']], f'{arm} {elem} sibling-arm row')
        summarize([r for r in sel if not r['row'] and not r['sibrow']], f'{arm} {elem} nonrow')
        if verbose:
          for ell in (3,5,7,11,13,17,31,73,127):
            s=[r for r in sel if not r['row'] and not r['sibrow'] and r['ell']==ell]
            if s: summarize(s, f'   {arm} {elem} nonrow ell={ell}')
