"""Dependency-aware row search with the validated reference engine.
Appends one JSON line per row to results_ref.jsonl; a counterexample line has
"COUNTEREXAMPLE": true and the engine then also tests further translates."""
import sys, json, subprocess, pickle, os, time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
sys.path.insert(0, '..')
import census as C
from rowprog import row_program, factor_pp
LIMIT = int(sys.argv[1]); PMAX = int(sys.argv[2]); WORKERS = int(sys.argv[3]) if len(sys.argv) > 3 else 12
OUT = 'results_ref.jsonl'
oeis = [int(x) for x in open('/Users/a9lim/Work/ogdoad/src/scalar/big/ordinal/b380496.txt').read().split()[1::2]]
odd = [p for p in C.primes if p > 2]
known = {p: m for p, m in zip(odd, oeis)}; known[719] = 1; known[727] = 1
PEETERS = {int(k): v for k, v in json.load(open('../peeters_records.json')).items()}
UNVERIFIED = {p for p in PEETERS if p not in known}
for p, v in PEETERS.items(): known.setdefault(p, v)
if os.path.exists(OUT):
    for l in open(OUT):
        d = json.loads(l); known[d['p']] = d['m']
rows = pickle.load(open('../rows_1000000.pkl', 'rb'))
def deps(p):
    out = set(); stack = [p]
    while stack:
        x = stack.pop()
        for q in C.Qset(C.ordtwo(x)):
            r, _ = factor_pp(q)
            if r > 2 and r not in out: out.add(r); stack.append(r)
    return out
todo = [r for r in rows if r[0] not in known and r[0] <= PMAX and r[5] <= LIMIT]
print(f'{len(todo)} rows to do, sum1/p={sum(1/r[0] for r in todo):.4f}', flush=True)
def run(r):
    p, h, Q, arm, rule, E = r
    t = time.time()
    trans = list(range(0, rule + 1))
    out = subprocess.run(['./refengine'], input=row_program(p, known, trans), capture_output=True, text=True)
    if out.returncode != 0:
        return {'p': p, 'error': out.stderr[-500:]}
    res = [(int(l.split('m=')[1].split()[0]), int(l.split('pth_power=')[1].split()[0])) for l in out.stdout.splitlines() if l.startswith('p=')]
    forced_ok = all(pw == 1 for mm, pw in res if mm < rule)
    rule_pw = dict(res)[rule]
    d = {'closure_unverified': sorted(deps(p) & UNVERIFIED), 'p': p, 'h': h, 'Q': list(Q), 'arm': arm, 'rule': rule, 'E': E, 'forced_ok': forced_ok, 'secs': round(time.time() - t, 2)}
    if rule_pw == 0 and forced_ok:
        d['m'] = rule; d['class'] = 'ok'
    else:
        # A hit is evidence: record it immediately, before anything else; no translate search here.
        d['class'] = 'HIT_CANDIDATE' if forced_ok else 'FORCED_FAILURE'
        d['translates'] = res
        with open('HITS.jsonl', 'a') as fh: fh.write(json.dumps(d) + '\n'); fh.flush(); os.fsync(fh.fileno())
        print('!!! ' + d['class'], d, flush=True)
    return d
pending = {}; blocked = list(todo)
with ThreadPoolExecutor(WORKERS) as ex:
    while blocked or pending:
        ready = [r for r in blocked if deps(r[0]) <= set(known)]
        ready = ready[:WORKERS * 2 - len(pending)] if len(pending) < WORKERS * 2 else []
        for r in ready:
            blocked.remove(r); pending[ex.submit(run, r)] = r
        if not pending:
            print('stuck: unresolved deps for', [r[0] for r in blocked[:10]], flush=True); break
        done, _ = wait(pending, return_when=FIRST_COMPLETED)
        for f in done:
            r = pending.pop(f); d = f.result()
            if 'error' in d:
                # possible ancestor failure or engine error: never unblocks descendants
                with open('ERRORS.jsonl', 'a') as fh: fh.write(json.dumps(d) + '\n')
                print('ERROR', d, flush=True); continue
            if d['class'] != 'ok':
                continue  # already recorded in HITS.jsonl; descendants stay blocked
            known[d['p']] = d['m']
            with open(OUT, 'a') as fh: fh.write(json.dumps(d) + '\n')
print('done', flush=True)
