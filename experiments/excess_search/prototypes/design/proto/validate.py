"""Validate the K-relative builder: (1) norm to F_2 == term-algebra min poly (independent oracle),
(2) Euler tests reproduce OEIS A380496 (and the structural smaller translates)."""
import sys, subprocess, time, os
from terms import *
from plan import Planner
from tower import oracle_minpoly
EMAX_EULER = int(sys.argv[1]) if len(sys.argv) > 1 else 30000
EMAX_ORACLE = int(sys.argv[2]) if len(sys.argv) > 2 else 6000
oeis = [int(x) for x in open('/Users/a9lim/Work/ogdoad/src/scalar/big/ordinal/b380496.txt').read().split()[1::2]]
known = dict(zip(primes[1:], oeis)); known[719] = 1; known[727] = 1
ok = bad = 0; ochk = 0
for p in primes[1:]:
    if p > 727: break
    E = deg(cl_alpha(p))
    if E > EMAX_EULER: continue
    pl = Planner(p); txt = pl.text()
    fn = f'/tmp/plan_v_{p}.txt'
    open(fn, 'w').write(txt)
    mode = 'e' + ('n' if E <= EMAX_ORACLE else '')
    t = time.time()
    out = subprocess.run(['/private/tmp/claude-501/-Users-a9lim-Work-ogdoad/b7db691f-f4bd-47a5-89a6-06b1f9fbbfc3/scratchpad/search/design/proto/exec', fn, mode], capture_output=True, text=True)
    if out.returncode != 0:
        print('EXEC FAIL', p, out.stderr); bad += 1; continue
    lines = out.stdout.split('\n')
    eul = {int(l.split()[1][2:]): int(l.split()[2].split('=')[1]) for l in lines if l.startswith('EULER')}
    m = min([mm for mm, pw in eul.items() if pw == 0], default=None)
    good = (m == known[p]) and all(eul[mm] == 1 for mm in eul if mm < m)
    msg = ''
    if E <= EMAX_ORACLE:
        normhex = [l.split()[1] for l in lines if l.startswith('NORM')][0]
        orc, L = oracle_minpoly(cl_alpha(p), alpha_monomials(p, 0))
        k = E // L; target = orc
        while k > 1:
            assert k % 2 == 0
            target = sum(1 << (2*i) for i in range(target.bit_length()) if (target >> i) & 1); k //= 2
        same = (target == int(normhex, 16)) and E % L == 0
        ochk += 1
        msg = f'oracle_minpoly_match={same}'
        good = good and same
    print(f'p={p} E={E} degK={pl.degK} m={m} oeis={known[p]} {msg} {"OK" if good else "BAD"} t={time.time()-t:.2f}s', flush=True)
    ok += good; bad += (not good)
print('ok', ok, 'bad', bad, 'oracle checks', ochk)
