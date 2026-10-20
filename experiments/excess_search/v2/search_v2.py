"""Dependency-aware search with engine v2 over rows not covered by OEIS,
the certificates, ../ref results, or Peeters' records.

    python3 search_v2.py PMAX WORKERS BCAP RTCAP [classes]

classes (comma list, in priority order): missO (arm O/C/D rows of
../missing_below_12289.json), missZ (other missing rows), hi (12289 <= p <= PMAX).
Rows sharing a conductor h run in one engine call.  Appends to results_v2.jsonl.
"""
import json
import os
import sys
import time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait

import census2 as C
import driver as DR
import plan as PL

HERE = os.path.dirname(os.path.abspath(__file__))
PMAX = int(float(sys.argv[1]))
W = int(sys.argv[2])
BCAP = int(float(sys.argv[3]))
RTCAP = int(float(sys.argv[4]))
CLASSES = sys.argv[5].split(",") if len(sys.argv) > 5 else ["missO", "missZ", "hi"]

src = DR.load_sources()
known = DR.known_excess(src)
missing = set(json.load(open(os.path.join(HERE, "..", "missing_below_12289.json"))))


def cls(p, arm):
    if p in missing:
        return "missO" if arm in "OCD" else "missZ"
    if 12289 <= p <= PMAX:
        return "hi"
    return None


groups = {}
for p in C.primes:
    if p > PMAX:
        break
    if p < 3 or p in known:
        continue
    try:
        pl = PL.plan(p, None)
    except PL.Refuse:
        continue
    c = cls(p, pl["arm"])
    if c not in CLASSES or pl["B"] > BCAP or pl["Rt"] > RTCAP:
        continue
    g = groups.setdefault(pl["h"], {"ps": [], "cls": c, "pl": pl})
    g["ps"].append(p)
    if CLASSES.index(c) < CLASSES.index(g["cls"]):
        g["cls"] = c
todo = sorted(groups.values(), key=lambda g: (CLASSES.index(g["cls"]), g["ps"][0]))
mass = sum(1 / p for g in todo for p in g["ps"])
print(f"{sum(len(g['ps']) for g in todo)} rows in {len(todo)} conductor groups, mass {mass:.5f}", flush=True)
deps = {g["pl"]["h"]: set().union(*(PL.closure_primes(p) for p in g["ps"])) for g in todo}
pending, blocked = {}, list(todo)
t0 = time.time()
with ThreadPoolExecutor(W) as ex:
    while blocked or pending:
        ready = [g for g in blocked if deps[g["pl"]["h"]] <= set(known)]
        for g in ready[: max(0, W - len(pending))]:
            blocked.remove(g)
            pending[ex.submit(DR.run_rows, g["ps"], dict(known))] = g
        if not pending:
            print("stuck: unresolved deps for", [g["ps"][0] for g in blocked[:20]], flush=True)
            break
        done, _ = wait(pending, return_when=FIRST_COMPLETED)
        for f in done:
            g = pending.pop(f)
            try:
                res = f.result()
            except Exception as e:  # noqa: BLE001
                print("EXC", g["ps"], repr(e), flush=True)
                continue
            for d in res:
                d["class"] = g["cls"]
                with open(DR.V2OUT, "a") as fh:
                    fh.write(json.dumps(d) + "\n")
                if d.get("m") is not None:
                    known[d["p"]] = d["m"]
                flag = d.get("COUNTEREXAMPLE") or not d.get("forced_ok", True) or d.get("error") or d.get("refused")
                print(("!!! " if flag else "") + f"{d['p']} {g['cls']} {d.get('path')} m={d.get('m')} "
                      f"B={d.get('B')} Rt={d.get('Rt')} cpu={d.get('cpu', {}).get('TOTAL_cpu')} "
                      f"[{time.time() - t0:.0f}s]" + (" " + json.dumps(d) if flag else ""), flush=True)
print("done", flush=True)
