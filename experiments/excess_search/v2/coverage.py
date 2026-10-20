"""Structural coverage of engine v2 over rows p <= PMAX (assuming the rule for
closure primes, i.e. degrees as in the census).  Writes coverage_<PMAX>.json
with one record per row: path or refusal reason, B, t, D, R, Rt."""
import json
import os
import sys

import census2 as C
import plan as PL

HERE = os.path.dirname(os.path.abspath(__file__))
PMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10**5

recs = []
for p in C.primes:
    if p > PMAX:
        break
    if p < 3:
        continue
    try:
        d = PL.plan(p, None)
        recs.append({k: v for k, v in d.items() if k != "program"})
    except PL.Refuse as e:
        _, h, Q, arm, rule, E = C.row(p)
        recs.append({"p": p, "h": h, "Q": list(Q), "arm": arm, "rule": rule, "E": E, "path": None, "why": str(e)})
json.dump(recs, open(os.path.join(HERE, f"coverage_{PMAX}.json"), "w"))

peeters = {int(k) for k in json.load(open(os.path.join(HERE, "..", "peeters_records.json")))}
missing = set(json.load(open(os.path.join(HERE, "..", "missing_below_12289.json"))))


def summary(sel, label):
    tot = sum(1 / r["p"] for r in sel)
    print(f"\n== {label}: {len(sel)} rows, mass {tot:.5f}")
    for capB, capRt in ((10**4, 10**5), (10**5, 10**5), (10**5, 10**6), (10**6, 10**6)):
        ok = [r for r in sel if r["path"] and r["B"] <= capB and r["Rt"] <= capRt]
        by = {}
        for r in ok:
            by.setdefault(r["path"], [0, 0.0])
            by[r["path"]][0] += 1
            by[r["path"]][1] += 1 / r["p"]
        m = sum(1 / r["p"] for r in ok)
        print(f"  B<={capB:>8} Rt<={capRt:>8}: {len(ok):5d} rows mass {m:.5f} ({m/tot:.1%})  "
              + " ".join(f"{k}:{v[0]}/{v[1]:.4f}" for k, v in sorted(by.items())))
    ref = [r for r in sel if not r["path"]]
    why = {}
    for r in ref:
        key = r["why"].split(":")[0].split("=")[0]
        why[key] = why.get(key, 0) + 1
    print("  refused:", why)


summary([r for r in recs if r["p"] in missing], "missing below 12289 (uncovered by Peeters)")
summary([r for r in recs if 12289 <= r["p"] <= PMAX], f"12289 <= p <= {PMAX}")
summary([r for r in recs if r["p"] > 727 and r["p"] <= PMAX], f"727 < p <= {PMAX} (all)")
