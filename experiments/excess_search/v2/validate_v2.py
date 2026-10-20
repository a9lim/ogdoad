"""Validate engine v2 against every known row it can do.

For each row in OEIS b-file (p <= 709) U certificates {719, 727} U
../ref/results_ref.jsonl U ../peeters_records.json with a v2 path and
B <= BCAP, Rt <= RTCAP:
  * run v2 (and its direct full-exponent Euler cross-check when Rt <= DCAP);
  * run the reference-engine copy when E <= ECAP and compare EVERY translate;
  * compare the resulting excess with every source that has the row.
Writes validation_log.jsonl (one line per row) and prints a summary.

    python3 validate_v2.py BCAP RTCAP DCAP ECAP WORKERS
"""
import json
import os
import sys
from concurrent.futures import ThreadPoolExecutor

import census2 as C
import driver as DR
import plan as PL

HERE = os.path.dirname(os.path.abspath(__file__))
BCAP = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10**5
RTCAP = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10**6
DCAP = int(float(sys.argv[3])) if len(sys.argv) > 3 else 20000
ECAP = int(float(sys.argv[4])) if len(sys.argv) > 4 else 60000
W = int(sys.argv[5]) if len(sys.argv) > 5 else 6
LOG = os.path.join(HERE, sys.argv[6] if len(sys.argv) > 6 else "validation_log.jsonl")

src = DR.load_sources()
known = DR.known_excess(src, use=("oeis", "cert", "ref", "peeters"))
rows = []
for p in sorted(known):
    if p < 3:
        continue
    try:
        pl = PL.plan(p, known)
    except PL.Refuse:
        continue
    if pl["B"] <= BCAP and pl["Rt"] <= RTCAP:
        rows.append(pl)
done = set()
if os.path.exists(LOG):
    for line in open(LOG):
        done.add(json.loads(line)["p"])
rows = [r for r in rows if r["p"] not in done]
print(f"{len(rows)} rows to validate (BCAP={BCAP}, RTCAP={RTCAP})", flush=True)


def one(pl):
    p = pl["p"]
    v = DR.run_rows([p], known, direct=DCAP)[0]
    rec = {"p": p, "path": pl["path"], "arm": pl["arm"], "E": pl["E"], "B": pl["B"], "t": pl["t"],
           "D": pl["D"], "R": pl["R"], "Rt": pl["Rt"], "v2_m": v.get("m"), "v2_res": v.get("res"),
           "v2_forced_ok": v.get("forced_ok"), "v2_cpu": v.get("cpu", {}).get("TOTAL_cpu"),
           "direct_checked": pl["Rt"] <= DCAP, "checks": v.get("checks"), "error": v.get("error")}
    rec["sources"] = {s: src[s][p] for s in ("oeis", "cert", "ref", "peeters") if p in src[s]}
    if pl["E"] <= ECAP:
        r = DR.run_ref(p, known, list(range(pl["rule"] + 1)))
        rec["ref_res"] = r["res"]
        rec["ref_error"] = r["fatal"]
        # same translate labels: v2 label m <-> ref translate m (beta = kappa + m)
        rec["per_translate_agree"] = sorted(map(tuple, v.get("res") or [])) == sorted(map(tuple, r["res"]))
    rec["agree_sources"] = all(rec["v2_m"] == m for m in rec["sources"].values())
    return rec


bad = []
with ThreadPoolExecutor(W) as ex, open(LOG, "a") as fh:
    for rec in ex.map(one, rows):
        fh.write(json.dumps(rec) + "\n")
        fh.flush()
        ok = rec["agree_sources"] and rec.get("per_translate_agree", True) and not rec["error"]
        if not ok:
            bad.append(rec)
            print("MISMATCH", json.dumps(rec), flush=True)
        else:
            print(rec["p"], rec["path"], rec["v2_m"], rec["sources"], "ref-agree" if "ref_res" in rec else "",
                  rec["v2_cpu"], flush=True)
print("mismatches:", len(bad))
