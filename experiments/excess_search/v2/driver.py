"""Engine-v2 driver: run one row (or rows sharing a conductor h) with the
crossed-binomial engine when a path applies, else with the reference-engine
copy when E is small, else refuse.  Reports which path ran.

    python3 driver.py 1433            # one row
    python3 driver.py 359,1433        # rows sharing h, one engine run
    python3 driver.py search PMAX [WORKERS] [BCAP] [RTCAP]
"""
from __future__ import annotations

import json
import os
import subprocess
import sys
import time

import census2 as C
import plan as PL

HERE = os.path.dirname(os.path.abspath(__file__))
SEARCH = os.path.dirname(HERE)
OEIS = "/Users/a9lim/Work/ogdoad/src/scalar/big/ordinal/b380496.txt"
V2OUT = os.path.join(HERE, "results_v2.jsonl")


def load_sources() -> dict[str, dict[int, int]]:
    src: dict[str, dict[int, int]] = {}
    vals = [int(x) for x in open(OEIS).read().split()[1::2]]
    odd = [p for p in C.primes if p > 2]
    src["oeis"] = dict(zip(odd, vals))
    src["cert"] = {719: 1, 727: 1}
    ref = {}
    fn = os.path.join(SEARCH, "ref", "results_ref.jsonl")
    if os.path.exists(fn):
        for line in open(fn):
            d = json.loads(line)
            if d.get("m") is not None and not d.get("COUNTEREXAMPLE"):
                ref[d["p"]] = d["m"]
    src["ref"] = ref
    fn = os.path.join(SEARCH, "peeters_records.json")
    src["peeters"] = {int(k): v for k, v in json.load(open(fn)).items()} if os.path.exists(fn) else {}
    v2 = {}
    if os.path.exists(V2OUT):
        for line in open(V2OUT):
            d = json.loads(line)
            if d.get("m") is not None:
                v2[d["p"]] = d["m"]
    src["v2"] = v2
    return src


def known_excess(src, use=("oeis", "cert", "ref", "peeters", "v2")) -> dict[int, int]:
    k: dict[int, int] = {}
    for s in use:
        for p, m in src[s].items():
            if p in k and k[p] != m:
                raise SystemExit(f"sources disagree at p={p}: {k[p]} vs {m} ({s})")
            k[p] = m
    return k


def parse_engine(out: str) -> dict:
    res, times, checks = [], {}, 0
    fatal = None
    for line in out.splitlines():
        if line.startswith("p="):
            f = dict(kv.split("=") for kv in line.split())
            res.append((int(f["p"]), int(f["m"]), int(f["pth_power"])))
        elif line.startswith("TIME "):
            parts = line.split()
            times[parts[1]] = times.get(parts[1], 0.0) + float(parts[5])
        elif line.startswith("TOTAL"):
            parts = line.split()
            times["TOTAL_wall"] = float(parts[2])
            times["TOTAL_cpu"] = float(parts[4])
            checks = int(parts[6])
        elif line.startswith("FATAL"):
            fatal = line
    return {"res": res, "cpu": times, "checks": checks, "fatal": fatal}


def run_v2(prog: str, direct: int = 0, minpoly: bool = False, timeout=None) -> dict:
    cmd = [os.path.join(HERE, "v2engine"), "--cache", os.path.join(HERE, "cache")]
    if direct:
        cmd += ["--direct", str(direct)]
    if minpoly:
        cmd += ["--minpoly"]
    t = time.time()
    out = subprocess.run(cmd, input=prog, capture_output=True, text=True, cwd=HERE, timeout=timeout)
    d = parse_engine(out.stdout)
    d["rc"] = out.returncode
    d["wall"] = round(time.time() - t, 3)
    d["minpoly"] = [l for l in out.stdout.splitlines() if l.startswith("MINPOLY")]
    if out.returncode != 0 and not d["fatal"]:
        d["fatal"] = out.stderr[-400:]
    return d


def run_ref(p: int, excess, translates, timeout=None) -> dict:
    prog = PL.ref_program(p, excess, translates)
    t = time.time()
    out = subprocess.run([os.path.join(HERE, "refengine")], input=prog, capture_output=True, text=True,
                         cwd=os.path.join(HERE, "refcache"), timeout=timeout)
    res = []
    for line in out.stdout.splitlines():
        if line.startswith("p="):
            f = dict(kv.split("=", 1) for kv in line.split()[:3])
            res.append((int(f["p"]), int(f["m"]), int(f["pth_power"])))
    return {"res": res, "rc": out.returncode, "wall": round(time.time() - t, 3),
            "fatal": None if out.returncode == 0 else out.stderr[-400:]}


def verdict(pl_or_row: dict, res: list[tuple[int, int, int]], p: int) -> dict:
    """Interpret per-translate results for row p (same convention for v2 and ref:
    label m means the element kappa + m, for ratio/finite paths label 0 is beta)."""
    rule = pl_or_row["rule"]
    mine = {m: pw for (pp, m, pw) in res if pp == p}
    forced_ok = all(mine.get(m) == 1 for m in range(rule))
    rule_pw = mine.get(rule)
    if rule_pw is None:
        return {"m": None, "forced_ok": forced_ok, "error": "rule translate missing"}
    if rule_pw == 0 and forced_ok:
        return {"m": rule, "forced_ok": True}
    return {"m": None, "forced_ok": forced_ok, "COUNTEREXAMPLE": rule_pw == 1}


def run_rows(ps: list[int], excess, direct: int = 0, ref_ecap: int = 60000, minpoly=False,
             force_ref=False) -> list[dict]:
    """Run rows sharing one conductor h with v2 (one engine call) or fall back."""
    out = []
    try:
        if force_ref:
            raise PL.Refuse("forced reference path")
        pl = PL.plan(ps[0], excess, ps=ps)
        hs = {C.ordtwo(p) for p in ps}
        if len(hs) != 1:
            raise SystemExit("rows in a batch must share h")
        r = run_v2(pl["program"], direct=direct, minpoly=minpoly)
        info = {k: pl[k] for k in ("h", "Q", "arm", "rule", "E", "path", "B", "R", "t", "D", "Rt")}
        for p in ps:
            d = {"p": p, **info, "engine": "v2", "cpu": r["cpu"], "checks": r["checks"]}
            if r["fatal"]:
                d["error"] = r["fatal"]
            else:
                d.update(verdict(info, r["res"], p))
                d["res"] = [x for x in r["res"] if x[0] == p]
            if r["minpoly"]:
                d["minpoly"] = r["minpoly"]
            out.append(d)
        return out
    except PL.Refuse as why:
        for p in ps:
            row = C.row(p)
            info = dict(zip(("p", "h", "Q", "arm", "rule", "E"), row))
            info["Q"] = list(info["Q"])
            if info["E"] <= ref_ecap:
                r = run_ref(p, excess, list(range(info["rule"] + 1)))
                d = {**info, "path": "reference", "engine": "ref", "why_not_v2": str(why), "wall": r["wall"]}
                if r["fatal"]:
                    d["error"] = r["fatal"]
                else:
                    d.update(verdict(info, r["res"], p))
                    d["res"] = r["res"]
            else:
                d = {**info, "path": None, "refused": str(why)}
            out.append(d)
        return out


if __name__ == "__main__":
    src = load_sources()
    known = known_excess(src)
    if sys.argv[1] != "search":
        ps = [int(x) for x in sys.argv[1].split(",")]
        for d in run_rows(ps, known, direct=int(os.environ.get("V2_DIRECT", "0")),
                          minpoly=bool(os.environ.get("V2_MINPOLY"))):
            print(json.dumps(d))
        sys.exit(0)
    # dependency-aware search over v2-feasible rows not yet known
    from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait

    PMAX = int(sys.argv[2])
    W = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    BCAP = int(float(sys.argv[4])) if len(sys.argv) > 4 else 10**5
    RTCAP = int(float(sys.argv[5])) if len(sys.argv) > 5 else 10**6
    groups: dict[int, list[int]] = {}
    for p in C.primes:
        if p > PMAX:
            break
        if p < 3 or p in known:
            continue
        try:
            pl = PL.plan(p, None)
        except PL.Refuse:
            continue
        if pl["B"] <= BCAP and pl["Rt"] <= RTCAP:
            groups.setdefault(pl["h"], []).append(p)
    todo = sorted(groups.items(), key=lambda kv: kv[1][0])
    print(f"{sum(len(v) for _, v in todo)} rows in {len(todo)} conductor groups, "
          f"mass {sum(1/p for _, v in todo for p in v):.5f}", flush=True)
    deps = {h: set().union(*(PL.closure_primes(p) for p in v)) for h, v in todo}
    pending, blocked = {}, list(todo)
    with ThreadPoolExecutor(W) as ex:
        while blocked or pending:
            ready = [g for g in blocked if deps[g[0]] <= set(known)]
            for g in ready[: max(0, 2 * W - len(pending))]:
                blocked.remove(g)
                pending[ex.submit(run_rows, g[1], dict(known))] = g
            if not pending:
                print("stuck: unresolved deps for", [g[1][0] for g in blocked[:10]], flush=True)
                break
            done, _ = wait(pending, return_when=FIRST_COMPLETED)
            for f in done:
                g = pending.pop(f)
                for d in f.result():
                    with open(V2OUT, "a") as fh:
                        fh.write(json.dumps(d) + "\n")
                    if d.get("m") is not None:
                        known[d["p"]] = d["m"]
                    if d.get("COUNTEREXAMPLE") or not d.get("forced_ok", True) or d.get("error"):
                        print("!!!", json.dumps(d), flush=True)
                    else:
                        print(d["p"], d["path"], d["m"], d.get("cpu", {}).get("TOTAL_cpu"), flush=True)
    print("done", flush=True)
