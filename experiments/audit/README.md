# experiments/audit — rescued research probes

Reproducibility scaffold for the parallel research run of 2026-06-10, rescued from
`/tmp` (where the fable fleet wrote them — ephemeral, not a citable substrate). The
2026-07 `docs/PY.md` sweep repointed the `/tmp` and absolute-path import fossils so
the archive runs from this checkout; per-file citation status now lives in the
STATUS TABLE below, not in prose.

- **gold** backs `writeups/goldarf.tex` (the Gold-quadric Tier-2 assault, consolidated
  into the draft note).
- **audit** holds the 2026-06-10 mathematical-correctness sweep (run logs; the archived AUDIT-ARCHIVE.md snapshot was retired in the 2026-06-12 docs reorg — see git history).
- **excess** backs `writeups/excess.tex` (transfinite nim excess; see also the
  committed `experiments/cyclotomic_3k_family.py`).

These are **research probes, not maintained or CI-tested code**. Most import
`ogdoad`, so install the debug wheel into the shared base Python first. They are
machine-generated; triage before citing any result.

## STATUS TABLE

Status vocabulary (`pinned` / `oracle` / `superseded-by:<file>` / `scratch`) and
its sourcing priority are defined once in `experiments/gold/README.md`; this
table reuses it unchanged.

No file in this directory is directly cited by path in `writeups/goldarf.tex` or
`writeups/excess.tex` (checked by grep, escaped-underscore form) — `audit/` is run
logs for the 2026-06-10 correctness sweep, not a writeup's evidence base, so
`pinned` does not appear below. Four files are declared independent-oracle ports
of specific Rust internals (per `docs/PY.md` §5's "Reimplementations of bound
API" list); everything else is triage-before-citing scratch.

| file | status | purpose |
|---|---|---|
| `arf_audit.py` | oracle | pure-Python nim arithmetic + Arf-invariant stack; docstring self-declares a deliberate independent port kept as a cross-check oracle |
| `dickson_audit.py` | scratch | Dickson-invariant homomorphism check for O+_4(2)/O-_4(2)/O(H) over F4, via brute-force orthogonal-group construction. The `mat_mul` landmine from `docs/PY.md` §1.4 is gone — already deleted (only the correct `mmul` remains) |
| `dyadic_check.py` | scratch | brute-force square-mod-2^k check vs `is_square_mod_two_power`, plus Qp/Zp arithmetic spot checks |
| `fp_emulate.py` | scratch | shared LDL/`fp_search`/`norm` helpers for the `fp_*` family; sibling-imported by `fp_full.py` (fixed in the 2026-07 sweep — was `exec(open('/tmp/...'))`, now a plain import with a `__main__` guard) |
| `fp_full.py` | scratch | `fp_search` exact-vector-count regression case at a fixed (K,a,b,c); imports `fp_emulate` |
| `fp_scan.py` | scratch | brute scan for float-vs-exact d2 mismatches over random (K,a,b,c) |
| `fp_scan2.py` | scratch | narrower targeted brute scan (4 variants, K up to 1.65e9) for the same float/exact d2 mismatch — a *different*, not superseding, search from `fp_scan.py` (see `docs/PY.md` §4) |
| `gauss_teich.py` | oracle | raw Teichmuller-lift reimplementation in Z_5 mod 5^6; `docs/PY.md` §5 names it as a declared independent reimplementation of the bound `.teichmuller()` |
| `genus_probe.py` | scratch | lattice-equivalence probe: is diag(1,20) ~ diag(5,4) over Z/64 |
| `hnf_check.py` | scratch | faithful port of `normalize_relation_rows`/`incremental_hnf` (`integer.rs`), fuzzed 3000x |
| `inv_sim.py` | scratch | Fraction-Laurent toy algebra: `inv_to_terms` vs `exact_inv_terms` random fuzz (part of the 4-file byte-identical toy-algebra cluster, `docs/PY.md` §5) |
| `loopy_audit.py` | scratch | loopy stopper-catalogue closure audit (over+over, under+under, star+dud sums) |
| `loopy_audit2.py` | scratch | independent retrograde W/L/D cross-check of `loopy_audit.py`'s claims; docstring self-declares a deliberately different algorithm from its sibling |
| `loopy_check.py` | scratch | loopy stopper identity spot-checks (over+under, on+off, star+star, etc.) |
| `loopy_check2.py` | scratch | up/star/down `>=` comparisons; `sum_game`/`left_survives_second` shared verbatim with `loopy_ge.py` (duplication noted in the file's own comment, not supersession — different comparisons are tested) |
| `loopy_ge.py` | scratch | over/under/star/on/off `>=` comparison table; shares the same helpers as `loopy_check2.py` |
| `root_sim2.py` | oracle | Fraction-Laurent series-root oracle with i128-overflow tracking; docstring self-declares it subsumes the retired `root_sim.py` |
| `root_sim3.py` | oracle | finer overflow detector than `root_sim2.py`'s, but only run for the sqrt case here — docstring notes the cbrt case is still covered only by `root_sim2.py`'s cruder detector (not a full supersession) |
| `snf_check.py` | scratch | faithful port of `smith_normal_form` (`integer.rs`), 4000 random matrices, chain + determinantal-divisor checks |
| `witt_check.py` | scratch | classical vs twisted Witt-vector addition law check over F_4 |

Row count: 20 files, all present in `experiments/audit/`. `root_sim.py` (the file
`root_sim2.py`'s docstring says it subsumes) is gone — deleted in the 2026-07
sweep, not merely superseded-in-place, so it has no row.
