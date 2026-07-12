# experiments/excess — rescued research probes

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

| file | status | purpose |
|---|---|---|
| `cyclo_family.py` | superseded-by:../cyclotomic_3k_family.py | cyclotomic-model `ord(kappa_{3^k}+1) = 3^{k+1}(2^{3^k}-1)` verification; the committed top-level `cyclotomic_3k_family.py` carries this thread forward (per `docs/PY.md` §4 genealogy) |
| `cyclo_family2.py` | superseded-by:../cyclotomic_3k_family.py | extends `cyclo_family.py` to levels 5-6 via factordb factorizations; docstring self-declares "`cyclotomic_3k_family.py` at experiments/ top level supersedes this thread through k=8" |
| `step1_term_checks.py` | scratch | k=1.. term-algebra order checks for kappa_{3^k}+c identities (imports the top-level `ordinal_excess_probe.TermAlgebra`); misfiled under `experiments/gold/` originally, moved here in the 2026-07 sweep per `docs/PY.md` §4 — not itself cited by path in `writeups/excess.tex` |

Row count: 3 files, all present in `experiments/excess/`. `cyclo_family.py`'s
own module docstring does not self-declare superseded (only `cyclo_family2.py`'s
does); its status here follows the seeded genealogy in `docs/PY.md` §4 plus the
fact that `cyclo_family2.py` imports directly from it — the two files share one
fate.
