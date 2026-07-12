# experiments/gold — rescued research probes

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

Every archived file carries one status. Vocabulary (defined here once; the
`experiments/audit/README.md` and `experiments/excess/README.md` tables reuse it):

| status | meaning |
|---|---|
| `pinned` | a verified harness, or a result/value directly cited by a writeup (`writeups/goldarf.tex`, `writeups/excess.tex`) or treated as a reference value by `docs/PY.md` |
| `oracle` | a deliberate ogdoad-independent implementation kept around for cross-checking — not itself a citable result |
| `superseded-by:<file>` | kept for provenance only; do not cite its printed numbers — see `<file>` instead |
| `scratch` | exploratory research probe; triage before citing anything it prints |

Sources of truth, in priority order: each file's own module docstring (several
carry SUPERSEDED/oracle notes added in the 2026-07 sweep), `docs/PY.md` (the
audit ledger — its §1/§4/§5 genealogies), `writeups/goldarf.tex` filename
mentions (checked by grepping the escaped-underscore `\_` form the file actually
uses), and the git-visible rescue/move history. A trailing `?` marks a
best-effort read where the source was genuinely ambiguous, not a citation-grade
claim.

| file | status | purpose |
|---|---|---|
| `ao_orbitals.py` | pinned | AO(Q)-orbital coarsening (Lemma 1) + conjugation vacuity (Lemma 2), Obstruction arm; cited in `goldarf.tex` |
| `asym2_bench.py` | superseded-by:asym2_variants.py | m=4/m=8 bench on the base ECHO-ko rule; docstring self-declares superseded (abandoned for FIFO+ko1) |
| `asym2_bigscreen.py` | scratch | random big-board (k=7..9) screen of `asym2_fifo.abstract_value` |
| `asym2_degeneracy.py` | superseded-by:asym2_variants.py | decision-degeneracy analysis + miss dissection on the same abandoned base rule as `asym2_bench.py` |
| `asym2_dummy.py` | scratch | ECHO-FIFO + one dummy coin, the odd-k parity fix; precursor to the verified fifo+dummy realizer |
| `asym2_fifo_bench.py` | scratch | ECHO-FIFO real Gold-form bench via decomposition, validated directly on m=4 |
| `asym2_fifo.py` | scratch | FIFO+ko1 abstract k=5,6 linking-game screen + real Gold-form benches |
| `asym2_final.py` | scratch | k=9 full boards, m=16 spot checks, explicit position graph for the dummy game |
| `asym2_probe.py` | oracle | ECHO-ko CORRECT (sigma-in-key) solver; docstring self-declares its nim arithmetic a deliberate independent oracle (fuzz-verified per `docs/PY.md` §5) |
| `asym2_sweep.py` | scratch | capstone full-lambda sweep at m=8, a=1,2,3, all positions incl. full board |
| `asym2_variants.py` | scratch | screens alternation-discipline variants on the abstract linking game; the intended replacement thread for `asym2_bench.py`/`asym2_degeneracy.py` |
| `bent_check.py` | scratch | brute-force bent-Gold-component count over F_256 |
| `center_reading_probe.py` | scratch | exploratory sweep of center-reading translation rules on the extraspecial group E |
| `construct_round2.py` | pinned | round-2 T2-weierstrass Gold-quadric construct; `docs/PY.md` §1.1 treats its lam=10/lam16=138 values as the pinned reference `synth_verify.py` is checked against |
| `criterion_calibration.py` | scratch | Tier-2 naturality-criterion calibration (torsor-uniformity N1, locality N2, outcome-criticality N3) |
| `echo_charge_probe.py` | superseded-by:echo_window2.py+../echo_solver.py | ECHO-ko charge probe; sigma-key memo bug per `docs/PY.md` §1.2. goldarf.tex's "Corrected results" provenance names this family, but this rescued snapshot predates the memo-key fix — the table's numbers stand on `echo_solver.py` stage `ko2`'s independent re-derivation (both the docstring and the tex now say so) |
| `echo_frame_robust.py` | superseded-by:echo_window2.py+../echo_solver.py | frame-order robustness sweep; inherits `echo_charge_probe.py`'s sigma-key bug (imports its `make_form`) |
| `echo_nondegen.py` | scratch | decision-(non)degeneracy instrument for the corrected ECHO-ko game (imports the `asym2_probe` oracle solver) |
| `echo_window_probe.py` | superseded-by:echo_window2.py+../echo_solver.py | window-w ko variant of the echo-charge game; same inherited sigma-key bug |
| `echo_window2.py` | pinned | window-w ko ECHO with the CORRECT (sigma-in-key) solver; `docs/PY.md` §1.2 names it (with `../echo_solver.py`) as the fix the superseded trio above should point to |
| `extraspecial_adapted.py` | scratch | Arf-normal symplectic adapted-frame builder + miss prediction for m=8 Gold forms |
| `extraspecial_badpatterns.py` | scratch | inspect bad k=3 patterns for ko=self; ko=self vs ko=opp; B-adaptive kos |
| `extraspecial_core.py` | oracle | standalone nim arithmetic + Gold forms + correct ECHO-ko solver; declared cross-check oracle (`docs/PY.md` §0/§5), also cited in `goldarf.tex` §"extraspecial reframing" |
| `extraspecial_dbl.py` | scratch | double-touch ECHO variant (open+close as one move) |
| `extraspecial_k4char.py` | scratch | characterize the k=4 value function for ko=self |
| `extraspecial_k5.py` | scratch | k=5 value-depends-only-on-(B-graph,target) census |
| `extraspecial_m10.py` | scratch | scale check: synthetic rank-4 Arf-0/1 forms on F_2^10, full 1024-position sweep |
| `extraspecial_m4.py` | scratch | validate the solver against an independent no-memo tree solver, then sweep m=4 |
| `extraspecial_m8.py` | scratch | m=8 sweep with the correct solver + decision-nondegeneracy counts |
| `extraspecial_matching.py` | scratch | matching-pattern exactness + the reduced (p,s) scheduling game |
| `extraspecial_normal.py` | scratch | normal-frame sweep at m=8 for the four Gold forms, both orientations |
| `extraspecial_patterns.py` | scratch | pattern-level characterization of the ECHO game value; exhaustive k=3/k=4 enumeration |
| `gold_check.py` | scratch | brute-force Gold form rank/zero-count/Arf/radical-isotropy checks, m=4,8,16 |
| `gold_diag_probe.py` | pinned | Gold-diagonal source probe (top-coin trace, subfield vanishing, tower recursion, trace-dual lambda); cited in `goldarf.tex` |
| `nogo_synthesis_check.py` | scratch | verification of the two new components of the synthesized no-go theorem |
| `nogo_verify.py` | pinned | no-go verification bench (L1-L6: affine stabilizer, transvection criterion, orbitals, refinement torsor); cited in `goldarf.tex` alongside `skeptic_nogo_check.py` |
| `obstruction_extras.py` | scratch | kill-arm centralizer check, under-constrain-arm Frobenius check, Gold-radical isotropy check |
| `octal_attack.py` | oracle | self-contained octal/coin-turning attack probes; declares independence as its purpose, cited in `goldarf.tex` |
| `ogdoad_big_quotient_detail.py` | scratch | detail pass on order>=10 bounded misere quotients, backtracking `\|Aut\|` |
| `ogdoad_misere_subgroup_sweep.py` | scratch | bounded misere quotient sweep; `docs/PY.md` §1.6 flags it as ~120 lines reimplementing the bound `octal_misere_quotient`/`quadric_fit` API with no stated independent-oracle rationale — triage before reuse |
| `sandwich_m4.py` | scratch | equivariance-sandwich verification at m=4 (Sp(B) transitivity, O(Q) orbital lemma, maximality) |
| `skeptic_check.py` | scratch | independent skeptic verification of the T2 claim, random forms + Gold components |
| `skeptic_diag_check.py` | scratch | adversarial re-verification of the gold-diagonal attack, independent code |
| `skeptic_escape_edge_attack.py` | pinned | skeptic attack on N3 (pending-marker clock + escape edge); cited in `goldarf.tex` |
| `skeptic_indep.py` | superseded-by:../echo_solver.py | independent ECHO-ko solver written fresh from the prose; docstring self-declares it re-litigates a reading already superseded by fifo+dummy (kept for archival completeness only) |
| `skeptic_independent_check.py` | scratch | adversarial re-verification of load-bearing symmetry claims S1/S3/S4 + maximality |
| `skeptic_nogo_check.py` | pinned | independent re-verification of the no-go attack (both Arf classes, transvection retrograde check); cited repeatedly in `goldarf.tex` (Thm D/F/G) |
| `skeptic_octal_check.py` | scratch | independent adversarial verification of the anisotropic-normal-frame unwinding-game claims |
| `skeptic_round2_verify.py` | scratch | final-skeptic independent verification of the round-2 construct result |
| `skeptic_supplement.py` | scratch | verify the attack's corrected sweep numbers absent from the cited script |
| `skeptic2_independent.py` | scratch | independent skeptic verification of ECHO-FIFO+dummy, everything rebuilt from scratch |
| `synth_verify.py` | oracle | synthesis-round verification of the two load-bearing round-1 skeptic claims; declared independent nim arithmetic. The closed-form-lam assert flagged in `docs/PY.md` §1.1 is now present (fixed in the 2026-07 truth-repair wave) |
| `tier2_stratum_sweep.py` | scratch | exhaustive sweep of the minimal Tier-2 stratum over bent Gold components |
| `weil_gold_probe.py` | scratch | Weil/discriminant-form route verification probe, four falsifiable claims |
| `witness_test.py` | pinned | witness-reduction theorem test; cited in `goldarf.tex` ("and companions") |

Row count: 55 files, all present in `experiments/gold/`. Two files (`echo_window2.py`,
`construct_round2.py`) were marked `pinned` on `docs/PY.md`-level evidence rather than
a direct `writeups/goldarf.tex` filename citation — flagged as such above rather than
guessed at a stronger or weaker status.
