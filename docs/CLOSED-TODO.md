# CLOSED-TODO: remaining work on the closed-problem papers

The 2026-08-12 six-referee review (one independent referee per
[`CLOSED.md`](CLOSED.md) paper: full proof-chain verification, statement-level
Lean cross-checks, literature search, several from-scratch re-implementations)
found **all six papers mathematically sound — zero false theorems** — and its
findings were implemented the same day: four papers merged into the flagship
`writeups/goldarf.tex`, `thermo_newton.tex` restructured around the Norton
thermic law, `transfinite_arf.tex` promoted to perfect Artin--Schreier-surjective
characteristic-2 fields. Every referee-supplied formula was independently
re-derived before printing; none failed. The full findings text lives in the
review digest a9 holds (`publishability-review-2026-08-12.md`) and the
`flagship-merge-2026-08-12` entry in [`DONE.md`](DONE.md); this file now tracks
only what remains.

Current state:

| paper | state | destination |
|---|---|---|
| `goldarf.tex` (flagship) | revised, merged, compiles clean | INTEGERS, games section |
| `thermo_newton.tex` | restructured theorem-first | INTEGERS (or TCS), **gated on the novelty check below** |
| `transfinite_arf.tex` | revised | stays internal; the mathlib PR is the outlet |

(Venue note from the review, still current: IJGT is economic game theory — a
poor CGT fit; INTEGERS' games section is the natural home for both submissions.)

## a9's print-only checks

- **Winning Ways ch. 8 and Siegel §III.3** (both print-only): confirm the
  Norton thermic law `temp(G.u) = u·temp(G) + (u−δ_u)` is absent before
  `thermo_newton.tex` ships its "not found in the literature" novelty claim.
  This is the one gate blocking the thermo submission.
- **Siegel GSM 146**: pull the exact theorem number for the Moews
  structure-theorem presentation cited in the flagship's game-exterior appendix.

## Submission prep

- **goldarf**: a9 read-through of the merged paper (the structure changed
  substantially: retitled, diagonal-source section absorbed, Brown-selector
  section + game-exterior appendix spliced in); then cover letter, final
  formatting pass, arXiv posting.
- **thermo**: after the novelty gate clears — bounded re-run of the deeper
  stress harness for citable counts (the original second run died to a laptop
  OOM, not a failure). Standing verified counts, quotable now: 3,360 regrade
  checks (336-game day-≤3 catalogue × 10 units) and 112,896 max-inequality
  sums, zero failures; `experiments/under_descent.py` re-passed 2026-08-12
  (210/210 thermic + 24+24 descent + 2,304 defect pairs).
- **flagship verification counts**, quotable in a cover letter: referee
  re-implemented the Rule box from the printed text alone and minimax-solved
  160 instances with zero mismatches; 7,410 Brown forms machine-checked; the
  diagonal-source recursion/descent/solver verified against an independent nim
  tower through `m = 64`.

## Lean follow-ups (valuable, deliberately unscheduled)

- `FifoMatching.lean`: promote the per-close-zero strengthening (carry "every
  close so far had zero flip" through the existing induction). This is the
  **sole load-bearing non-kernel-checked step** in the flagship's exactness
  chain, and the paper now flags it explicitly as the next Lean follow-up.
- `BrownGame.lean`: the selector's game step is *defined*, not proved (no
  `PGame`). A half-page mathlib `PGame` upgrade (`Bq := PGame.mk` with the two
  followers; derive the outcome from `G ≈ 0` / `G ‖ 0`) would make the
  `formal/README.md` selector wording literally true; soften that wording
  meanwhile. (README is being actively edited by the live FIFO codexes — do
  this when `formal/` is quiet.)
- `GameExterior.lean`: add the sharpened `⋂ₖ4ᵏR` theorem (~5 lines given
  `polarization`) — the flagship appendix currently notes it as paper-level —
  and drop the superfluous `hrootT` hypothesis from
  `torsion_anticommutator_eq_zero`.
- `formal/README.md`: note that the transfinite classification theorem itself
  is not stated in Lean (the `Off.lean` docstring was already narrowed to its
  actual pointwise statement, 2026-08-12). Same quiet-window caveat as above.

## The mathlib PR (transfinite outlet)

`Mathlib/LinearAlgebra/QuadraticForm/AlgClosed.lean` has an in-file TODO asking
for exactly the quadratically-closed characteristic-2 generalization the
revised `transfinite_arf.tex` now states; `Off.lean` is ~70% of the needed
material. The missing prerequisite is **symplectic-basis existence for a
nondegenerate alternating form** — absent from mathlib and independently
valuable. Unscheduled; the biggest single deliverable left in this thread.

## Loose ends

- Solé--Tokareva (IACR ePrint 2009/544) is cited in the flagship but has no
  local PDF: the ePrint endpoint sits behind a Cloudflare bot wall. Manual grab
  into `ref/` if a local copy is ever wanted.
- `ref/` is local and gitignored; `ref/README.md` records sources and the
  verification receipts (both arXiv IDs confirmed against PDFs; Moews pages
  49--57), so the library is refetchable on any machine.
