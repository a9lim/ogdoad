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

Later the same day the flagship absorbed three further closures — observation
width above weight one (`cor:blocks`), the impartial uniform realizer (the
rewritten pass-free realization), and the game-native Gold--Heisenberg model
(`thm:goldheisenberg`) — and took its final author block
(`gpt-5.6-sol`, `claude-fable-5`, `a9lim`). [`CLOSED.md`](CLOSED.md) now
indexes nine results, seven flagship-homed. The paper has no remaining
mathematical debt; everything below is verification polish, print checks, and
submission mechanics.

Current state:

| paper | state | destination |
|---|---|---|
| `goldarf.tex` (flagship) | publication rewrite + the three same-day closure folds and harmonization pass done 2026-08-12, compiles clean | INTEGERS, games section |
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

- **goldarf**: publication rewrite landed 2026-08-12 (verified by a fresh
  codex sol consult; zero content loss found, two findings in the one
  newly written proof paragraph, both fixed): theorem-first reorder
  (contract §4 → construction §5 → boundary §6 → Gold--Arf §7 → Brown §8 →
  obstruction landscape §9), repo paths routed through a companion-repository
  citation, INTEGERS house format applied (references before appendix,
  `\footnotesize` alphabetical bibliography, Equation-prose refs,
  MSC/keywords, tightened abstract). `thm:nolivemiddle` now states
  normal-play $P$ / misère $P$ / loopy Loss (the unproved Draw claim was
  dropped, matching its own scope remark) with a corrected proof paragraph.
  Remaining: a9 read-through — now covering the 2026-08-12 late folds too
  (pass-free realization section, `cor:blocks`, the Gold--Heisenberg
  subsection, retitled §9, the new author block); cover letter; pin the
  `\cite{ogdoad}` entry to an exact tag/commit; arXiv posting.
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

The flagship's `sec:status` names two formalization boundaries; closing both
would delete "no single end-to-end Lean theorem constructs the complete
arena" from the paper. Sizing estimated 2026-08-12 against the shipped
modules (`ImpartialRealizer.lean` 539 lines, `GoldExtraspecial.lean` 253):

- **End-to-end arena** (≈3--4 sessions, ~800--1100 lines, three separable
  chunks; supersedes the old `FifoMatching.lean` per-close-zero item, which
  the impartial rewrite absorbed):
  1. *single-policy reification* (~1 session): make the safe-front policy a
     `State → Move` function of the full potential matching and re-run the
     existing `forcesScore` induction with the scoring submatching varying;
     key lemma is matching-degree monotonicity (clean in the full matching ⇒
     clean in every submatching);
  2. *weighted charges* (~1 session, mechanical): generalize the uniform
     edge score to `w : E → ZMod 2` plus close-charges `p_i`; the
     overlap-charge structure survives;
  3. *Witt basis, loading, root theorem* (~1--2 sessions, the long pole):
     deterministic symplectic-plus-radical basis over `F_2` (likely
     hand-rolled — see the mathlib-PR overlap below), coefficient transport
     `y = C⁻¹x`, glue to `GoldMatchingAlgebra`, state `root P ↔ Q(x) = 0`.
- **`GoldExtraspecial.lean` nimber-trace specialization** (≈1 session,
  ~300--400 lines): instantiate the universal cocycle group at
  `φ_a = Tr(λ·x·y^(2^a))`; `Excess.lean` and `GoldDiagonal.lean` already
  drive mathlib's `Algebra.trace` over finite fields, including the
  even-degree-vanishing shape the radical quotient needs. Friction points:
  Frobenius-power fixed-field API, and the `Q_8` identification (match
  `QuaternionGroup` or state "nonabelian order 8, unique involution").
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
Note the overlap: the end-to-end arena's chunk 3 above needs the same
symplectic-basis construction over `F_2` — build it once, mathlib-shaped,
and it serves both consumers.

## Loose ends

- Solé--Tokareva (IACR ePrint 2009/544) is cited in the flagship but has no
  local PDF: the ePrint endpoint sits behind a Cloudflare bot wall. Manual grab
  into `ref/` if a local copy is ever wanted.
- `ref/` is local and gitignored; `ref/README.md` records sources and the
  verification receipts (both arXiv IDs confirmed against PDFs; Moews pages
  49--57), so the library is refetchable on any machine.
