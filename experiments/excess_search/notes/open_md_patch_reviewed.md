# Patch for `docs/OPEN.md` section 2

Insert the subsection below between "The nim reciprocity route" and
"Evidence and authority". Then replace the "Evidence and authority" bullets
with the second block. Nothing else in section 2 changes. The open front
stays as it is: the universal `0/1/4` rule.

Before landing (for the lead; not part of the patch):

- `formal/Ogdoad/ExcessRandomModel.lean` must be tracked, imported (from
  `Ogdoad.lean` or `Papers.Excess`), and entered in `formal/README.md`.
  Until then, the Lean references below point at an untracked file.
- The engines, their logs, and the Peeters snapshot must be in the
  repository, or the engine bullet must be dropped. OPEN.md cites only
  material that the repository carries.
- The `excess.tex` section must land first, because this text points to it.

---

### Random model

This subsection is a heuristic. It is not evidence for or against the
conjecture, and it adds no new open front.

**The model.** Every odd prime is one row. A row fails exactly when its
Euler phase `rho_p = beta_p^((2^E-1)/p)` equals `1`, where
`beta_p = kappa_f(p) + rule(p)`. The rows group into cells
`Z_h, ZF_n, O_(r,a), C_k, D_k`, and each cell has one selected coordinate in
a cyclic group.
- The base model `M_0` takes these coordinates to be independent and
  uniform. A row then fails with probability exactly `1/p`, whatever
  `v_p(2^E-1)` is.
- The uniform cell model `M` conditions `M_0` on the proved constraints. The
  conditioning has positive probability and changes the `1/p` figures
  negligibly.
- The precise models (`M_0`, `M`, `M_Levy`, `M+`) are stated in `excess.tex`
  §`sec:model`, together with what each consequence needs.

**Inside the model.** These are theorems about a probability measure, not
about `On_2`.
- Almost surely infinitely many rows fail. Under the translate model `M+`,
  the excess is also almost surely bounded.
- Lean checks the infinitely-often half in
  `formal/Ogdoad/ExcessRandomModel.lean`, through
  `RandomModel.ae_infinite_fails` and
  `ae_cond_infinite_oddPrime_of_eq_inv`. The identification of the cell
  model's row events with that file's independent `1/p` events (a CRT step)
  is not formalized.
- The boundedness half is first Borel–Cantelli and is not formalized.
- Divergence of `sum 1/p` and search hit probabilities are properties of the
  model. They are not evidence that a counterexample exists.

**Against the data.** This is data together with the model.
- The observed rows all succeed: `1,020` when settled rows are dropped, and
  `1,033` when they are kept.
- Under `M` the probability of that is `0.37` and `0.32` respectively, a
  Bayes factor of about `3` for the rule.
- The real factor is lower. The rule was found by studying the rows below
  `709`, and the rows above `727` contribute a factor of only `1.32`.
- So the data test `M` only weakly. The model's small probabilities measure
  the model, not the tower.

**Predictions.** These are heuristic and conditional on `M` or `M+`.
- Arm `Z` is predicted to fail infinitely often, with counts growing like
  `lnln X`.
- If the extrapolated arm-`O` mass is finite, arm `O` is predicted to fail
  only finitely often, with `0.44` to `0.56` further failures expected.
- `C`, `D` and `ZF` are predicted to hold, with total expected failures
  about `1.4e-4`.
- The first unobserved failure has model median about `4e7`.
- Proved lower bounds for `m_p` at a failure:
  - `2` on `Z` rows with a two-power component, and in `O`;
  - `4` in `C`;
  - `16` in `D`.
- Under `M+`, a failure most likely gives `m_p = 1` on the other `Z` rows,
  `2` on two-power `Z` rows and in `O`, and `4` in `C`. In `D` it gives only
  `m_p >= 16`.

**Proved structure the model must respect** (`excess.tex` §`sec:model`).
- **Translate ties.** At every prime `p` not dividing `30`, the translates
  `zeta_k + c` share one power status for all `c` in `{1, 2, 3}`, and another
  for all `c` in `{4, ..., 15}`. Two consequences follow:
  - an arm `C` failure has `m_p >= 4`;
  - an arm `D` failure has `m_p >= 16`.
- **Two-power tie.** On `Z` rows with a two-power component, under a
  valuation hypothesis that holds on every such row up to `1e6`, a Frobenius
  power sends `kappa_h` to `kappa_h + 1`. So a failure there has `m_p >= 2`.
- **Cell success.** Every `O` cell whose prime-to-`r` order is squarefree
  contains a row with `m_p = 1`. That order is squarefree exactly when no
  base-2 Wieferich prime divides it. So if infinitely many `O` cells are
  Wieferich-free, the rule holds for infinitely many `p`. Whether they are is
  open.
- **Arm `C` without selection** (proved here; an independent check is
  pending). Take `K = Q(zeta_(3^(k+1)))^+`. Row `p` fails exactly when either
  of these holds:
  - the `psi_p`-component of `Cl(K) ⊗ Z_p` is nonzero;
  - `2 O_K` splits completely in `K(mu_p, (O_K^x)^(1/p))`.

  So the rule implies a restricted Weber-type class-number statement. An
  arm `D` analogue has been proposed but not checked.
- **Relations.** Multiplicative relations whose error terms have zero
  coordinate can never prove a success. They can prove a failure only by
  exhibiting an explicit certificate.
- **A control family** (outside the tower). Type-II Gaussian periods are
  biased toward cubes through a class-number channel.
  - At the inherited prime `3`, the cube frequency is `0.399` against `1/3`
    over `3377` conductors.
  - These figures come from the proved criterion, evaluated with uncertified
    PARI class numbers.
  - This shows how one channel moves natural elements. It is not a statement
    about row primes. Other proved structure, such as the tensor-proved `Z`
    levels, acts toward success.

**What would bear on the question.**
- An exact certificate `m_p != rule(p)` at some row would refute the rule.
- A structure theorem forcing the rule-value phase on rows of divergent
  `1/p`-mass would show the model misspecified there. It would not prove the
  rule.
- A calibration of non-row phases at fresh primes, counted per distinct
  selected element, would test the model's premise that no hidden structure
  exists.

### Evidence and authority

- **Data.** OEIS A380496 supplies the 126 values for `3 <= p <= 709`.
  Django Peeters' `transfinite-nim-calculator` (commit `9f7d67c`), the
  program that also produces the OEIS files, records `m_p` for `1,023` odd
  primes `p <= 12281`.
  - The record contains every odd prime up to `829` except `719`, and omits
    `444` of the primes in `(829, 12289)`.
  - Every record equals the rule.
  - These are a third party's computed values, not certificates.
- **Certificates.** Exact local certificates give `m_359 = m_719 = m_727 = 1`
  (`experiments/ordinary_*_certificate.py`, `experiments/certificates/`).
- **Engine recomputation.** The project's exact crossed-binomial and
  reference engines recomputed `411` rows in `(727, 8609]`, all equal to the
  rule.
  - `395` of them replicate Peeters' records.
  - `16` are new; all are in arm `O`, with `m_p = 1`.
- All of the above are finite data, not an induction.
- `experiments/ordinal_excess_probe.py` and
  `experiments/fermat_selected_screen.py` are bounded screens. Explicit
  countermodels in non-Conway fields refute overstrong lemmas only.
- Lean checks algebraic ingredients and named finite certificates, some
  through `native_decide`. `SelectedLogUnitTarget`,
  `ExceptionalColumnTarget`, and `DPrimeTarget` define open propositions
  without assuming them. See [`../formal/README.md`](../formal/README.md).
- `ExcessRandomModel` proves theorems about the probability model only.
  Nothing in it connects the model to `On_2`.
- **Heuristic figures.** Random-model numbers (expected failures,
  first-failure quantiles, value-set probabilities) are heuristic and
  conditional on the model. They are never evidence about the tower.
- The implementation boundary is `src/scalar/big/ordinal/tower.rs`.
- The authoritative account is
  [`../writeups/excess.tex`](../writeups/excess.tex).
