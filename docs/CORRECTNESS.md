# CORRECTNESS.md (the verification-status ledger)

The verification-status ledger: which shipped claims are **machine-verified**, which
are **source-pinned**, and which are **asserted-but-unproven** — valued like
[`COMPLETENESS.md`](COMPLETENESS.md) — a game value `g` on a pillar blade `e_B` (`e_s`
scalar, `e_c` clifford, `e_f` forms, `e_i` integral, `e_g` games, `e_o` grundy, `e_y`
py). Claim level **interpretation/engineering**: each entry is a status call on the
existing verification surface, checked against the actual oracles, not vibes. Numbers
≈ focused days to close a verification gap; `±n` flags an a9 scope call; `↑` is worth
less than any number but strictly positive; `*n` is real, on-thesis, unscheduled.

The standing verification surface is the baseline this ledger reads against: `cargo
test` (the `proptest` suites `tests/scalar_axioms.rs` and `tests/clifford_axioms.rs` —
smoke-depth by default, `OGDOAD_PROPTEST_CASES=N` for real fuzzing — the
`associativity_*` oracles, and `general_product_reproduces_reduce_word_when_a_empty`),
the adversarial stdlib harnesses `experiments/echo_solver.py` and
`experiments/linking_game.py`, and the source-pinned finite tables inventoried in
[`TABLES.md`](TABLES.md). Its aesthetic sibling — structural/stylistic findings rather
than soundness — is [`CONSISTENCY.md`](CONSISTENCY.md).

---

## Status — audited 2026-07-02, PLAYED 2026-07-02 (same day)

The 2026-07-02 audit (baseline `30588ec`, sixteen adversarial math audits + seven
claim→oracle inventories; headline: **no mathematical error in any shipped computed
value — every error-grade finding was a wrong contract**) was played the same day in
four waves of sonnet agents plus lead fixups (`78a45bc..362ebed`), with an independent
codex review of the full diff returning PASS on every math-load-bearing area (one
comment-only transcription swap, fixed). Post-sweep baseline: **968 lib tests** (was
895), clippy clean both feature sets, cold rustdoc clean, `demo.py` green. The
archived play record is [`DONE.md`](DONE.md) → `revision-sweep-2026-07-02`; residuals
and standing switches below are what remains *of this ledger's scope*.

### Addendum — `under` separation theorem, 2026-07-20

The positive-dyadic Norton regrading is a proved result, not merely a bounded
pattern: for `u=m/2^k`, `a=u-2^-k` (or `u-1` for an integer), nonnumeric finite
thermographs satisfy `mean(G.u)=u mean(G)` and
`temp(G.u)=u temp(G)+a`, and numeric inputs land strictly below `a`.
The proof in `writeups/thermo_newton.tex` was adversarially reread; that pass
caught and removed the false shortcut “numeric differences remain numeric,”
supplied the load-bearing numeric-image lemma, and isolated the
temperature-zero no-premature-meeting argument.

The final separation is also proved, under an explicit full-dyadic,
lift-compatible coefficient contract.  First, `gr_0` retains the nonzero class
`[*]`; a homogeneous coefficient representing 2 sends it to the initial class
of `*+*=0`, while the full dyadic coefficient object also supplies the inverse
representing `1/2`, forcing a contradiction.  This covers ordinary
`ℤ[1/2]`-algebras and graded initial-form/Rees coefficients without falsely
claiming that a valued field embeds additively in its associated graded.  Second,
the numeric Norton degree maps have the exact nonnegative composition defect
`Δ(u,v)=v(1-δ_u)-δ_v+δ_(uv)`; `u=1/2`, `v=2` gives exact degree mismatch `1`, so
no temperature-preserving residue refinement makes them a multiplicative action.

Machine verification is supporting rather than a formal proof: exact Rust
checks cover the complete 22-value day-two census, a bounded day-three
singleton-option census, dedicated numeric images, quotient representatives,
matching Berlekamp overheating, and five materialized composition defects.  The
Python binding probe adds 210 thermic and 48 quotient/operator checks plus 2,304
positive-dyadic pairs for defect nonnegativity and the exact zero classification.
The surviving structure is a filtered abelian group with external transports,
not an internal full-dyadic graded ring; valuation-ring/integer-only or
characteristic-2 restricted structures remain outside the theorem's contract.

### Addendum — Lean proof-kernel boundary, 2026-08-09

`formal/` pins Lean 4 and mathlib and contains no `sorry`, `admit`, or custom
`axiom`.  `Ogdoad/Off.lean` kernel-checks the load-bearing `off` algebra:
Artin–Schreier surjectivity, explicit symplectic-plane hyperbolization with the
plane span preserved, and the zero-polar radical normal form `Q = ℓ²` with its
zero/codimension-one split.  It uses a set-sized algebraically closed
characteristic-two field as the finite-form proxy for full proper-class `On₂`;
the standard general symplectic decomposition remains an input interface rather
than a theorem reproved here.

`Ogdoad/BrownGame.lean` kernel-checks the `over` algebraic reduction and the
ambient value-level obstruction.  On every exponent-two additive source it
splits a Brown refinement canonically as `q = lift(ell) + 2Q`, proves
`ell = q mod 2` additive, proves the corrected polar
`B_Q = b + ell tensor ell` alternating/symmetric/biadditive, and proves the
converse and pointwise round trip.  Separately, two-divisibility kills every
exponent-two polar defect and then every exponent-four quadratic value.  The
finite `Z/8` cyclic extension is a kernel-checked sharpness witness: it carries
an odd Brown line only relative to a chosen section, so a bare `Z/4`-central
extension does not determine `q`.  Moews's classification supplies the
short-game divisibility used to instantiate the abstract theorem and remains
source-pinned rather than encoded as an axiom.  The same file kernel-checks the
starter-profile semantics of `{A_(Q+ell) | A_Q}`, its `N,R,P,L` outcome table,
and the fixed decoder to the Brown residue.  The shipped weighted-source
theorem supplies the follower contract; Lean does not duplicate that complete
arena construction here.

`Ogdoad/Fifo.lean` kernel-checks the exact reduced game semantics, strict
termination rank, queue invariant, strategy quantifiers, queue-cut conservation,
the edgeless base theorem, and the dummy-free conditioned close-first theorem.
The last result uses an absolute-target close-first strategy tree and a
whole-queue drain argument to prove that such an attacker cannot change parity
from any coherent ko-clear defender checkpoint with nonempty queue.
`FifoLinkingTheorem` is deliberately only a definition of the open proposition.
The exhaustive graph census through eight real coins remains machine evidence,
not a formal proof of the missing global affine-contraction lemma or of the
stronger prefix-safe STOP normalization.

`Ogdoad/Excess.lean` kernel-checks the exceptional-column reduction: coprime
order classes supply the four lower translates, the corrected sparse norm is
an identity in every characteristic-two commutative ring, and the
Euler-quotient test is an iff in finite cyclic groups and finite fields.  The
recorded `k=2,...,6` factor products and order-of-two residue screens reduce
inside Lean; primality is locally proved through `k=4`, while larger primality
claims retain their documented external provenance.  `DPrimeTarget` is only
the open universal `D'_k` proposition: no declaration assumes that the
distinguished `M_k` meets it.

The newer global saturation cores have the same ingredient-level boundary.
Lean checks the Fibonacci factorization, two-branch, and normalized-coboundary
algebra used by the `Z` semiconjugacy argument; the norm, translate, and torsion
phase transport used by the fixed-prime `C` tail; and the Kummer-quotient and
Hilbert coefficient identities used by the marked `D` phase bridge.  Their
selected finite-field specializations remain paper-level, and none of these
declarations asserts any of the four universal nonvanishings.

For the `Z` arm, the selected-prime transversality theorem is an all-level
paper proof with a small kernel-checked core.  Lean verifies the first-Witt
coefficient simplification and its nonvanishing from genuine quadratic birth.
The paper proves that every conjugate intersection above two is simple and
that their support has cardinality
`phi(F_n)/phi(delta_n)`.  Thus CSDU is exactly support cardinality one, not a
multiplicity assertion; the two-adic splitting, orbit count, and cyclotomic
norm identification are paper-level.  For `n>=2` it further proves the packet
gap `1` or at least `2^(n+2)` (the levels `n=0,1` are immediate).  For
`n>=3`, Lucas's divisor congruence, Gauss's cubic-residue criterion, and
elementary congruences sharpen this to `1` or at least
`kappa_n*2^(n+2)`, with `kappa_n=(7,5,6,3)` according to `n mod 4`; failure
then forces `phi(F_n)>=(kappa_n*2^(n+2))^2`.  The Fermat-divisor and cubic
reciprocity specialization is paper-level, while Lean checks the local
prime-power factors, abstract threshold, and square inequality.  The paper
also proves that this square-totient consequence is automatic for every
`n>=6`; Lean checks the odd-totient square bound and the full tail comparison.
Thus the sieve is a real packet gap, not a tail contradiction.  The paper also
identifies the selected nonunit as an
oriented simple primitive ray with trace-one first coefficient and a
nontrivial Kummer extension ramified at three.  Lean checks the ray coefficient
and conjugate-sum identity underlying
the trace calculation, the universal principal-two-unit congruence, and the
product identity underlying the shifted-unit norm.  Finite-field trace,
number-field norm, conjugation, local ramification, splitting, the
roots-of-unity product, and the finite-field specialization remain paper-level;
universal cardinality one remains open.

The literal-order and rational-dynamics refinements are also boundary
theorems, not CSDU.  Lean checks the quadratic trace/norm coordinates and the
one-step endpoint-orbit criterion.  It also checks the normalized torus-point
algebra, the denominator-free sum/ratio/product identities underlying its
finite-field coordinates, the inverse-pair fibre identity, and the
inverse-factor congruence core.  The Binet-to-torus displacement, finite-field
conjugacy and trace-block bijection, and Fourier specialization remain
paper-level. Lean
also checks the adjacent-exponent
modular signs, the two quotient-ring cofactor identities, and the short
modular-window and terminal divisibility cores used by the paper to
exclude both adjacent period classes.
The minimal-failure arithmetic and finite-field Fibonacci-period
specialization remain paper-level.  The paper iterates those coordinates to
show that recursive ancestry selects a Frobenius orbit while literal order only
selects its first representative.  Lean also checks the left-right Dickson
identity, the forward affine identity from the
elliptic model, and the coprime-cubing core for an `ell`-torsion phase.  The
finite-field ancestry specialization, smooth normalization, supersingularity,
critical portraits, projection degrees, and non-Lattès argument are
paper-level; none supplies the missing selected-order inequality.

The next global frontier cores sharpen that boundary without changing it.
Lean checks the `Z` first-additive-edge power coordinates, trace identity, and
factor-parameter obstruction, together with the exact cross-level gcd identity;
the associated exact-offset product, divisibility, and size inequalities;
the `C` birth-secant factorization, phase-weight
algebra, and coprime-primary projection; and the `D` sixth-root and
coprime-primary noncancellation used by the current-support cube.  The selected
finite-field ancestry, orbit-product, and support realizations are paper-level.
These are all-level reductions and route exclusions, not a proof of the
remaining selected nonvanishing assertions.

The global split-ray layer has the same strict division. Lean checks norm
descent through a degree-`(ell-1)` extension, the exact integer inequalities
used with the Amoroso--Dvornicich height theorem, rank--nullity for imposed
local splitting conditions, and the one-dimensional marked-evaluation core.
The paper supplies the cyclotomic heights, unramified-base hypotheses, local conductor calculations,
Kummer/Artin reciprocity, and character multiplicities. Together these prove
that the `O`, `C`, and `D` Kummer extensions are globally nontrivial and turn
hypothetical failure into complete splitting at the selected primes. They do
not prove the arms: the unprojected split-ray quotients have unavoidable
current-primary rank, leaving marked eigenspace/Frobenius nonvanishing.
For the cubic arm, the complete conjugate-lattice refinement is also split at
the proof boundary: Lean checks the multikummer rank accounting, while the
paper uses the circular-unit index theorem, local conductor calculation, and
Artin reciprocity.  Subject to the real class-number term, this identifies
failure with a jump from the unconditional `n-2` split character lines to all
`n-1` nontrivial lines.  Lean additionally checks the orbit-norm algebra which
isolates the last fixed line.  The paper-level semidirect-product and
Chebotarev calculation proves that replacement primes with the same base
Frobenius realize both final-line states; it does not evaluate the literal
prime two or prove that the jump is impossible there.
Lean also checks the decomposition-orbit covariance, the conjugation/eigenvalue
collision which forces a marked functional to vanish, and compatibility of a
nonzero marked coordinate with its unique Frobenius eigenvalue.  The paper's
cyclotomic unit-representation multiplicity and reflected-character
specializations remain paper-level.

The ordinary `p=359` row now has two deliberately separated verification
classes.  The checked-in 438,103-byte Hilbert-root artifact plus the maintained
python-flint full verifier form a locally replayable exact finite certificate:
the script checks the selected root equation, recomputes the degree-19,580
resultant norm, and verifies its nontrivial 359-phase.  The generic
root-to-factor deduction is proved in the paper, not Lean.  Separately, a
stdlib provenance checker verifies the hashes and endpoint records of two
complete historical runs of Peeters's pinned exact sparse calculator, both
ending with the same nonidentity support size.  Those external runs are
source-pinned corroboration, not part of the local certificate.

The ordinary row `p=719` is now also locally exact-computation-backed.  The
paper first reduces it to a degree-179 factor of
`(T^359+1)^179+(kappa_89+1)` over `F_(2^7029220)`, then uses a crossed tower
to compress the certificate to two 438,103-byte payloads over `F_(2^179)`
and two 8,033-byte checkpoints in `F_(2^64261)`.  The maintained
python-flint verifier reconstructs the certified `p=359` root and phase,
checks `a^359=(1+x)/c`, verifies the stored monic degree-19,580 polynomial at
`a` in authoritative full mode, recomputes
`W=v^19580*f_a(v^(-1))`, and obtains a nonidentity 719-torsion Euler phase.
Together with the paper's crossed-tower deduction this proves `m_719=1`.
The payload computation is not a Lean theorem: Lean checks only the generic
scaled-product identity and conditional exponent multiplication, while the
field, Kummer, norm, and numerical specializations remain paper-level.

The next ordinary singleton row `p=727` is independently locally certified by
`experiments/ordinary_727_certificate.py`.  The stdlib checker constructs the
literal five-term degree-2420 polynomial `P_alpha_11(X^121)`, proves it
irreducible by the complete Rabin checks, verifies that `kappa_121` itself is a
727-th power, and obtains a nonidentity 727-torsion Euler phase for
`kappa_121+1`.  This proves `m_727=1`.  Lean checks the prime, order, and degree
arithmetic; the binary finite-field evaluation remains exact computation rather
than a kernel theorem.  This is the deliberate endpoint of finite-row
certification; the next unsupported carry is retained only as a runtime
guardrail while the open mathematical target is uniform.

`Ogdoad/GameExterior.lean` kernel-checks the algebraic core of the resolved
`tisn` theorem.  From explicit roots `ny=t`, `nz=x` and the torsion relation
`nt=0`, it proves in an arbitrary associative ring that an additive grade-one
map satisfies `i(t)^2=0` and has zero polar anticommutator with `i(x)`; an
injective coefficient map then gives `Q(t)=B(t,x)=0`.  It also derives
polarization from the Clifford relations and proves `Q(x+t)=Q(x)`.  Moews's external
classification of the short-game group supplies the power-of-two roots and
power-of-two torsion used to instantiate that theorem.  The game classification
is source-pinned prose, not a Lean axiom or executable model of short games.

## What holds (the baseline — don't dilute it on any cleanup pass)

- **The cross-validation spine is real, and this sweep widened it.** `verify_milgram`
  checks three independent routes to `signature mod 8`; `nikulin_genus_iff…` pins two
  independently implemented algorithms against each other — and the Nikulin machinery
  now also has both *negative* obstruction branches forced plus a positive
  `is_isomorphic` DFS witness on differently-presented forms; the Clifford engine is
  pinned to the brute-force `reduce_word` oracle on all three product paths, with the
  even-subalgebra, dim-4 polar-rank, bialgebra-compatibility, direct-sum-shift, and
  versor-inverse-`None` gaps now closed; the ordinal tower's generator path is
  cross-checked exhaustively against the `φ_{ω+1}`-polynomial path;
  `LocalQp`/`Qq`/`WittVec` each have an element-for-element cross-backend oracle, and
  the whole p-adic wing now carries the `assert_supported_params` +
  `invalid_parameters_are_rejected` discipline.
- **Reciprocity is the gold oracle at every leg**: brute-forced `∏(a,b)_v = +1` over ℚ,
  the multiplicative sweep over `F_5(t)`, the additive XOR sweep over `F_2(t)`/`F_4(t)`,
  and the full-strength `n ∈ {2..5}` constant-extension sums over `F_q(t)`.
- **Source pins**: A380496 is now diffed **in full** (all 126 rows) against a vendored
  b-file copy (`src/scalar/big/ordinal/b380496.txt`, fetched 2026-07-02);
  `LEECH_AUT_ORDER` and the ADE data are recomputed; the BW16 group orders now
  **derive in-repo** from Grove's `|O⁺(2m,q)|` closed form instead of being
  hand-entered; the 2-adic canonical-symbol Sage examples in `genus.rs` remain the one
  executed Sage oracle.
- **The games wing is honestly two-implementation tested where it claims to be**,
  now including a day-≤2 exhaustive canonical-form sweep recovering the known
  22-value census (day 3 bounded, labeled as such), a two-way Norton oracle, and a
  branched hackenbush ordinal-sum witness. `thermograph_via_tropical` remains a
  naming bridge over the shared recursion — not an independent cooling
  implementation; don't cite it as a cross-check.
- **"source-pinned" is now a reserved term** (external data pin, à la A380496). The
  Aravire–Jacob expected values are labeled "paper-derived worked examples" — weaker,
  and now worded as such at every site.

---

## Played 2026-07-02 — the audit items, with residuals

Every numbered item of the 2026-07-02 audit was played; full per-item detail is in
the four `Play wave …` commit messages and `DONE.md`. What each left behind:

- `spinor-norm-char2-claim` (½·e_c): the three doc sites reworded (raw norm only; the
  char-2 ℘-reduction is *not* the invariant), Nimber-backed `spinor_norm`/
  `classify_versor` pin added. **Residual**: the honest additive Wall/Dye invariant
  stays a buildable — [`COMPLETENESS.md`](COMPLETENESS.md) → `char2-spinor-norm`.
- `modular-overflow` (½·e_i): `sigma_power` overflow now a deterministic documented
  panic (`n = 2989` boundary at power 11, pinned both sides); `B_1 = +1/2` convention
  stated and pinned. The documented-cap route was chosen over `Option` to keep the
  public Eisenstein surface infallible.
- `p-adic-guard-gap` (½·e_s): WittVec/Qq/Ramified guarded + rejection-tested; Qq (and
  Qp, found during play) valuation arithmetic checked; `adele_prec`'s cap verified
  against `LocalQp::check`'s real bound and **widened** (~2^64 → ~2^127).
- `nullspace-skip` (½·(e_s∧e_c)): column-skip elimination with the load-bearing
  full-width sweep (a skipped column must keep being updated by later pivots — caught
  during play, membership-tested); `solve`/`inverse_matrix` local round-trips added.
- `alpha-row-pins` (1·e_s): integer table now full-diffed against the vendored
  b-file; ordinal reconstruction value-pinned at 16 rows (`{3..47} ∪ {73, 89}`).
  **Residual**: rows `97..709` still have no ordinal-value oracle, and the plan to
  lift `u = 179` FAILED for a real reason — `alpha_ordinal(179)` hits a compute cliff
  (Frobenius minimization over `χ(89)`'s subfield degree, 3+ min unterminated), so
  the "too costly" boundary bites at 179, far below 709. Documented in
  [`OPEN.md`](OPEN.md); any future pin of large rows needs an algorithmic idea, not
  patience.
- `bw-ff-sweep` (1·e_f): all-eight-residue sweep ported; genuinely independent
  Clifford-side oracles exist only at residues 2–3 (same boundary as the rational
  leg — Lam's table is itself the source for the other arms; the test says so).
- `rank16-pins` (1·e_i): BW16 orders derived from the `|O⁺(8,2)|` closed form; the
  Kneser reports now assert the **generated** labels equal the static catalogue
  (previously the generated set was silently discarded); the `D16_PLUS_AUT_ORDER`
  tautology is labeled as transcription-only, pointing at the Siegel–Weil pin.
- `nikulin-negative-witnesses` (½·e_i): both obstruction variants forced (27/8 at
  p=3, 16/3 at p=2 — each hand-derived and re-derived through an exact-fraction
  port), positive DFS on differently-presented `A_1⊕A_1` Grams, fqm cases for a
  noncyclic anisotropic core / an exponent-8 block (impossible-by-lemma: `q(4x)=0`
  forces order-4 Witt cancellation) / D_4 cross-checked against `brown_invariant`.
  **Residual**: coverage is witness-grade now, not exhaustive-grade; a
  Kawauchi–Kojima-cited row was deliberately not pinned (citation uncertainty —
  derive-twice used instead).
- `char2-decomp-coverage` (½·e_f): all three closed; the equal-degree-splitter input
  was *verified to fire the trace-splitter branch* (traced: split at seed 24, before
  any early-gcd coincidence) — the audit's "one product closes it" was optimistic
  about branch selection, recorded here so the next test author checks the branch.
- `arf-vs-constant-bias` (½·(e_g∧e_f)): `QuadricFit::bias() = arf XOR constant`
  shipped with the exhaustive k ≤ 4 both-polarities pin; examples routed through it;
  the loopy Draw-branch now constructed and tested.
- `clifford-test-gaps` (½·e_c): all five closed, no production bug found.
- `partizan-oracle-breadth` (½·e_g): played at the honest scope — day ≤ 2 exhaustive
  (22-value census), day 3 bounded-not-census (the 1,474-value day-3 universe is
  future work if ever wanted); Norton oracle is a second transcription, not a
  citation (none was certain enough to pin).
- `one-line-pins` + `proptest-depth-note` (↑): all bullets played.

## switches — closed

### ±1·e_f: `aj-second-engine` — CLOSED 2026-07-02 (accepted)
a9's call: **accept paper-derived worked examples as the documented boundary** — no
second engine. The decision is recorded at the source
(`springer/char2/mod.rs` module doc, "Oracle boundary (accepted, 2026-07-02)"): the
odd-residue engine rejects residue char 2 by structure, the hand-worked
Aravire–Jacob oracles are the contract, and a test-only brute-force verifier stays
welcome-if-ever-wanted rather than owed. "source-pinned" remains reserved for
external data pins.

### recorded boundaries (not gaps, decisions)
- `weight_enumerator` (both code types) keeps an infallible signature with a
  documented budget-referencing panic (`CODEWORD_ENUMERATION_BUDGET`); full
  `Option`-ification is a 3-caller follow-up (py, lexicode, theta) if ever wanted.
- The next audit of this kind should read `grundy/src/` and `src/py/` — both were out
  of scope for the 2026-07-02 pass (see [`CONTINUATIONS.md`](CONTINUATIONS.md) →
  `ogham-reflect` part (3)).
