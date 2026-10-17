# Open mathematical problems

Ogdoad has three live research problems:

1. **isolated-dummy FIFO linking**, a universal conjecture about a parity
   game on graphs;
2. **the `0/1/4` rule for finite excess** in transfinite nim multiplication,
   a universal arithmetic conjecture;
3. **natural realization of finite misère quotients**, a classification
   program for octal rulesets together with the exact quotient of misère
   Grundy's game.

Each section gives the statement, why it matters, what is proved, the exact
missing step, and the evidence with its authority. The linked papers carry
the arguments. Finite censuses, certificates, and implemented APIs are
evidence or infrastructure; none substitutes for the stated theorem.
Engineering that serves these problems is tracked in
[`ROADMAP.md`](ROADMAP.md).

## 1. Isolated-dummy FIFO linking

Let `G` be a finite simple graph on real vertices `R`, and adjoin one
isolated dummy `d`. A state holds the untouched set `U`, a FIFO queue `Q` of
open vertices, a ko bit, the player to move, and a score in `F_2`. The moves
are:

- `OPEN(x)` for `x` in `U`: remove `x` from `U` and append it to `Q`; set ko
  exactly when `Q` was empty;
- `CLOSE`, when `Q` is nonempty and ko is clear: remove the front `f` of `Q`
  and add `deg_G(f, U) mod 2` to the score;
- a forced pass, which clears ko, when neither is legal.

Every move changes the player to move, and play stops when `U` and `Q` are
both empty. A designated defender seeks terminal score zero.

**Conjecture.** For every finite simple graph, the defender can force
terminal score zero from the empty-queue, score-zero root, whichever seat is
designated defender.

**Why it matters.** The game is graph-independent: the graph only evaluates
the schedule. For a complete history `h`, FIFO order makes the activity
intervals pairwise non-nesting, and the score is `<A_G, D(h)>`, where `A_G`
is the adjacency vector and `D(h)` records the disjoint interval pairs in the
binary edge space. The conjecture is therefore a statement that one isolated
tempo vertex neutralizes every linear functional on a universal schedule
invariant. The Gold--Arf realization needs only matching-plus-isolates
boards, which are proved; it does not depend on this conjecture.

### What is proved

- **Affine duality.** For a fixed attacker strategy `S` with terminal
  histories `H_S`, `S` is harmless on every graph exactly when `0` lies in
  `Aff{D(h) : h in H_S}`. A score-erased public-policy formulation is
  equivalent to the conjecture (`FifoPublicPolicyDuality`), so the problem is
  graph-free.
- **Solved regimes.** Matching-plus-isolates boards are won by either seat;
  boards partitioned into two-element cells with an even number of edges
  between any two cells are won by the second player; close-first attackers
  are excluded on every graph.
- **Separator normal form.** In a separated public policy, a rank-minimal
  sheet-one occurrence with the dummy live selects a real `OPEN(v)` of
  separator increment one into a complete sheet-zero defender fan, and the
  old queue is nonempty and carries one unit of separator debt.
- **Strategy-relative normal form.** A minimal score-zero failure inside one
  odd strategy has one of two predecessors: a unit-charged close followed by
  a score-neutral suffix (the charged-close spike), or an open onto an empty
  queue (the protected singleton).

### Missing step

The paper isolates one sufficient statement, the **causal factor
extension**: for every separated initial public policy, the charged-close or
protected-singleton frontier admits an odd family of occurrences whose
decorated prefixes and continuation directions cancel, using descendant
continuation directions together with strictly earlier defender siblings.
It implies the conjecture. Equivalently, at the selected minimal-bad
occurrence `h`, the decorated point `b_h` must lie in the span `M_h` of
frontier continuation spaces and even sums of off-spine decorated points.

The queued debt vertex may survive behind the last charged front or open
inside the neutral suffix, and ko legality and score parity identify it with
the charging neighbor in neither order. Exact models show that canonical
positional strategies, unlabelled state-DAG cycles, dummy deletion, immediate
fan completeness, and unrestricted pair descent each lose the information the
extension needs, and that no bounded number of terminal vectors witnesses
every required affine zero. A proof must select siblings through the
occurrence's actual ancestry.

### Evidence and authority

- Lean defines `FifoLinkingTheorem` and proves the public-policy duality, the
  matching-plus-isolates and close-first regimes, and both normal forms; it
  neither assumes nor proves the conjecture.
- Exact minimax shows every nonisomorphic graph through eight real vertices,
  plus the dummy, is defender-won for both seats. This is a finite census.
- The executable oracle is `experiments/linking_game.py`.
- The authoritative account is
  [`../writeups/linking_affine.tex`](../writeups/linking_affine.tex).

## 2. The `0/1/4` rule for finite excess

Conway's nim operations make the ordinals a field of characteristic two, and
its first transfinite layers are Kummer extensions. For an odd prime `p` with
`f(p) = ord_p(2)`, Lenstra's construction writes the Kummer radicand as

```text
alpha_p = kappa_f(p) + m_p
```

with a finite *excess* `m_p` in `N`. Let `Q(h)` be Lenstra's component set
for `kappa_h`.

**Conjecture.**

```text
m_p = 0   if Q(f(p)) is not a singleton odd prime power,
m_p = 4   if f(p) = 2 * 3^k for some k >= 1,
m_p = 1   otherwise.
```

Lenstra asked the weaker question whether `m_p` is bounded at all; that
question is also open. With `C_a` the nimbers below `2^(2^a)`,
`m_p < 2^(2^a)` exactly when some `c` in `C_a` makes `kappa_f(p) + c` a
non-`p`-th power in the compositum `F_2(kappa_f(p)) C_a`, so boundedness is
the existence of one finite affine line that works for every prime.

**Why it matters.** `Ordinal` arithmetic is exact only inside a window built
from these rows: OEIS A380496 supplies `3 <= p <= 709`, certificates supply
`m_719 = m_727 = 1`, and checked multiplication refuses at `m_733`. A proof
would replace the table by a formula. The problem is also a clean instance of
*selected-point arithmetic*: every reduction ends at a single element chosen
by the literal Conway tower, and no statement about generic elements of the
same field decides it.

### Four-arm reduction

Notation follows `excess.tex`. For `h > 1`, `Pi_h` is the full primary part
of `2^h - 1` at primes first occurring at residue degree `h`, and `T_h` is the
norm of `kappa_h` to `F_(2^h)`. For an odd prime `r` and `a >= 1`,
`b_r = d(alpha_r)`,
`y_(r,a) = kappa_(r^a) + 1` in `F_(r,a) = F_(2^(r^a b_r))`, and
`L_(r,a) = Phi_(r^a)(2^(b_r))` is the order of
`F_(r,a)^x / F_(r,a-1)^x`. For `k >= 1`, `zeta_k = kappa_(3^k)`,
`gamma_k = zeta_k + zeta_k^(-1)`, and `M_k = A_k^(q-1)` with
`q = 2^(3^k)`, `omega = zeta_k^(3^k)` in `F_4`, and
`A_k = zeta_k^2 + zeta_k + omega`; finally `Psi_k = Phi_(2*3^k)(2)/3`.

The conjecture is equivalent to the conjunction of:

| arm | case | assertion |
| --- | --- | --- |
| `Z` | `Q(h)` not a singleton odd prime power | `Pi_h` divides `ord(T_h)` |
| `O` | singleton `r^a`, `r != 3` | every prime `p != r` dividing `L_(r,a)` has full valuation in `ord(y_(r,a) F_(r,a-1)^x)` |
| `C` | `h = 3^k` | `gamma_k` is primitive in `F_(2^(3^k))^x` |
| `D` | `h = 2 * 3^k` | `Psi_k` divides `ord(M_k)` |

Every arm is an exact Euler test on one selected coordinate: for nonzero
`beta` in `F_(2^E)` and a prime `p` dividing `2^E - 1`, `beta` has no `p`-th
root exactly when `beta^((2^E - 1)/p) != 1`. The weaker `p | ord(beta)` loses the full primary
valuation when `p^2` divides the ambient order.

### What is proved

**Arm `Z`.** The support criterion identifies `m_p = 0` with the primary
factor of `Z`. On the singleton-even Conway--Fermat chain
`c_n = 2^(2^n)`, `c_n^2 + c_n = c_0 ... c_(n-1)`, the arm is exactly
`delta_n = F_n`, where `delta_n` is the order of `c_n` in
`F_(2^(2^(n+1)))^x / F_(2^(2^n))^x`; all compatible root choices form one
Frobenius orbit, so the question is intrinsic. The packet degree gives
`phi(delta_n) >= 2^(n+2)` for `n >= 2`, so a prime `p | F_n` missing at full
valuation has `p <= 1 + 2^(2^n - n - 2)`. At a least counterexample every
prime factor of `F_n / delta_n` is at least `p` and `1 mod 2^(n+2)`, and below
explicit thresholds the cofactor is `p` or divisible by `p^2` (a repeated
Fermat-factor boundary). The selected element lives on the supersingular
curve `y^2 + y = x^3 + x^2`; the all-iterate Artin--Schreier ramification,
the generalized-Prym saturation, and the top-orbit `S`-unit reduction (to the
two function values `g(P_n)` and `Theta_n`, in a one-dimensional Kummer
quotient) are proved boundaries, not detectors. Two-block tensor arguments
prove the multicomponent arm at `h = 12, 15, 24, 36, 40`.

The Fermat chain has an elementary reformulation that is not yet in the
paper. With `q = 2^(2^n)`, Frobenius over `F_q` sends `c_n` to `c_n + 1`, so
`z -> z^(q-1)` identifies the quotient with the norm-one torus of order
`F_n` and sends `c_n` to

```text
w_n = 1 + c_n^(-1),        w_n + w_n^(-1) = (c_0 c_1 ... c_(n-1))^(-1).
```

Thus `ord(w_n) = delta_n`, and the arm asks whether `w_n` generates that
torus. Wiedemann's conjecture asks the same of `x_n` in the tower
`x_0 + x_0^(-1) = 1`, `x_n + x_n^(-1) = x_(n-1)` (D. Wiedemann, *Fibonacci
Quart.* 26(4), 1988), and is also open. The two elements are
Frobenius-conjugate for `n <= 2` and for no `n >= 3`: with
`a_m = c_0 ... c_m`, the relative trace satisfies
`Tr(a_m^(-1)) = a_(m-1)^(-2)`, so conjugacy would descend to level two, where
`a_2^(-1)` and `x_2` have different minimal polynomials. The towers are
siblings, not one tower, and no transfer of an order theorem between them is
known (`experiments/wiedemann_sibling.py` checks levels `0..5` and the
level-two obstruction).

**Arm `O`.** The arm is the residue symbol
`(epsilon_a / P_a)_p != 1` on the unique inert ray above two, and residue
corestriction kills the new coordinate. Bottom-ancestor sections settle
every factor with `L_(r,a)/p <= b_r r^a`; when the literal bottom polynomial
`P_r` is not self-reciprocal, deficiency forces
`L_(r,a)/p >= 2 b_r r^a + r`, and a least counterexample at `r != 3` must
have `P_r != P_r^*`. Kummer-ratio packing over minimal coefficient fields
gives `log_2 o >= (log_2 3)(1 - 1/r) sqrt(r^a) - (log_2 3)/2` for the
selected order `o`. Below explicit thresholds, the prime-to-`r` defect of a
least counterexample is `p` or divisible by `p^2`, and the latter forces a
base-`2^(b_r)` Wieferich prime.

**Arm `C`.** Half-angle reduction gives a recursive norm-one coordinate
`eta_k`: `C_k` holds exactly when `C_(k-1)` holds and
`ord(eta_k) = Phi_(3^k)(2)`. Packing gives
`log_2 ord(eta_k) >= (log_2 3 + 5/6) sqrt(3^k) - O(k)`. The first possible
one-sided relation has weighted residue at least `2 * 3^k + 1`, sharply, and
failure at a current prime `ell` is the single divisibility
`Y^(2H) + Y^H + 1 | T_(N/ell)` for an explicit cubic power-sum recurrence.
The symmetric power-state composition law, its first two jets, and the
digit-gap bound are proved to contain no further obstruction, and the failure
class is invisible to Hilbert 90 because its cyclic `H^1` vanishes.
`C_1`--`C_3` have exact proofs and `C_4`, `C_5` finite certificates; `C_6`
keeps a source-assisted factorization boundary.

**Arm `D`.** The target is equivalent to irreducibility of `R_k(X^ell)` for
every prime `ell | Psi_k`. Palindromicity and a one-third Frobenius
compression reduce it to a parity-twisted power equality, which proves the
arm whenever `Psi_k` is prime. The Cayley coordinate
`V_k = (gamma_k + omega^2)/(gamma_k + omega)` satisfies
`Norm(V_k) = V_(k-1)^(-1)` for `k >= 2`, but every birth-level norm fibre
contains every `ell`-Kummer class, so the full norm recurrence cannot evaluate
the new symbol. An intermediate-field packing sieve proves each current
`ell`-coordinate with `Psi_k/ell < S_k`, where
`log_2 S_k >= 1.2306 sqrt(3^k) - O(k)`, and so a whole level when every prime
divisor of `Psi_k` qualifies. `D'_2`, `D'_3`
follow analytically and `D'_4`, `D'_5` have finite certificates; `D'_6` keeps
a source-assisted primality boundary.

### Missing step

Every arm ends at a one-dimensional value selected recursively by the literal
Conway tower, and a proof must evaluate that marked coordinate uniformly along
its ancestry. Statements about all points of a field do not distinguish it
from formal countermodels with the same trace, norm, torsion, or conductor
data. The proved bounds are exponential in the square root of the field
degree, while the relevant orders are exponential in the degree.

Cross-arm induction is primary-vacuous. If a strict ancestor lies in
`F_(2^d)` with `f(ell)` not dividing `d`, then `ell` does not divide
`2^d - 1` and its `ell`-Kummer image is trivial. Using the next component's
degree to identify `m_ell` is circular, because that radicand is defined as
`kappa_(f(ell)) + m_ell`. A surviving cross-arm argument needs a second,
independently defined top-born `ell`-coordinate.

### The nim reciprocity route

A route into the same conjecture, not a fifth arm: find an
ancestry-recursive formula for the power-residue coordinates

```text
rho_(ell,E)(beta) = beta^((2^E - 1)/ell) in mu_ell
```

of selected elements in the Conway--Lenstra Kummer basis. It must retain the
marked compatible root sequence, be covariant under simultaneous Frobenius,
identify and evaluate the selected prime over `2` wherever a lift to a
number or ray-class field is used, and specialize to `T_h`, `y_(r,a)`,
`gamma_k`, and `M_k` in arms `Z`, `O`, `C`, and `D`.

Its boundary is a proved **rank-one saturation**. After adjoining `mu_ell`,
covariance gives `s_(j,c) = s^(2^j c)` for every Frobenius conjugate and
cyclotomic lift of a selected phase `s`, so every multiplicative reciprocity
word in this family is a single power `s^lambda`: it either erases the phase
or restates `s != 1`. Jacobi convolutions scale one Kummer line by a fixed
character value, and class functions on an affine coset with fixed
multiplier `q != 1` erase its translation coordinate. The intrinsic object is
the gauge-invariant `E`-step Frobenius-orbit holonomy
`T = sum_j 2^(E-1-j) t_j`, but homomorphic splittings over a nontrivial
multiplier subgroup are coboundaries with trivial full-period holonomy, and
affine intertwiners only rescale it.
A successful formula must therefore import an independently evaluable local
class or a genuinely nonhomogeneous ancestry identity; reconstructing the
residue symbol or its orbit product is not enough.

### Evidence and authority

- OEIS A380496 supplies the 126 values for `3 <= p <= 709` as data; exact
  local certificates give `m_359 = m_719 = m_727 = 1`
  (`experiments/ordinary_*_certificate.py`, `experiments/certificates/`).
- `experiments/ordinal_excess_probe.py` and
  `experiments/fermat_selected_screen.py` are bounded screens; explicit
  countermodels in non-Conway fields refute overstrong lemmas only.
- Lean checks algebraic ingredients and named finite certificates, some
  through `native_decide`; `SelectedLogUnitTarget`, `ExceptionalColumnTarget`,
  and `DPrimeTarget` define open propositions without assuming them. See
  [`../formal/README.md`](../formal/README.md).
- The implementation boundary is `src/scalar/big/ordinal/tower.rs`.
- The authoritative account is
  [`../writeups/excess.tex`](../writeups/excess.tex).

## 3. Natural realization of finite misère quotients

Let `A` be a set of finite impartial games closed under options and
disjunctive sum, with misère outcome `o^-`. Positions are equivalent when
`o^-(G + X) = o^-(H + X)` for every `X` in `A`. The quotient is a
commutative monoid `Q` with a distinguished set `P` of previous-player wins:
a reduced bipartite monoid, in which distinct elements are separated by a
context and `1` is not in `P`.

The abstract question is settled. A transition table is a subset of
`Q x Pow(Q)` with product `(x, E)(y, F) = (xy, xF ∪ yE)`; Siegel proved that
a reduced `(Q, P)` is a misère quotient exactly when it admits a
parity-correct, complete, product-closed, well-founded table
([Plambeck--Siegel](https://arxiv.org/abs/math/0609825);
[Siegel](https://arxiv.org/abs/math/0703070)). The open problem begins when
one uniform heap rule must generate the table at every heap size.

**Problem.** Characterize the finite reduced bipartite monoids that are exact
misère quotients of finite-code octal games, by a criterion decidable from
finite data that returns either a code with its quotient map or an
obstruction ruling out every code. An undecidability theorem for synthesis
is an alternative resolution. In
parallel, determine the exact quotient of misère Grundy's game,

```text
opts(H_n) = {H_i + H_(n-i) : 1 <= i < n - i}:
```

decide whether it is finite, and either give a finite presentation with its
`P`-portion and a proved quotient map for every heap, or exhibit infinitely
many pairwise distinguishable positions with separating contexts.

**Why it matters.** Misère play is where combinatorial game theory loses its
group structure, and quotients are the algebra that survives. The
obstruction this problem isolates is octal homogeneity: one digit imposes the
same translated move at every large heap, coupling an intended prefix move to
infinitely many others. Grundy's game is a simple natural ruleset whose
exact misère quotient remains unknown.

### What is proved

- **Trace calculus.** In a reduced valid table the complete option-value set
  determines the value, and no value occurs among its own options. A fixed
  code and table therefore determine one canonical heap trace; a code
  realizes `(Q, P)` exactly when that trace is total, stays in a valid
  table, and generates `Q`. No-self gives digit exclusions: a whole-removal
  move at `n` forces `x_n != 1`, an active one-remainder move forces
  `x_n != x_(n-k)`, and a legal split forces `x_n != x_i x_j` with
  `i + j = n - k`.
- **Periodicity and synthesis.** Finite no-split quotients have ultimately
  periodic traces, so fixed no-split codes are decidable; an asserted
  periodic split trace has a finite certificate: the prefix plus one full
  record period starting at `2N + p + d`. Any
  exact word periodic from `N` with period `p` has a realizing code of length
  at most `3N + 2p`, so synthesis is decidable for bounded preperiod and
  period.
- **Split recurrences.** The split recurrence is a system of unary Boolean
  language equations. For arbitrary partial decoders its totality is
  `Pi^0_1`-complete already for `0.7`, but every nontrivial valid table is
  total there, with the parity trace `x_n = a^n`; the same holds for every
  code with only odd removal offsets and both whole-removal and one-remainder
  moves at offset one. Every two-element split trace
  satisfies `x_(n+2) = x_n` for `n >= 1` (its least period may be one), with
  an explicit finite mask classification.
- **Normal form and its limit.** Every nontrivial finite valid quotient has a
  one-species heap model with finitely many source-local rules and the tail
  `H_n -> H_(n-1)`. When `|Q| > 2` an inert-pad theorem prevents a verbatim
  finite-octal encoding.
- **Ordinary subtraction.** Codes with digits in `{0, 3}` realize exactly the
  trivial quotient, `C_2`, and the tame quotients `T_r` (`r >= 2`), the
  latter by `2^(r-1)` consecutive digits `3`; synthesis in this class is
  decidable with no code-length bound.
- **Grundy's game.** The quotients generated through heaps `12`, `13`, and
  `18` have orders `6`, `12`, and `24`, with presentations, all-multiplicity
  outcome inductions, and separating translation rows. A finite full
  quotient forces a heap with the square of its value among its options and
  hence a nonconstant positive-power cycle. The star acts freely in every
  nontrivial valid quotient, so kernel nontriviality adds no obstruction. The
  canonical mate of `H_13` is not globally equivalent to any Grundy position,
  so separating contexts cannot be imported by mate closure.

### Missing steps

- **Fixed-trace layer.** Decide totality of the canonical trace for a fixed
  valid table and split code. The `Pi^0_1` theorem shows that validity must be
  used, but gives no hardness for valid tables.
- **Synthesis layer.** Give a computable bound on the periodic complexity a
  realization needs, and account for realizations whose heap words might not
  be ultimately periodic; or prove synthesis undecidable.
- **Two-element `P`.** Siegel classified the finite quotients with
  `|P| = 2`. Octal realization of the tame arm is complete; the tame
  extensions of `R_8`, whose base is realized by `0.75`, have no uniform
  finite-octal realization yet.
- **Grundy.** Continue the exact presentations and prove stabilization, or
  produce infinitely many distinct translation rows with explicit separating
  contexts built inside the Grundy universe.

The octal arm closes with the if-and-only-if theorem and its certified
construction/obstruction algorithm; the Grundy arm closes with one of the two
exact certificates. A quotient called *wild* is only non-tame; that word does
not assert infinitude.

### Evidence and authority

- Lean checks transition determinism, meximality and no-self, exact quotient
  fibres, periodic record certificates, saturation and the compressed masks
  with all-heap validity, the star involution, odd-removal totality, the
  binary split criterion, the subtraction mex sequence and outcome law, the
  normal form and inert-pad obstruction, the unary-language dictionary, and
  the finite-color and power-period cores of the Grundy constraint. The
  grammar reduction, compressed-record quotient interpretation, mask and
  subtraction classifications, Grundy presentations, and canonical-mate
  obstruction are paper proofs.
- `src/games/misere.rs` compares bounded element and test sets; its
  signatures are observational, not quotient certificates. The
  `misere_quotient` and `octal_hunt` examples are census instruments under
  that boundary.
- The authoritative account is
  [`../writeups/misere_natural_realization.tex`](../writeups/misere_natural_realization.tex).
