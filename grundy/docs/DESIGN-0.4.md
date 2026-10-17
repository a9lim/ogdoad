# grundy 0.4.0 — design

Working note for the 0.4.0 rewrite. When the build lands, its content moves
into `spec.md`, `implementation.md`, and `stance.md`, and this file is deleted.

## 1. What changes, in one paragraph

grundy 0.3.6 is an executable notation for game *values typed in by hand*,
with one modal world per session. grundy 0.4.0 is a typed, higher-order, pure
language whose subject is the **ruleset**: positions are ordinary data, moves
are functions, and games arise by exploring a ruleset from a position. Its
answers are **observations that state their scope and evidence**. A finite
graph is decided exactly. A claim about a whole family is stated only with a
checked certificate. A bounded sample is typed as bounded, and cannot silently
become a universal fact. Every value displays as a program that rebuilds it.
A certificate is therefore a portable text that re-checks in a fresh session.

## 2. Positioning

- **Standard foundation.** Conway games as a final coalgebra (Honsell–Lenisa,
  LMCS 2011). Win/loss/draw on a finite game graph as retrograde analysis,
  equivalently the well-founded semantics of the win–move program (Van Gelder,
  Ross & Schlipf, JACM 1991). The Sprague–Grundy theorem. Guy–Smith
  periodicity for octal games. Plambeck–Siegel misère quotients (JCTA 2008).
  Damas–Milner inference with Wadler–Blott-style built-in classes and
  Haskell-style literal defaulting.
- **Prior art that already covers part of the ground.** CGSuite/CGScript has
  rulesets via `Options(player)`, cyclic positions, sided values, and canonical
  stoppers. Siegel's MisereSolver computes quotients. Rulesets alone are
  therefore necessary, not novel.
- **Where 0.4.0 differs (synthesis).** Evidence scope is part of the type of
  an answer. Certificates are values that display as re-checkable programs.
  The value/form distinction is two types, not prose.

## 3. Types

Uppercase names are types; lowercase names are values. Types are inferred.
Annotations `e : T` and `(x : T) ↦ …` are optional.

| type | meaning |
| --- | --- |
| `Int` | ℤ as checked `i128`. It is both the integer world and the old Index sort. |
| `Bool` | verdicts |
| `(A, B, …)` | tuples |
| `List A` | finite lists |
| `A -> B`, `(A, B) -> C` | first-class functions (closures) |
| user `data` types | `data Cell = Empty \| Toad \| Frog`, constructors with fields |
| `Game` | a short game *value*, held in canonical form |
| `Form` | a presented game: a finite tree or finite cyclic graph, as built |
| `Rules S` | a ruleset over component positions of type `S` |
| `Winner` | builtin data `Left \| Right \| Draw` |
| `Option A` | builtin data `Some(A) \| None` |
| `Witness`, `Claim` | evidence data, and a sealed verified statement (§7) |
| `Bounded A` | an answer computed on an explicit finite sample (§7) |
| scalar types | `Nimber`, `Ordinal`, `Surreal`, `Omnific`, `F2 F3 F5 F7`, `F4 F8 F16 F9 F27 F25` |
| polynomial types | `F2[t] … F7[t]`, `Int[t]`, `F2(t) … F7(t)` |
| `Algebra S`, `Mv S` | a Clifford algebra over scalar `S` (it carries its metric), and its multivectors |

**Classes** are built in, not user-extensible. They are `Eq`, `Ord` (partial
orders, so `∥` is meaningful), `Add`, `Mul`, `Div`, `Rem`, and `Key` (usable
as a position: structural equality and hashing). There are also literal
classes: `IntLit` (numerals), `StarLit` (`*n`), `FracLit` (a literal-shaped
`a/b`), and `OmegaLit` (`ω`).

**Defaulting replaces the per-world literal tables.** An ambiguous literal type
takes the first type in `Int, Game, Nimber, Surreal` that satisfies all of its
constraints; failing that, the result is a type error asking for an annotation.
Defaulting is purely static. It never retries a candidate after a value-level
failure.

- `3 + 4` is `7 : Int`.
- `*3 ⋅ *5` is `*15 : Nimber`, because Game has no `Mul`.
- `*3 + *5` is the game `*6`.
- `3 + *1` is the game `3*`.
- `1/2` is the game `1/2`. `1/3` selects Game and fails its dyadic check;
  `(1/3 : Surreal)` is exact.
- `(3 : Nimber)` is a type error, with the hint "nimbers are written `*3`".
  The old `from_int` trap becomes a class fact.

Fraction literals and generalization:

- **Fraction literals.** `FracLit` applies only to the literal shape
  `INT/INT`, with an optional leading minus and no parentheses. Wherever a
  type has both `FracLit` and `Div`, the two agree. Game has `FracLit` but no
  `Div`, which closes the Conway parallel without pretending games form a
  field.
- **Generalization by inferred type.** A binding whose inferred type is a
  function type is generalized, with its class constraints. Any other binding
  is monomorphic and defaulted at the end of its statement. So
  `three := 3; three + *1` is a type error, and the hint names `game(three)`.
  A recursive group is monomorphic inside the group and generalized after it.
- **Runtime types.** Evaluation of a polymorphic function receives its
  instantiated types as runtime arguments, so each literal is built at its
  resolved type. No value is ever an untyped numeral.

**Typed display.** The REPL prints `display`, followed by ` : Type` exactly
when re-parsing the display alone would not recover the value's type. This is
0.3.6's minimal-mark rule moved to types.

- `*15 : Nimber`, but a game `*3` prints bare.
- An annotation binds its type's named generator: `(t↑2 + 1 : F5[t])` binds
  `t`, and `(x + 1 : F9)` binds `x`. Polynomial values therefore display as
  self-contained programs.

## 4. Syntax

0.4.0 keeps the 0.3.6 core: `↦` (`~`), `:=`, `=:`, parenthesized `;`
sequences, `if/then/else`, `and/or/not`, `{L | R}`, `*n`, `ω` (`w`), `↑` (`^`),
`∧` (`&`), `⋅` (`.`), `=`, `<`, `>`, `∥` (`!`), `≡` (`===`), the nine outcome
doubles, and both comment forms.

New forms:

- `≤` (`<=`) and `≥` (`>=`) on partial orders.
- `[a, b, c]` lists; `xs ⧺ ys` (`++`) concatenation; `a .. b` (exclusive) and
  `a ..= b` (inclusive) Int ranges.
- Comprehensions: `[e for x in xs if c for y in ys]`.
- Tuples `(a, b)`. Patterns in bindings and binders: `(a, b) := p`,
  `((a, b)) ↦ …`.
- `match e { pat ↦ e, … }`. Patterns are constructors, tuples, `[]`,
  `[x, ..rest]`, literals, and `_`.
- `data Name = C1 | C2(T, …)` declarations.
- Splices in brace forms: `{..xs, 0 | ..ys}` builds options from lists.
- Calls are `f(x, y)` for functions, builtins, polynomials, and rational
  functions. The 0.3.6 `@` is retired.

Retired: `#` and `?` marks (types replace them); `@`; the game-spine list
identity (lists are ordinary data; `[0] ≡ *1` is gone); `⧺` on games; the
modal `:world`.

## 5. Evaluation

- Strict call-by-value; `if`, `and`, and `or` short-circuit. Closures capture
  environments. 0.3.6's capture-by-substitution is retired. A recursive group
  holds its definitions and captured environment without referring to itself
  (no reference cycles). Its names resolve at call time.
- `=:` binds recursive definitions. An adjacent run of `=:` bindings is one
  system, for functions (mutual recursion) and for `Form` equations alike.
- **Budgeted general recursion.** Every closure call spends one unit of fuel,
  and so does every list element produced by a range, comprehension, or move
  generator (`E_Fuel`, default 2²²). Metering every call, not just `=:`
  calls, closes the divergence route through recursive data types with
  function fields. Recursion depth has its own guard
  (`E_StackDepth`). Every graph or exploration has a node budget
  (`E_GraphBudget`). Budget exhaustion is never a value, and never "draw" or
  "equal". This is the honest name for 0.3.6's "total" stance: grundy is not
  Turner-total.
- **Display law.** `parse ∘ unparse = id`, and `eval ∘ parse ∘ display ≃
  value`.
  - Closures display as let-blocks of their captured values.
  - Recursive closures display as `=:` systems.
  - Forms display as equation systems.
  - Claims display as `check`-able constructor calls.

## 6. Games

**`Game` and `Form` are the value/form distinction as two types.** Every
operation on `Game` respects `=` by construction, because the representation
is canonical.

- `Game` covers integers, dyadic literals, `*n`, `up`, `down`, and braces in
  `Game` context.
  - `+`, `-`, `= < > ≤ ≥ ∥`, and the outcome doubles.
  - `birthday`, `lefts`, and `rights` (canonical options).
  - `temperature`, `mean`, `left_stop`, `right_stop`, `atomic_weight`.
  - Bridges: `number(g) : Surreal` and `nimber(g) : Nimber` are partial (they
    fail with `E_Domain` off their domain); `game(x)` embeds `Int`, `Nimber`,
    or dyadic `Surreal` values.
- `Form` covers braces in `Form` context, `=:` equation systems, and
  `form(g)`. Its options come back in presentation order.
  - `≡` (multiset bisimilarity), `+` and `-` (product graph), and the outcome
    doubles.
  - Value relations only between stoppers. Beyond stoppers they fail with
    `E_Loopy`, which names the alternating cycle.
  - `canon(f) : Game` fails with `E_Loopy` on a cyclic form.
  - `stopper`, `hasdraw`, `outcome(f) : (Winner, Winner)`, and `birthday`
    (presented).
- A brace form takes `Game` or `Form` from context and defaults to `Game`, so
  `3 - 1` is `2` and the 0.3.6 form explosion is gone. A recursive non-function
  `=:` is a `Form`: guardedness is the 0.3.6 rule, and system names may appear
  only directly as brace options.
- **Misère is not a mode.** It is observed relative to a universe (§7).

### Rulesets

```text
nim          := impartial(n ↦ [[k] for k in 0 .. n])
subtraction  := impartial(n ↦ [[n - k] for k in [1, 2, 3] if k ≤ n])
kayles       := impartial(n ↦ [[a, n - k - a] for k in [1, 2] if k ≤ n
                                               for a in 0 ..= n - k])
grundy_game  := impartial(n ↦ [[a, n - a] for a in 1 .. n if 2 ⋅ a < n])
toads_frogs  := partizan(left_moves, right_moves)   // over a user data type
octal([0, 7])                                       // a Rules Int from an octal code
```

- **An option is a list of components**, that is, a disjunctive sum.
  Splitting games are first-class, and a ruleset's universe is the closure of
  its components under sum.
- `impartial(moves : S -> List (List S))` and `partizan(left, right)` build
  `Rules S`, which requires `Key S`.
- Exploration:
  - `value(R, p) : Game` computes components bottom-up with memoization.
    A component cycle fails with `E_Loopy`, carrying the cycle of positions.
  - `graph(R, p) : Form` materializes sum-states, cycles allowed.
  - `sg(R, p) : Int` (impartial) is the Grundy number: mex over the nim-sum
    of component values. By the Sprague–Grundy theorem `value(R, p)` is then
    `*sg(R, p)`. On a partizan ruleset, `sg` is `E_Domain`; impartiality is
    a checked runtime flag on `Rules`.
  - `moves(R, ps, player)` lists the actual ruleset moves of a sum `ps`.
  - `winning(R, ps, player)` keeps the moves whose successor sum wins in
    normal play: `≥ 0` for Left, `≤ 0` for Right. Canonical bypasses are never
    returned as moves.

Further rules for exploration:

- **`[]` and `[[]]` differ.** `[]` means no options; `[[]]` is one option
  that removes the component.
- **Sum-states are multisets** normalized by a structural total order on
  `Key` values. Finitely many component positions do not imply finitely many
  sum-states (`moves(p) = [[p, p]]`), so `graph` spends its node budget
  honestly.
- **`Game` is sealed canonical.** Every constructor and operation re-seals the
  canonical form, with options sorted by canonical key. `lefts` and `rights`
  are therefore deterministic, and every `Game` operation is a function of the
  value.

## 7. Scope and evidence

- **Exact.** A computation on a finite object (a short game, a finite graph,
  a well-founded explored ruleset) returns plain values. `=`, `outcome`, `sg`,
  and `value` are exact.
- **`Witness` → `Claim`.** A `Witness` is freely constructible evidence data.
  `verify(w) : Claim` runs only the independent checker, and either returns a
  sealed `Claim` or fails with `E_Refuted`, naming the failing condition.
  A `Claim` displays as `verify(<witness>)`, so re-evaluating its text
  re-verifies it. Edited text that states something false fails before any
  `Claim` exists. A statement is structured data bound to its exact graph,
  ruleset, root, and play convention. Producers return verified claims:
  - `certify(f : Form) : Claim` certifies `outcome(f)`. Its certificate labels
    every turn-state Win, Loss, or Draw, with ranks and chosen moves. Check by
    local conditions:
    - a Win's chosen move reaches an opponent Loss of lower rank;
    - every move from a Loss reaches an opponent Win of lower rank;
    - a Draw has no move to an opponent Loss, and its chosen move stays in Draw.

    The check is O(V+E) and independent of the solver.
  - `certify_sg(R, p) : Claim` certifies a Grundy labeling of the explored
    components:
    - ranks strictly decrease along options (well-foundedness);
    - for each `v < sg(p)`, an option attains `v`;
    - no option attains `sg(p)`.
  - `periodic(R, preperiod, period) : Claim` covers all heaps of an octal
    ruleset, via the existing Guy–Smith certificate. It applies only to rules
    built by `octal(…)`. Its scope is the family, resting on a cited theorem
    with checked hypotheses.
  - `separate(R, p, q, tests) : Option Claim` searches for a misère separating
    context `x` in the universe of `R`, with `o⁻(p + x) ≠ o⁻(q + x)`. A found
    context is verified by direct misère play, and one finite witness proves
    distinguishability in the whole universe. `None` means only that no
    witness exists among the stated tests.
  - Misère outcomes need no universe: `misere(R, ps) : Winner`. Misère
    indistinguishability does.
- **`Bounded A`.** An answer computed on an explicit finite sample of an
  infinite universe. It keeps its sample metadata: ruleset, elements, tests,
  and convention.
  - `misere_quotient(R, heaps, elems, tests) : Bounded Quotient`. A sampled
    quotient exposes its partition, signatures, P-classes, and a *candidate*
    multiplication table with its consistency flags. It offers no monoid
    operations, because finite-test agreement need not be a congruence.
  - `misere_equal(R, p, q, tests) : Bounded Bool`.
  - **A `Bounded Bool` is not a `Bool`.** `if misere_equal(…)` is a type
    error. The only projection is `sampled(b)`, which is visible in the
    program text. Sampled agreement cannot silently become equivalence.

## 8. Algebra worlds as types

Every 0.3.6 world survives as a type, and several coexist in one program.
`clifford(q)`, `clifford(q, b)`, and `clifford(q, b, a)` build an `Algebra S`
from metric lists; `grassmann(S, n)`, `basis(A) : List (Mv S)`,
`vector(A, xs)`, and `scalar(A, s)` complete the set. The operations are
`+ - ⋅ ∧ / ↑`, `rev`, `grade`, `even`, `dual`, and `coef`; mixing algebras is
`E_AlgebraMismatch`. Polynomials:

- `gen(F5[t])` is the indeterminate; `gen(F9)` is the field generator.
- `poly(xs)` builds from coefficients.
- `p(v)` evaluates or composes.
- `deg`, `gcd`, and `integral` carry over.

The scalar partiality boundaries carry over unchanged: Kummer escape, monomial
inverses, exact division.

## 9. Kept, cut, deferred

- **Kept from 0.3.6:**
  - the nine outcome doubles;
  - the loopy equation-system machinery and its self-contained display;
  - multiset bisimilarity;
  - dyadic and nimber recognition;
  - witness-carrying errors, with hints in the hint field;
  - budgets;
  - the display laws.
- **Cut:** the first-order restriction; capture by substitution; sort marks;
  sample-evaluation validation; the game-spine list identity; modal worlds;
  presentation-order indexing on `Game`.
- **Deferred:**
  - ordinal sum `G:H`;
  - sided loopy values and onside/offside;
  - Smith/Fraenkel generalized SG;
  - exact misère quotients for whole universes;
  - Lean-checkable certificate export;
  - removing host stack depth as a semantic limit.

## 10. Build order

The OPEN.md §3 pipeline comes first: components, impartial rulesets,
budgeted misère, signatures, separating contexts, and re-checkable evidence.
The algebra worlds follow, within the same 0.4.0.

1. Syntax: lexer, parser, AST, and unparser, with parse/unparse law tests.
2. Types: representation, unification, classes, defaulting, and
   span-carrying errors.
3. Evaluator: values, environments, closures, recursion, and budgets.
4. Games: `Game` and `Form` over the reused 0.3.6 loopy layer.
5. Rulesets, exploration, and SG.
6. Certificates, claims, and the `Bounded` type. The certifying outcome solver
   and SG certificates go in the engine (`src/games/`).
7. Misère: quotients, separation, and bounded equality.
8. Algebra worlds as types, and bridges.
9. Display of every value as a program.
10. The new corpus, law tests, and docs; the REPL; version 0.4.0.
