# grundy — language specification

Status: **implemented, 0.4.0**. This document is the normative language
contract: syntax, types, semantics, evidence, display, and errors. Runtime
architecture and resource guards live in [`implementation.md`](implementation.md);
the design tradition is in [`stance.md`](stance.md); proposed work is in
[`docs/ROADMAP.md`](../../docs/ROADMAP.md).

Every observable rule here is pinned by the conformance suite (§16): the
corpus [`conformance.txt`](conformance.txt) and the law tests. The
specification governs any behavior those tests do not select.

The name honors P. M. Grundy of the Sprague–Grundy theorem. Files use the
extension `.og` (after Ogdoad, the crate that supplies the values).

---

## 1. Identity

grundy is a typed, higher-order, pure language for combinatorial games. Its
subject is the **ruleset**: positions are ordinary data, moves are functions,
and games arise by exploring a ruleset from a position. Its answers state
their scope and evidence:

- **exact** answers about finite objects (a short game, a finite graph, an
  explored terminating ruleset) are plain values;
- **claims** about whole families or with checkable evidence are sealed
  `Claim` values, verified by an independent checker;
- **sampled** answers over an infinite universe are typed `Bounded(a)`, a
  different type from `a`, with one visible projection.

Ogdoad's scalar, polynomial, rational-function, and Clifford worlds are types
that coexist in one program. There is no modal world.

Two display laws govern the surface: `parse ∘ unparse = id` on parser-produced
trees, and re-evaluating a value's display rebuilds the value (§13).

Short games under disjunctive sum form an abelian group, not a ring: `Game` has
`+` and `-` but no `⋅`. There are no mutation, I/O, strings, floats, or
implicit coercions.

## 2. Symbols

| meaning | canonical | ASCII sugar |
|---|---|---|
| omega | `ω` | `w` |
| power | `↑` | `^` |
| wedge | `∧` | `&` |
| product | `⋅` | `.` (also `·`) |
| lambda | `↦` | `~` |
| function type | `→` | `->` |
| equality | `=` | `==` |
| fuzzy | `∥` | `!` |
| structural equality | `≡` | `===` |
| at most, at least | `≤`, `≥` | `<=`, `>=` |
| list concatenation | `⧺` | `++` |
| draw atom (in outcome doubles) | `‿` | `_` |
| range, inclusive range | `..`, `..=` | — |
| binding, recursive binding | `:=`, `=:` | — |
| annotation | `:` | — |

The nine **outcome doubles** `>> >‿ >< ‿> ‿‿ ‿< <> <‿ <<` (sugar: `_` for
`‿`) are relations. Each is two mover-result atoms: the result when Left
starts, then when Right starts (`>` Left wins, `<` Right wins, `‿` draw).

Reserved words: `if then else and or not true false up down for in match data`
and `w`. `↑↑` and `O(` are reserved (`E_Reserved`).

**Unary-fill principle.** A unary form of a binary operator fills the left
operand with that operator's identity: `-a = 0 - a`, `/a = 1/a`.

## 3. Lexical structure

- Tokens are self-delimiting; whitespace is never semantic, and there is no
  juxtaposition.
- `INT` is `[0-9]+` within `u128`; signs are unary `-`.
- Lowercase identifiers (`[a-z][A-Za-z0-9_]*`) are variables. Uppercase
  identifiers are types and constructors.
- `*` before an operand is the star prefix; `*` after a complete operand is an
  error with the hint that the product is `⋅`.
- `/*` always opens a comment, so a reciprocal of a star literal is written
  `/(*2)`.
- Comments: `//` to end of line, and `/* … */`, which nests.
- **Continuation.** Input continues while `(`, `[`, or `{` is open, inside a
  block comment, and after a line whose last token cannot end a statement (an
  operator, `↦`, `:=`, `=:`, `,`, `;`, `:`, or one of `if then else and or not
  for in match data`).

## 4. Grammar

```ebnf
statement  = data | sequence ;
data       = "data" UPPER "=" ctor { "|" ctor } ;
ctor       = UPPER [ "(" type { "," type } ")" ] ;
sequence   = { binding ";" } ( binding | expr ) ;
binding    = pattern ":=" expr | IDENT "=:" expr ;

expr       = lambda | cond [ ":" type ] ;
lambda     = params "↦" expr ;
params     = IDENT | "_" | "(" [ param { "," param } ] ")" ;
param      = pattern [ ":" type ] ;
cond       = "if" expr "then" expr "else" expr
           | "match" or "{" arm { "," arm } "}"
           | or ;
arm        = pattern "↦" expr ;
or         = and { "or" and } ;
and        = not { "and" not } ;
not        = { "not" } rel ;
rel        = cat [ relop cat ] ;           (* relations never chain *)
cat        = range [ "⧺" cat ] ;
range      = add [ ( ".." | "..=" ) add ] ;
add        = mul { ( "+" | "-" ) mul } ;
mul        = wedge { ( "⋅" | "/" | "%" ) wedge } ;
wedge      = unary { "∧" unary } ;
unary      = { "-" | "/" } power ;
power      = postfix [ "↑" unary ] ;       (* right-associative *)
postfix    = atom { "(" [ expr { "," expr } ] ")" | "[" expr "]" } ;
atom       = INT | star | "ω" | "true" | "false" | "up" | "down"
           | IDENT | UPPER
           | "(" sequence ")" | "(" expr { "," expr } ")"
           | "[" [ item { "," item } ] "]"
           | "[" expr clause { clause } "]"
           | "{" [ item { "," item } ] "|" [ item { "," item } ] "}" ;
item       = expr | ".." expr ;            (* a splice *)
clause     = "for" pattern "in" or | "if" or ;
star       = "*" [ INT | "ω" | "(" cnf ")" ] ;
cnf        = term { "+" term } ;           (* strictly descending, E_CnfOrder *)
term       = INT | "ω" [ "↑" ( INT | "ω" | "(" cnf ")" ) ] [ "⋅" INT ] ;

pattern    = "_" | IDENT | [ "-" ] INT | "true" | "false"
           | UPPER [ "(" pattern { "," pattern } ")" ]
           | "(" pattern [ ":" type ] ")" | "(" pattern "," pattern { "," pattern } ")"
           | "[" [ pattern { "," pattern } [ "," ".." [ pattern ] ] ] "]" ;

type       = btype [ "→" type ] | "(" type { "," type } ")" [ "→" type ] ;
btype      = UPPER [ "(" type { "," type } ")" ] | UPPER "[" "t" "]" | IDENT ;
```

Notes:

- **Precedence**, tightest first: call and index, `↑`, unary `- /`, `∧`,
  `⋅ / %`, `+ -`, ranges, `⧺`, relations, `not`, `and`, `or`, conditionals,
  `↦` and annotation. Wedge binds tighter than product, after Hestenes.
- **Fraction literals.** `INT / INT`, written without parentheses and with an
  optional unary minus on either side, is a literal. `(1)/(2)` is a division.
- A **star literal** is structural: inside `*(…)`, `+ ⋅ ↑` build a CNF
  ordinal *index*, not arithmetic. `*` alone is `*1`.
- `S[t]` is a polynomial ring and `S(t)` (for `S` in `F2 F3 F5 F7`) a
  rational-function field.
- In types, lowercase names are type variables. A conditional is not an
  operand; parenthesize it.
- `(a, b) ↦ e` takes two arguments; `((a, b)) ↦ e` takes one tuple.

## 5. Types

| type | values |
|---|---|
| `Int` | ℤ as checked `i128` |
| `Bool` | `true`, `false` |
| `(A, B, …)` | tuples |
| `List(A)` | finite lists |
| `A → B`, `(A, B) → C` | functions |
| user `data` types | constructors with fields |
| `Winner` | `Left`, `Right`, `Draw` |
| `Option(A)` | `Some(a)`, `None` |
| `Game` | short game values, sealed in canonical form (§8) |
| `Form` | presented games: finite trees as built, and finite cyclic graphs (§8) |
| `Rules(S)` | rulesets over component positions of type `S` (§9) |
| `Witness`, `Claim` | evidence, and verified statements (§10) |
| `Bounded(A)` | answers on an explicit finite sample (§10) |
| `Quotient(S)` | a sampled misère quotient (§10) |
| `Nimber` | finite nimbers `F_{2^128}` |
| `Ordinal` | ordinal nimbers `On₂`, below the represented Kummer tower |
| `Surreal`, `Omnific` | surreal numbers with finite Hahn support; omnific integers |
| `F2 F3 F5 F7`, `F4 F8 F16 F9 F27 F25` | prime and extension fields |
| `F2[t] … F7[t]`, `Int[t]` | polynomial rings |
| `F2(t) … F7(t)` | rational-function fields |
| `Algebra(S)`, `Mv(S)` | Clifford algebras over `S` (carrying a metric), and multivectors |

### 5.1 Inference and classes

Inference is Damas–Milner with let-generalization and a fixed set of built-in
classes. Users cannot add instances.

| class | meaning | instances |
|---|---|---|
| `Eq` | `=` | data without function fields; Game; Form (stopper-gated, §8.3); Mv; scalars |
| `Ord` | `< > ≤ ≥ ∥` (partial orders) | Int, Game, Form, Nimber, Ordinal, Surreal, Omnific |
| `Add` | `+ -`, unary `-` | numbers, Game, Form, polynomials, rational functions, Mv |
| `Mul` | `⋅`, `↑` by `Int` | Int, scalars, polynomials, rational functions, Mv |
| `Div` | `/`, unary `/` | scalars (exact for Omnific), polynomials (exact), rational functions, Mv |
| `Rem` | `%` | Int (Euclidean), Surreal and Omnific (monic ω-power moduli), polynomials |
| `Wedge` | `∧` | Mv |
| `Key` | usable as a position | Int, Bool, Winner, Game, scalars, polynomials, rational functions; tuples, lists, options, and data of keys |
| `IntLit` | numerals | Int, Game, Form, Surreal, Omnific, finite fields, polynomials and rational functions over them, Mv |
| `StarLit` | `*n` | Game, Form, Nimber, Ordinal, Mv over those |
| `FracLit` | literal `a/b` | Game (dyadics only), Form, Surreal, finite fields, rational functions, polynomials over fields, Mv |
| `OmegaLit` | `ω` | Surreal, Omnific, Mv over those |
| `GameLike` | brace forms, `up`/`down`, outcome doubles | Game, Form |
| `IntoGame` | `game(x)` | Int, Nimber, Surreal, Game |
| `Scalar` | Clifford coefficients | Int, Nimber, Ordinal, Surreal, Omnific, finite fields |
| `FiniteField` | `frob`, `tr` | Nimber, finite fields |
| `Integral` | `integral` | Surreal, Omnific, Int, polynomials, rational functions |

A power `a ↑ e` needs `e : Int` with `Mul a`, except that `ω ↑ s` with
`s : Surreal` builds a Hahn monomial (its base must be exactly `ω`).

### 5.2 Defaulting

An ambiguous variable with constraints takes the first type in
`Int, Game, Nimber, Surreal, Form` that satisfies all of them; if none does,
the result is `E_Ambiguous`. Defaulting is static and never retried after a
runtime failure.

- `3 + 4` is Int, `*3 + *5` is Game, `*3 ⋅ *5` is Nimber (Game has no `Mul`).
- `3 + *1` is the game `3*`; `1/2` is the game `1/2`.
- `1/3` selects Game and fails its dyadic check; `(1/3 : Surreal)` is exact.
- `FracLit` and `Div` agree wherever a type has both.
- `(3 : Nimber)` is `E_Type`. Nimber has no integer literals, because
  `from_int` would collapse 3 to 1 in characteristic two.

### 5.3 Generalization

- A binding whose right-hand side is a lambda is generalized with its
  constraints.
- Any other binding generalizes only unconstrained variables; its constrained
  variables stay monomorphic and are defaulted at the end of the statement.
  So `three := 3` is `Int`, and `three + *1` is a type error.
- A recursive group is monomorphic inside the group and generalized after it.
- A generalized function receives its instantiated types at runtime, so a
  literal inside it is built at the type of each use:
  `succ := x ↦ x + 1; (succ(3), succ({0 |}))` is `(4, 2) : (Int, Game)`.

### 5.4 Annotations and generators

`e : T` unifies the type of `e` with `T`. Lowercase names in `T` are type
variables scoped to that annotation.

An annotation **binds its type's generator** within `e`:

- `t` for `S[t]` and `S(t)`;
- `x` for the extension fields.

So `(t↑2 + 1 : F5[t])` and `(x + 1 : F9)` are self-contained, and these
values display that way.

## 6. Evaluation

- **Order.** Evaluation is strict, call-by-value, left to right. `if`,
  `and`, and `or` short-circuit.
- **Closures** capture their environment at definition, including globals:
  rebinding a name later does not change an earlier closure.
- **Recursion.** `name =: e` binds a recursive definition, and a maximal
  adjacent run of `=:` bindings is one system. By inferred type:
  - a run of functions is a mutually recursive group, and each right-hand side
    must be a lambda;
  - a run of `Form` equations is a guarded game-equation system (§8.4);
  - any other type is `E_Fixpoint`;
  - mixing functions and equations in one run is also `E_Fixpoint`.
- **Sequences.** `(b1; b2; e)` scopes bindings over `e`. At top level,
  `b1; b2; e` binds globally. A discarded intermediate value is `E_Parse` (it
  would be dead code).
- **Patterns** destructure in bindings, parameters, comprehension sources, and
  `match` arms. A refutable binding that fails is `E_Pattern`, and so is a
  `match` with no matching arm.

**Budgets.** These are the operational replacement for divergence. A budget
never becomes a value, a draw, or an equality.

- **Fuel** (`E_Fuel`, default 2²²) is spent on every closure call, on every
  list element produced by a range, comprehension, or builtin, and on every
  component of every generated option and sum-state. A product of
  surreals, polynomials, rational functions, or multivectors spends the
  product of its operands' term counts before the work, and their integer
  powers are square-and-multiply chains of such products. `Game` arithmetic,
  comparison, and construction spend one unit per canonical-form step they
  actually perform; a value met before costs nothing. A `Form` literal spends
  the size of the form it builds. Displaying a value spends one unit per atom
  written. Metering every call closes divergence through data with function
  fields.
- **The depth guards** (`E_StackDepth`) are host resources, distinct from
  fuel: 4096 call frames, and games born no later than day 2¹⁴.
- **The node budget** (`E_GraphBudget`, default 2¹⁶) bounds distinct
  positions, sum-states, and graph nodes in every exploration and
  materialization.

## 7. Scalars and algebra

| type | partiality |
|---|---|
| `Int` | checked overflow (`E_Overflow`); `%` is Euclidean; integer quotients are `div(a, b)` |
| `Nimber` | none in the field operations |
| `Ordinal` | `⋅`, `/`, `↑` past the represented Kummer tower are `E_KummerEscape` |
| `Surreal` | only CNF monomials invert (`E_NotInvertible`); `%` takes a monic ω-power modulus (`E_Modulus`) |
| `Omnific` | units are ±1; non-exact `/` is `E_NotInvertible` |
| finite fields | none; `%` is not defined |
| `S[t]` | `/` is exact division, failing with the remainder named; `Int[t]` divides only by monic polynomials (`E_Modulus`) |
| `S(t)` | evaluation at a pole is `E_DivisionByZero` |
| `Mv(S)` | operands from different algebras are `E_AlgebraMismatch`; non-invertible elements are `E_NotInvertible`; `rev` and `dual` refuse general bilinear metrics (`E_GeneralMetric`) |

Polynomials and rational functions are **callable**: `p(v)` evaluates at a
coefficient, and `p(q)` composes within one ring or field. Their call type
must be known where the call is checked.

A Clifford algebra is a value:

- `clifford(q)` takes a diagonal metric; `clifford_metric(q, b, a)` takes the
  polar and ordered data; `grassmann(n)` is the Grassmann algebra (annotate
  its scalar type).
- `basis(alg)` yields `e0 … e(n-1)`, conventionally bound with
  `[e0, e1] := basis(alg)`.
- A multivector carries its algebra. A grade-0 value built from a literal has
  no algebra until it meets one.

`Metric` keeps `q`, `b`, and `a` distinct, as the engine does.

## 8. Games

### 8.1 Game

A `Game` is a short game value held in **sealed canonical form**:
canonicalized (dominated options removed, reversible options bypassed),
hash-consed, with options sorted by a deterministic structural order. Every
operation on `Game` is therefore a function of the value.

- **Literals:** integers, dyadic fraction literals, `*n`, `up`, `down`, and
  braces in Game context.
- **Operations:** `+`, `-`, the relations `= < > ≤ ≥ ∥`, and the outcome
  doubles.
- **Inspection:** `lefts` and `rights` (canonical options), `birthday` (the
  value birthday), `outcome(g) : (Winner, Winner)`, `temperature`, `mean`,
  `left_stop`, `right_stop`, `atomic_weight` (all-small games).
- **Bridges** (partial, `E_Domain` off their domains): `number(g) : Surreal`,
  `nimber(g) : Nimber`, `is_number(g)`. `game(x)` embeds an Int, a Nimber, or
  a dyadic Surreal.

### 8.2 Form

A `Form` is a presented game: a finite tree exactly as built, or a finite
cyclic graph from guarded equations (§8.4).

- **Construction:** braces in Form context, `form(g)` (the canonical form
  presented), and equation systems.
- **Structure:** `lefts` and `rights` in presentation order, presented
  `birthday` (`E_Loopy` on a cycle), and `≡` (multiset bisimilarity, total on
  every form).
- **Arithmetic:** `+` (the product graph) and `-` (the L/R swap).
- **Inspection:** `stopper`, `hasdraw`, `outcome`.
- **Conversion:** `canon(f) : Game` reads a finite form's value and refuses a
  cyclic one (`E_Loopy`).

A brace form takes Game or Form from context and defaults to Game. A
literal's Form construction is exactly what its display rebuilds.

### 8.3 Relations

On Game, `= < > ≤ ≥ ∥` are the classical partition, and the doubles read the
outcome of `G − H`. Finite games never draw, so the five `‿` doubles are
false there.

On Form:

- **Doubles** read the outcome partition of the conjugate sum `G + (−H)`,
  total on every pair. A player wins by forcing a finite win; infinite play is
  a draw; each player prefers win over draw over loss.
- **Value relations** require both presented operands to be stoppers (no
  reachable alternating cycle in the turn-expanded graph). They then project
  the double: `{>>, >‿} → >`, `{><} → ∥`, `{<>, <‿, ‿>, ‿‿} → =`,
  `{‿<, <<} → <`. Standard: Siegel, *Combinatorial Game Theory*, GSM 146,
  Def. VI.1.8 and Thm. VI.2.1.
- **Non-stoppers.** Beyond stoppers, value relations are `E_Loopy`, naming
  the alternating cycle (for example `left operand has alternating cycle
  0:L→0:R→0:L`).

Negation is 180° rotation of the grid: `cell(−G, −H) = rotate(cell(G, H))`,
and swapping operands acts the same way.

### 8.4 Guarded game equations

`name =: rhs`, where `rhs` is Form-typed, closes into a finite cyclic graph,
and adjacent equations form one system.

- **Guardedness:** a system name may appear only directly as a brace option,
  possibly inside nested braces. A bare root (`g =: g`), or a system name
  under any other operator (`h =: {0 | h} + 1`) or inside a splice, is
  `E_Unfounded`.
- **Equation solutions:** `on =: {on |}` and `dud =: {dud | dud}` are Siegel's
  defining equations.
- **Semantics:** these presentations are the finite (regular) part of the
  final-coalgebra account of loopy games (Honsell–Lenisa, *LMCS* 2011).

## 9. Rulesets

A ruleset is a move generator over component positions of a `Key` type `S`.
**An option is a list of components**, that is, a disjunctive sum:

- `[]` means no options;
- `[[]]` is one option that removes the component;
- `[[a, b]]` splits the component into `a + b`.

| constructor | |
|---|---|
| `impartial(moves)` | `moves : S → List(List(S))` for both players |
| `partizan(left, right)` | separate Left and Right generators |
| `octal(digits)` | the octal game `0.d₁d₂…` on heaps |

| exploration | |
|---|---|
| `value(R, p) : Game` | explores components and values them children-first; a component cycle is `E_Loopy`, naming the cycle of positions |
| `sg(R, p) : Int` | the Grundy number of an impartial component: mex over the nim-sum of each option's components |
| `graph(R, p) : Form` | the sum-state graph (states are multisets of components), cycles allowed |
| `moves(R, ps, player)` | the actual ruleset moves of the sum `ps` |
| `winning(R, ps, player)` | the moves whose successor wins in normal play: `≥ 0` after a Left move, `≤ 0` after a Right move |

By the Sprague–Grundy theorem, `value(R, p) = *sg(R, p)` for impartial
terminating rulesets; this is a law test (§16). `sg` on a partizan ruleset is
`E_Domain`. `winning` never returns a canonical bypass as a move.

A ruleset caches its explored values. Finitely many component positions do
not imply finitely many sum-states: `impartial(n ↦ [[n, n]])` spends its
budget honestly.

## 10. Evidence

### 10.1 Witnesses and claims

A `Witness` is freely constructible evidence data. `verify(w) : Claim` runs
only an independent checker and either seals a `Claim` or fails with
`E_Refuted`, naming the failed condition. A claim displays as
`verify(<witness>) /* claim: … */`: re-evaluating the text re-checks the
evidence, and the comment states the conclusion. `evidence(c)` returns the
witness.

| producer | witness | the checker verifies |
|---|---|---|
| `certify(f : Form)` | `outcome_witness(left, right, misère, labels)`: an explicit graph and one `(verdict, rank, chosen)` label per turn-state | the edges are valid. A Win of rank `r > 0` chooses a move to an opponent Loss of lower rank; under misère, rank 0 is a terminal win. Every move from a Loss reaches an opponent Win of lower rank; under normal play, a terminal is a Loss of rank 0. A Draw is not terminal, has no move to an opponent Loss, and chooses a move to a Draw. |
| `certify_sg(R, p)` | `sg_witness(R, p, table)`: `(position, grundy, rank)` triples | the ruleset is impartial and the root is in the table. Each entry's complete options are regenerated: every component is in the table at a lower rank, the Grundy value is at most the option count, and it equals the mex of the options' nim-sums. |
| `periodic(R, preperiod, period)` | `periodic_witness(R, preperiod, period)` | `R` was built by `octal`, and the Guy–Smith window holds. Scope: every heap. |
| `separate(R, p, q, contexts)` | `separation_witness(R, p, q, x)` | the ruleset is impartial and the misère outcomes of `p + x` and `q + x` differ. |

The outcome checker is sound and complete for the retrograde partition: Win
and Loss labels are sound by induction on rank. A player at a Draw state who
keeps choosing Draw successors never reaches a Loss, and no move from a Draw
state reaches one. The retrograde stages supply such ranks; they need not be
optimal distances. The checker is `O(V + E)` on the explicit graph,
independent of the solver.

The other evidence rests on cited theorems:

- **Guy–Smith.** The periodicity theorem as stated in A. N. Siegel, *Games
  of No Chance 5*, Thm. 2.4. The
  checker recomputes the exact prefix of length `2⋅preperiod + period + k`
  and its shift, where `k` is the last nonzero digit. It certifies the
  supplied period, not its minimality.
- **Separation.** The universe of `R` is all finite sums of its positions, so
  one finite context proves the two sums distinguishable in the whole
  universe.

`separate` returns `None` when no stated context separates. That says only
that no witness exists among those tests.

### 10.2 Bounded answers

A `Bounded(a)` is an answer computed on an explicit finite sample. It is a
different type from `a`; the only projection is `sampled(b)`, visible in the
program text. `samples(b)` is the sample size, and a bounded value displays
as `bounded(value, samples)`.

- `misere_equal(R, p, q, contexts) : Bounded(Bool)` is agreement of misère
  outcomes on the stated contexts.
- `misere_quotient(R, atoms, elements, tests) : Bounded(Quotient(S))` takes
  every multiset of at most `elements` atoms and classifies it by its misère
  outcome signature against every multiset of at most `tests` atoms
  (Plambeck–Siegel, *JCTA* 2008, bounded).

A sampled quotient exposes:

- `classes` (the member sums of each class);
- `p_classes` (the misère P-positions);
- `table` (a *candidate* multiplication table, present when every class
  product was sampled);
- `consistent` (whether every sampled member product agrees with that table);
- `class_of`.

It offers no monoid operations, because agreement on finitely many tests need
not be a congruence. `quotient(classes, p, table)` rebuilds one.

Misère outcomes need no universe: `misere(R, ps) : (Winner, Winner)`, for
impartial and partizan rulesets alike. Misère indistinguishability does.
Misère quotients and separation are impartial (`E_Domain` otherwise) and
cover terminating rulesets (`E_Loopy` on a misère cycle).

## 11. Builtins

| builtin | type |
|---|---|
| `len`, `reverse`, `flatten`, `zip` | list structure |
| `map`, `filter`, `fold`, `any`, `all` | higher-order list operations |
| `sum` | `Add a ⇒ List(a) → a` (zero at the element type) |
| `contains` | `Eq a ⇒ (List(a), a) → Bool` |
| `sort`, `unique` | `Key a ⇒ List(a) → List(a)` (structural order; `unique` keeps first occurrences) |
| `sums(atoms, k)` | every multiset of at most `k` atoms, the empty sum first |
| `div`, `abs`, `min`, `max`, `xor`, `mex` | Int; `xor` is nim-sum of natural numbers |
| `game`, `form`, `canon`, `number`, `nimber`, `is_number` | §8 |
| `lefts`, `rights`, `birthday`, `outcome`, `stopper`, `hasdraw` | §8 |
| `temperature`, `mean`, `left_stop`, `right_stop`, `atomic_weight` | §8.1 |
| `impartial`, `partizan`, `octal`, `value`, `sg`, `graph`, `moves`, `winning` | §9 |
| `misere`, `misere_equal`, `misere_quotient`, `separate` | §10 |
| `bounded`, `sampled`, `samples`, `quotient`, `classes`, `p_classes`, `table`, `consistent`, `class_of` | §10.2 |
| `certify`, `certify_sg`, `periodic`, `verify`, `evidence`, and the `*_witness` constructors | §10.1 |
| `deg`, `coef`, `gcd`, `integral` | polynomials; `integral` is ring-of-integers membership |
| `frob`, `tr`, `nimtr(x, m)` | finite fields; a nimber trace names its subfield `F_{2^m}` |
| `clifford`, `clifford_metric`, `grassmann`, `basis`, `vector`, `dim` | §7 |
| `rev`, `even`, `dual`, `grade`, `component`, `scalar_part` | multivectors |

Builtins live in the outermost scope; any binding may shadow one.

## 12. Data and patterns

- `data T = C1 | C2(A, B)` declares constructors, and a declaration may
  refer to itself.
- A data type supports `=` and is a `Key` exactly when every field does.
  Function fields remove both.
- Constructors are values and patterns.
- `Left`, `Right`, `Draw`, `Some`, and `None` are builtin.
- The patterns are `_`, variables, integer and Boolean literals, tuples,
  constructors, list patterns `[p, q]` and `[p, ..rest]`, `[p, ..]` (which
  ignores the rest), and annotated patterns.

## 13. Display

A value displays as a program that rebuilds it. The REPL appends ` : T`
**exactly when** re-reading the text alone would not recover the type `T`.
This is the minimal-annotation rule.

- **Numbers and nimbers:** `7`, `*15 : Nimber`, `*6` (a game), `2 : Game`,
  `1/2`, `3⋅ω↑2 - ω + 5`.
- **Games:** recognized integers, dyadics, nimbers, `up`, and `down`;
  otherwise braces with canonical options in structural order: `{2 | 0}`,
  `{0 | {0, *1 | 0}}`.
- **Forms:** finite forms render as built, with the same recognition. Cyclic
  forms render as self-contained equation systems:
  - names are reused from their source only when the session does not bind
    them to a different graph, and otherwise synthesized as `g1, g2, …`
    against every binding in scope;
  - a single equation at top level is a statement, `on =: {on |}`;
  - a system, or any nested display, names its root:
    `(a =: {b |}; b =: {| a}; a)`.
- **Polynomials and fields:** `t↑2 + 1 : F5[t]` and `x↑2 : F8` (the
  annotation binds the generator); rational functions show as `(num)/(den)`.
- **Multivectors:** `(alg := clifford([*1, *1]); [e0, e1] := basis(alg); e0∧e1)`;
  a grade-0 multivector shows as its scalar with its type.
- **Closures:** a sequence binding their captured free variables, then the
  lambda: `(k := 10; x ↦ x + k)`. Recursive groups render as their system:
  `(fact =: n ↦ …; fact)`.
- **Rulesets, evidence, and samples:** rulesets as `impartial(…)`,
  `partizan(…, …)`, or `octal([…])`; claims as `verify(…) /* claim: … */`;
  bounded answers as `bounded(…, n)`; quotients as `quotient(…)`.

Data-type values rebuild in a session that has the same declarations.

## 14. Errors

`GrundyError { kind, span, message, hint }`. Corrective guidance lives in the
hint, never in the message tail.

| kind | trigger |
|---|---|
| `E_Parse` | grammar violations, with teaching hints (`!=`, barless braces, chained relations, `*` as a product, a conditional as an operand, `f(x) := …`, a discarded value before `;`) |
| `E_Reserved` | `↑↑`, `O(` |
| `E_Type` | types that do not unify, or a missing instance; hints name the bridge (`game(n)`, `form(g)`, `canon(f)`) or the class fact (nimbers are `*3`; games are a group) |
| `E_Ambiguous` | no default satisfies a variable's constraints |
| `E_Unbound` | an unknown name, constructor, or type; hints for `t`, `x`, `ω`, and uppercase variables |
| `E_Shadow` | a binder repeated within one pattern or system, or a duplicate constructor |
| `E_Arity` | a call or constructor pattern with the wrong argument count |
| `E_Pattern` | a refutable binding or `match` that matches nothing |
| `E_Fixpoint` | a recursive binding with no recursion theory at its type |
| `E_Unfounded` | an unguarded game equation |
| `E_Domain` | an operand outside an operation's domain: a non-dyadic game, a non-nimber value given to `nimber`, `sg` on a partizan ruleset, an index out of range, an invalid octal digit |
| `E_NotInvertible`, `E_DivisionByZero`, `E_Overflow`, `E_KummerEscape`, `E_Modulus`, `E_CnfOrder`, `E_GeneralMetric`, `E_AlgebraMismatch`, `E_DimMismatch`, `E_BladeIndex` | the partial operations of §7 |
| `E_Loopy` | a value relation beyond stoppers (naming the cycle), `canon` or `birthday` of a cyclic form, a component cycle in `value` or `sg`, a misère cycle |
| `E_Refuted` | evidence failing its check, naming the condition |
| `E_Fuel`, `E_StackDepth`, `E_GraphBudget` | the budgets of §6 |

## 15. REPL and files

`cargo run -p grundy --example repl` starts a session. The commands are
`:type e` (the generalized type), `:env`, `:fuel [n]`, `:graph [n]`, `:help`,
and `:quit`. Input that differs from its canonical form is echoed
canonically. A piped `.og` file is a sequence of statements with the same
continuation rules.

## 16. Conformance

1. **Corpus vectors** — [`conformance.txt`](conformance.txt): hand-checked
   statements with canonical echo, display, and error kind, message, and hint.
   The harness is `tests/conformance.rs`. Expected values were verified
   independently of the implementation, including OEIS Grundy sequences.
2. **Law tests** — `tests/laws.rs`:
   - stopper relations against an independent survival oracle;
   - negation rotation and operand swap of outcome cells;
   - loopy displays rebuilding `≡`-equal values in fresh sessions;
   - every display a fixed point;
   - `value = *sg` on random rulesets;
   - winning moves against the presented sum-state graph;
   - certified outcomes agreeing with direct outcomes;
   - fraction literals agreeing with division, failures included.
3. **Unit and engine tests** — the parse/unparse identity, type inference,
   and the engine's certificate tests: on seeded graphs, certificates verify
   and agree with the existing solver, and single-label forgeries are
   rejected.
