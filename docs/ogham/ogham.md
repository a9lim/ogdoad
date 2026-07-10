# ogham — the ogdoad expression language

Status: **v0.3.5 implemented** (spec'd 2026-07-09 at the reflection pass —
a9 + fable, four-perspective review with the codex seat; built 2026-07-09/10,
sol over the gaslamp `ogham-v35` thread in six gated stages, fable gating).
For the language this document is the implementation contract: every
decision either cashes out as a vector in
[`docs/ogham/conformance.txt`](conformance.txt) or it is not really
decided ([`conformance_v0.3.5.txt`](conformance_v0.3.5.txt) is the merged
staging file, retained as provenance). Implementing agents work until the
corpus is green; judgment calls go back to the spec, not into the code.

**Release gate:** 0.3.5 is followed by **0.3.6 — a second comprehensive
adversarial pass** (fresh session, fresh eyes, same four-perspective +
codex discipline; chartered in `docs/CONTINUATIONS.md` as `ogham-0.3.6`)
**before any release**. The reflection pass found five real defects in a
shipped, conformance-green language; the honest inference is that one pass
is not enough. Release scoping (front door vs `ogham` crate, the public
name) is deferred to that session.

File extension `.og`. The name: og(doad) + the ancient stroke-script —
fitting a language whose operators are strokes and ticks (`*`, `↑`, `∧`,
`⋅`, `/`, `#`, `‿`).

---

## 1. Identity

ogham is a **lisp for games with weird numbers**: a small language whose
data model is Conway's ontology and whose computation model is as thin as
the data model is rich. Most languages are the other way around —
elaborate control, impoverished numbers. ogham inverts the profile. The
values are the richest objects in the language (nimbers addressed by
ordinals, Hahn-series surreals, multivectors over either, game forms over
everything); computation is exactly three things — substitution you can
see, one equation binder, and non-strictness exactly where the mathematics
never looks. In the algebraic worlds ogham is a coordinate calculus over
unusually rich scalars; in the game world it becomes a first-order
recursive-equation language; the two faces share one fenced grammar, one
canonical executable display, and explicit boundaries.

Because the values are rich, the language needs almost no machinery to be
expressive: mex and Grundy are four lines of user code, not primitives.
Because computation is thin, every construct can afford to coincide with a
piece of mathematics. The coincidences are the language:

- **The cons cell and the game form are one constructor.** `{h | t}` read
  with singleton sides is Lisp's pair; nil is `{|}` = `0` — *list
  exhausted, game ended, additive identity* are one object. This is a
  productive structural coincidence, stated as such (claim level:
  interpretation): the deeper true reading is that a proper list is a
  *polarized game* — Left selects the head, Right advances the tail, and
  negation swaps the reader's roles.
- **The relation set is the outcome partition.** The four value relations
  `= < > ∥` are the four cells of the finite CGT order; relate a game to
  `0` and you have read out its outcome class. There is no `≠` because
  the partition has no fifth cell. Where draws exist the partition grows
  to nine cells and the notation grows with it — the outcome relations of
  §10.6, whose glyphs *are* the 3×3 outcome grid.
- **`=:` is the equation binder — one glyph, two polarities.** Written to
  a function it unfolds inductively under fuel; written to a game Element
  it closes coinductively into a finite cyclic graph — Siegel's loopy
  games are recursive equations, and ogham writes them as such
  (`on =: {on |}` is the textbook definition, verbatim). Assignment `:=`
  flows the past in; `=:` states an equation the name satisfies. The
  notation mirror is the semantics; the polarity is decided by the sort.
- **Non-strictness sits exactly where the mathematics never looks.**
  Ternary branches and the right operands of `and`/`or` (play one
  branch); the right operand of `⧺` (coinduction never reaches it until
  the left spine ends). The list is exhaustive.
- **Partiality is attributable.** A program terminates or errors with the
  mathematics in the message — `E_KummerEscape` naming the tower,
  `E_NotInvertible` naming the remainder, `E_Fuel` naming the μ that
  struck zero — never a silent hang, never a coerced answer. Where
  non-termination *has* a mathematical value — loopy games, draws — it is
  a value, not an error.
- **Two containers, one glyph, one per pillar.** `[…]` is the world's
  native container: in the Clifford worlds the world-fixed coordinate
  array (bulk algebra, random access); in the game world the free cons
  spine (option descent, μ/coinduction). The ring/group divide — the
  repo's founding scope boundary — reappears as fixed-shape-with-algebra
  vs free-shape-with-recursion. (An architectural rhyme, not a theorem.)

The discipline (unchanged since v0.1, in service of the identity above):

1. **Weird numbers first.** Scalar literals are the richest part of the
   grammar. `*` belongs to nimbers, not to multiplication.
2. **Two display laws.** `parse ∘ unparse = id` on ASTs, and
   `eval ∘ parse ∘ display ≃ value` — structural `≡` for game forms,
   α-equivalence for recursive equations. Display emits canonical ogham;
   the parser's input language is a superset. Every value's display is a
   program that rebuilds it, up to and including loopy values, which
   display as the equations that define them.
3. **Two layers: canonical and sugar.** Canonical uses the unicode math
   glyphs where ASCII is contested (`ω ↑ ∧ ⋅ ∥ ↦ ⧺ ≡ ‿`); ASCII stays
   canonical where it is uncontested (`* e # + - / = := < > > < [ ] ( )`
   and the four ASCII outcome corners `>> >< <> <<`, plus `|` as the
   structural braceform bar — its only role). Sugar is input-only; the
   REPL echoes canonical (the REPL is the tutor).
4. **Context is fenced, never guessed.** A world declaration chooses the
   laws; `*(…)` and `#(…)` and `{… | …}` visibly fence structural
   subgrammars; sort positions are explicit in the grammar. No
   juxtaposition anywhere, no coercions, no inferred worlds.
5. **One active world at a time.** Mixing is a parse/eval-time error,
   never a coercion.
6. **Display never canonicalizes.** Forms display as built (up to
   presentation, §10.1); value identity is said with `=` or `canon`.
7. **Errors are mathematical content.**
8. **Pure Rust, zero deps, no pyo3 outside `src/py/`** (core rule 1).

Non-goals, permanent: quote/macros (code-as-data would blur the
structural/arithmetic fence the grammar fights hardest to keep); mutation,
I/O, strings (rebinding is the only state, the REPL the only effect);
floats; juxtaposition; coercions. Transfinite/ω-length games: out — the
game world is the finite-graph pillar.

## 2. Symbols and codepoints

| meaning | canonical | codepoint | ASCII sugar | notes |
|---|---|---|---|---|
| omega | `ω` | U+03C9 | `w` | atom; also inside star-literals |
| power | `↑` | U+2191 | `^` | right-assoc; Knuth's arrow |
| wedge | `∧` | U+2227 | `&` | exterior product |
| product | `⋅` | U+22C5 | `.` | the algebra's product; U+00B7 `·` also accepted on input |
| nimber prefix | `*` | — | — | value marker in nim-worlds (§7.3) |
| index prefix | `#` | — | — | meta-integer marker (§7.6): `#5`, `#(2⋅3)`; mirrors `*` — one marks the world's address, one the spectator's integer |
| blade prefix | `e` | — | — | `e0`, `e1`, … basis 1-blades |
| neg / sub | `-` | — | — | unary and binary |
| recip / div | `/` | — | — | unary and binary |
| add | `+` | — | — | |
| remainder | `%` | — | — | Euclidean / CNF-truncation remainder (§8.3) |
| evaluate | `@` | — | — | substitution/application, binds tightest (§8.4) |
| equality | `=` | — | `==` | Bool-valued value relation (§8.5, §10.6) |
| less / greater | `<` `>` | — | — | Bool-valued strict order relations |
| fuzzy | `∥` | U+2225 | `!` | incomparable, CGT ∥ — sugar is `!` (was `\`, retired with prefix factorial; `a != b` earns a hint: not-equal is `not (a = b)`) |
| draw atom | `‿` | U+203F | `_` | the undertie — the tie glyph; occurs only inside outcome doubles (§10.6); a lone `‿` errors with "mover-result atoms come in pairs" |
| outcome relations | `>> >‿ >< ‿> ‿‿ ‿< <> <‿ <<` | — | `_`-forms | the nine-cell grid as its own glyphs (§10.6); game world only |
| structural equality | `≡` | U+2261 | `===` | relop tier, non-chaining; game world only (§10.5) |
| append | `⧺` | U+29FA | `++` | right-assoc, looser than `+ -`, tighter than relations; game world only (§10.4) |
| game form | `{L\|R}` | — | — | braces are real; `\|` and `,` structural inside; the bar is mandatory (barless braces died with the container move, §10.3) |
| container | `[a,b,c]` | — | — | the world-shaped container (§7.8): Clifford coordinates / game spine; `[]` is nil in the game world |
| binding | `:=` | — | — | `name := expr`; rebinding allowed |
| fixpoint binding | `=:` | — | — | the equation binder (§9); munches before `=` |
| lambda | `↦` | U+21A6 | `~` | first-order Function value (§6) |
| ternary | `? :` | — | — | lazy condition; full-expression branches, right-assoc nesting (§4) |
| bool words | `and or not` | — | — | lazy word operators; reserved |
| comment | `//` and `/* … */` | — | — | line and block; block comments nest; `#` is the Index prefix now |
| vector … | | | | *(the word "vector" survives only in Clifford-world prose; the syntax is the container)* |

Reserved, must lex but reject with `E_Reserved`: `↑↑` and `O(` (precision
tails). The name `t` is reserved only inside poly/ratfunc worlds (the
indeterminate); `x` inside `f*` worlds (the field generator).

**Unary-fill principle**: a unary form of a binary operator fills the left
operand with the operator's identity. `-a = 0 - a`, `/a = 1/a`. Only the
two inverse-taking operators have unary forms; no other operator gets one.

## 3. Lexical structure

- Tokens are self-delimiting; there are **zero juxtaposition rules**.
  Whitespace separates tokens but is never semantic.
- `INT`: `[0-9]+`, value must fit `u128`. No sign (sign is unary `-`); the
  one exception is a tight signed exponent immediately after `↑` (§4).
- `IDENT`: `[a-z][a-z0-9_]*`, excluding reserved words. Reserved
  everywhere: `w`, `and`, `or`, `not`, the literal atoms
  (`true false up down dim`), and stdlib function names (§11).
  Interior `_` stays identifier material: `foo_bar` is an IDENT; the
  draw atom is only recognized where an IDENT cannot start.
- `e` followed immediately by digits lexes as a BLADE token. `e` alone is
  an error. `*` followed by anything lexes as the STAR prefix; `*` is
  never infix. `#` followed by an INT or `(` lexes as the
  INDEX prefix; `#` is never infix and no longer opens a comment.
- Comments: `//` to end of line; `/* … */` nesting block
  comments. Both are whitespace to the lexer. The sequence `/*` always
  opens a comment, so the reciprocal of a star-literal takes parens:
  `/(*2)` — display emits the parenthesized form (the one place comment
  syntax touches canonical output).
- Sugar substitution happens in the lexer: `w→ω`, `^→↑`, `&→∧`, `.→⋅`,
  `·→⋅`, `!→∥`, `==→=`, `~→↦`, `++→⧺`, `===→≡`, `_→‿`, and the
  `_`-spelled outcome doubles (`>_ → >‿`, `_> → ‿>`, `<_ → <‿`,
  `_< → ‿<`, `__ → ‿‿`). After the lexer, only canonical tokens exist.
- Multi-char tokens munch longest-first and require adjacency: `=:`
  before `=`, `===` before `==`, `++` before `+`, the nine
  outcome doubles before the relational singles (`>>` before `>`, `<>`
  before `<`, …). `a + + b` stays `E_Parse`; `a > > b` stays two tokens
  and errors as chained relations.
- The braceform bar is not a relation: `|` is canonical as the structural
  separator and has no relop reading (a relop-tier `|` earns the §13
  hint), and `∥` is refused as the bar in turn.
- `!` lexes to `∥`. The sequence `!=` therefore lexes as `∥`
  `=` — ungrammatical, and the error carries the hint: "not-equal is
  `not (a = b)`; `!` is fuzzy `∥`".

## 4. Grammar (EBNF)

Statements (one per line at depth 0; blank and comment-only lines are
no-ops; the lexer consumes continuation lines while `(`/`[`/`{` are
unbalanced):

```ebnf
statement   = binding | expression | lambda ;
binding     = IDENT (":=" | "=:") ( lambda | expression ) ;
lambda      = binders "↦" expression ;        (* ↦ grabs maximally rightward *)
binders     = IDENT | "(" IDENT { "," IDENT } ")" ;
sequence    = { binding ";" } statement ;     (* top level; bodies via parens *)

expression  = orexpr [ "?" expression ":" expression ] ;   (* full branches, right-assoc *)
orexpr      = andexpr { "or" andexpr } ;
andexpr     = notexpr { "and" notexpr } ;
notexpr     = { "not" } relexpr ;
relexpr     = catexpr [ relop catexpr ] ;     (* relations not chainable *)
relop       = "=" | "<" | ">" | "∥" | "≡"
            | ">>" | ">‿" | "><" | "‿>" | "‿‿" | "‿<" | "<>" | "<‿" | "<<" ;
catexpr     = additive [ "⧺" catexpr ] ;      (* right-assoc via recursion *)
additive    = mulexpr { ("+" | "-") mulexpr } ;
mulexpr     = wedge   { ("⋅" | "/" | "%") wedge } ;
wedge       = unary   { "∧" unary } ;
unary       = { "-" | "/" } power ;
power       = appl [ "↑" exponent ] ;         (* right-assoc via recursion *)
appl        = atom { "@" applarg } ;          (* left-assoc *)
applarg     = atom
            | "(" expression { "," expression } ")" ;  (* argument frame, not a value *)
exponent    = [ "-" ] INT | IDENT
            | "(" expression ")" ;            (* Index sort; Scalar iff base is ω in surreal-family worlds *)
atom        = INT | starlit | indexlit | "ω" | BLADE | container | braceform
            | call | IDENT | "true" | "false" | "up" | "down" | "dim"
            | "(" lambda ")" | "(" sequence ")" | "(" expression ")" ;
container   = "[" [ expression { "," expression } ] "]" ;
braceform   = "{" [ optlist ] "|" [ optlist ] "}" ;          (* bar mandatory *)
optlist     = expression { "," expression } ;
call        = IDENT "(" [ arglist ] ")" ;
arglist     = expression { "," expression } ;

starlit     = "*" ( INT | "ω" | "(" cnf ")" ) ;
indexlit    = "#" ( INT | "(" expression ")" ) ;             (* Index-sorted interior *)
cnf         = cnfterm { "+" cnfterm } ;       (* strictly descending exponents, else E_CnfOrder *)
cnfterm     = INT | "ω" [ "↑" cnfexp ] [ "⋅" INT ] ;
cnfexp      = INT | "ω" | "(" cnf ")" ;
```

Notes:

- **Star-literals are structural, not arithmetic.** Inside `*(…)` the
  symbols `+ ⋅ ↑` build a CNF ordinal *index* (the nimber's address in
  On₂); they do not evaluate. `*(ω + 1)` is the nimber at ordinal ω+1;
  `*ω + *1` is a nim-sum that happens to equal it. Unparenthesized star
  applies only to `INT` and bare `ω`; the star binds tighter than `↑`
  (`*ω↑2 = (*ω)↑2`).
- **Index-literals are the meta mirror**: `#5`, `#(2⋅3)`. The
  interior is an Index expression (`+ - ⋅ ↑`, parens). `*` marks an
  Element address; `#` marks the spectator's integer. Bare `INT` remains
  input sugar at Index-*forced* positions (exponents, stdlib I-slots);
  display marks Indexes minimally (§12.4).
- The surreal-family worlds allow CNF **at expression level, unstarred
  and live**: `3⋅ω↑2 - ω + 5` is ordinary arithmetic over monomials.
- **Ternary**: condition Bool-sorted; branches are full
  expressions agreeing in sort; nesting is right-associative and
  parens-free (`a ? b ? c : d : e` = `a ? (b ? c : d) : e` — the then-arm
  binds greedily; relations, boolean words, appends, and nested
  ternaries all sit in branches bare).
- Relations stay non-chaining. A parenthesized relation is a Bool atom.
- **Multi-param application is an argument frame** — `b@(u, v)`,
  arity-checked; not a value, not a container, cannot be bound. One-param
  keeps the atom rule: `f@7`, `f@(u + 1)`. No currying.

## 5. Precedence (tight → loose)

```text
atoms:  INT, *‹i›, #‹i›, ω, e‹i›, […], {L|R}, f(…), true/false/up/down/dim, (…)
@            evaluation/application, left-assoc; operands atoms/frames
↑            power, right-assoc; tight signed INT exponent ok (ω↑-1)
unary - /    neg, reciprocal
∧            wedge
⋅  /  %      product, division, remainder, left-assoc
+  -         add, subtract
⧺            append, right-assoc (game world)
relations    = ≡ < > ∥ and the nine outcome doubles — non-chaining, one per relexpr
not
and
or
? :          ternary, right-assoc, full-expression branches
↦            lambda, grabs maximally rightward
```

Wedge tighter than `⋅` follows Hestenes. Display v3 relies on the blade
row: blade terms print unparenthesized (`*3⋅e0∧e1`).

**Host-language caveat** (§15): Rust and Python cannot reproduce this
table for the overloaded operators. The precedence above is ogham's, full
stop; host code parenthesizes.

## 6. Sorts

ogham has **three first-order data sorts** — **Element** (the world's
values: multivectors, polynomials, game forms), **Index** (meta-integers,
`i128`), **Bool** (verdicts) — plus **closed Function abstractions**,
which may be bound, displayed, composed, and applied but not passed,
returned, or stored. Position determines sort; there are no coercions.

- **Function** = a binder-AST, closed over its own binders by
  substitution at definition time (§8.6). The first-order discipline is
  one rule: a Function-sorted term appears only as (a) the RHS of
  `:=`/`=:`, (b) an operand of `@`, (c) a whole statement. Everything
  else is `E_FnSort`. (Higher-order is 0.4.0's opening gate, §18.)
- **Bool** positions: ternary conditions, `and`/`or`/`not` operands,
  binding RHS, statement position, lambda bodies. Banned in containers,
  arithmetic, and exponents: `E_BoolSort`.
- **Binder sorts are inferred per binder** from occurrence positions;
  conflicts are `E_IndexSort`/`E_BoolSort` *at definition*. The flagship:
  `gold := (a, u) ↦ tr(u ⋅ u↑(2↑a))` infers `a : Index`, `u : Element`.
- Bindings bind any sort; a bare statement of any sort evaluates and
  prints. An Index value *stays* Index through capture,
  binding, and application — the substituted literal is `#n`, so the
  sort is visible and the round-trip exact (this repairs the 0.3.0
  defect where capture lowered Index to Element).

## 7. Worlds and literals

A session holds exactly one world plus environment (cleared on `:world`).
Clifford-capable worlds monomorphise a scalar backend into a
`CliffordAlgebra<S>`; the function-shaped worlds are polynomial/ratfunc
evaluators; the game world is the first non-scalar world. Declaration:

```text
:world ‹name› ‹dim› q=[s0,…] [b=[(i,j):s,…]] [a=[(i,j):s,…]]
:world ‹name› ‹dim› grassmann
:world nimber gold(m,a)
:world ‹name› 0
:world ‹poly/ratfunc name›
:world game
```

`q`/`b`/`a` mirror `Metric::diagonal`/`::new`/`::general`. Declaring
`a≠∅` warns that `rev`/`dual` are unavailable (`E_GeneralMetric`).
`dim ≤ 128`. World declarations parse under the same host
guards as statements (§17.2) — a pathological metric literal is an
honest `E_Parse`, never a host abort.

### 7.1 The world menu (fixed dispatch)

| world name(s) | backend | field? | notes |
|---|---|---|---|
| `nimber` | `Nimber` (u128) | yes | F_{2^128} |
| `ordinal` | `Ordinal` | partial | Kummer-checked (§8.2) |
| `surreal` | `Surreal` | partial | monomial inverses only |
| `omnific` | `Omnific` | no (units ±1) | |
| `integer` | `Integer` (i128) | no (units ±1) | |
| `fp2 fp3 fp5 fp7` | `Fp<p>` | yes | |
| `f4 f8 f16 f9 f27 f25` | `Fpn<p,n>` | yes | generator `x` |
| `poly2 poly3 poly5 poly7` | `Poly<Fp<p>>` | no | `F_p[t]`, function-shaped |
| `polyint` | `Poly<Integer>` | no | `ℤ[t]`, monic division boundary |
| `ratfunc2 ratfunc3 ratfunc5 ratfunc7` | `RationalFunction<Fp<p>>` | yes | `F_p(t)` |
| `game` | `games::Game` + loopy graphs | no (group) | forms, lists, loopy values; no metric, no blades |

Further out: precision worlds (`O(p^k)` literals are their own iteration).

### 7.2 Bare `INT` at Element position (the `from_int` trap)

`Scalar::from_int` is the ℤ-ring map — in char-2 backends `from_int(3) = 1`.
Literal meaning is defined per world and **never** via `from_int` in
nim-worlds:

| world | bare `INT` at Element position |
|---|---|
| `nimber`, `ordinal` | error `E_BareInt`, hint `did you mean *3?` |
| `surreal`, `omnific`, `integer` | exact integer |
| `fp*`, `f*` | residue |
| `poly*`, `polyint`, `ratfunc*` | constant polynomial / rational function |
| `game` | the integer game — the canonical CGT embedding; the one world where bare-literal `from_int` is honest |

Bare `INT` at Index-forced position is a meta-integer in every world;
elsewhere `#n` says so explicitly (§7.6).

### 7.3 Star-literals

- `nimber`: `*n` = `Nimber(n)`; bare `*` is sugar for `*1` (canonical
  prints `*1`).
- `ordinal`: `*n`, `*ω`, `*(cnf)`; the star is the value marker; there
  are no unstarred Element literals in this world. Bare `ω` is
  `E_BareOrdinal` (hint: `*ω`).
- `game`: `*n` is the nimber game in standard form; bare `*` is `*1`.
- All other worlds: `E_WrongWorld`.

### 7.4 Other scalar literal forms

- `ω` atom: `surreal`/`omnific` — `Surreal::omega()`.
- Dyadic/rational values are spelled with division: `1/2` (the field
  operation *is* the literal; non-exact division errors honestly).
- `f*` worlds: generator `x`; elements are reached arithmetically.
- `e‹digits›` blades: `alg.e(i)`, `E_BladeIndex` if `i ≥ dim`.
- poly/ratfunc: reserved `t`; fractions print `(num)/(den)`.

### 7.5 Literal atoms

`true`/`false` (Bool, every world); `up`/`down` (game world: the standard
forms `{0 | *1}` and `{*1 | 0}`; `E_WrongWorld` elsewhere); `dim` (Index:
the world's dimension in Clifford worlds, `#0` in dim-0 worlds,
`E_WrongWorld` in function and game worlds). The 0.3.0 call forms
`up()`/`down()`/`dim()` are gone — no nullary calls exist; the old
spellings earn hints. `-up ≡ down` holds structurally (nimber forms are
self-negative), so the literal family is closed under negation for free.

### 7.6 Index-literals

`#5`, `#(2⋅3 + 1)` — the Index sort made audible. Two prefix markers, two
sorts: `*` is the world's address, `#` is the spectator's integer. Input
may still write bare ints where the position forces Index; canonical
display marks exactly the positions that don't (§12.4).

### 7.7 The game world's literals

Bare `INT` = the integer game; `*n` = the nimber game; `up`/`down`; `[…]`
lists (§7.8); `{L | R}` forms (§10). `ω`, blades: `E_WrongWorld`.

### 7.8 The container

`[a0,…,a(n-1)]` is the world's native container — one glyph, two shapes:

| | Clifford worlds | game world |
|---|---|---|
| shape | fixed: length must equal `dim` (else `E_DimMismatch`); `[]` legal only at `dim 0` (the empty sum) | free: any length; `[]` is nil `= {|} = 0` |
| builds | `Σ aᵢ⋅eᵢ` (grade-1) | the right-nested spine `{a0 | {a1 | … {a(n-1) | 0}…}}` |
| access | random: `coef(v, i)` | sequential: option descent (`left`/`right`) |
| algebra | `+` is zip-with-add; `⋅` exists (ring) | `+` is game sum, **not** append; `⋅` is `E_WrongWorld` (group) |
| iteration | Index recursion, bounded by `dim` | μ-recursion / coinduction |

Function worlds: `E_WrongWorld`. Braces take no part in list sugar
anymore: `{a, b}` without a bar is `E_Parse` with the hint
"`[a, b]` is the list; braces are game forms `{L | R}`" — the 0.3.0
missing-bar footgun is structurally dead.

## 8. Semantics

Evaluation is strict, left-to-right, **except** the non-strict positions
(§1): ternary branches, `and`/`or` right operands, and the right operand
of `⧺` (evaluated only if the left walk reaches nil, §10.4). Bindings
live in a per-world environment. A bare expression statement evaluates
and prints canonical display; non-canonical input is first echoed
canonically (the unparser).

### 8.1 Operator → engine desugaring

| ogham | engine call |
|---|---|
| `a + b` | `Multivector::add`; game world: disjunctive sum (form-level materialization; total on loopy operands via the product graph, §10.7) |
| `a - b`, `-a` | `sub`/`neg` — scalar `neg()` underneath, never literal −1 (core rule 3); game world: game negation (total on loopy operands — the L/R graph swap) |
| `a ⋅ b` | `alg.mul`; game world `E_WrongWorld` (group, not ring) |
| `a ∧ b` | `alg.wedge`; game world hint points at `⧺` |
| `a / b` | `a ⋅ inv(b)` — right division; at grade 0 in non-field worlds, exact division (unique `x` with `x ⋅ b = a`), remainder named on failure |
| `/a` | `Scalar::inv` / `multivector_inverse`; `None → E_NotInvertible` |
| `a % b` | per-world remainder (§8.3) |
| `f @ v` | substitution/application/composition (§8.4) |
| `a ↑ k` | iterated `alg.mul`; `a↑0 = 1`; `a ↑ -k = (/a) ↑ k` |
| `ω ↑ s` | Hahn monomial constructor (surreal family; base exactly ω) |
| `[…]` | §7.8 |
| relations | §8.5, §10.6 |

### 8.2 Partiality (the honest edges)

| operation | behavior |
|---|---|
| `ordinal` mul/inv past the verified Kummer tower | `E_KummerEscape` ("below ω^(ω^ω), primes ≤ 709 — see docs/OPEN.md") |
| `surreal` inverse of a non-monomial | `E_NotInvertible` ("only CNF monomials invert exactly; 1/(ω+1) is an infinite Hahn series") |
| `integer`/`omnific` non-unit inverse, non-exact division | `E_NotInvertible`, remainder named |
| `/0`, `% 0` | `E_DivisionByZero` |
| grassmann/degenerate inverses | `E_NotInvertible` |
| μ-unfolding past the budget | `E_Fuel` (§9.2) |
| materialized graphs past the node budget | `E_GraphBudget` (§10.7, §17.2) |

### 8.3 `%` — remainder (the integrality column's operator face)

| world | semantics |
|---|---|
| `integer` | Euclidean remainder, `0 ≤ r < \|b\|` (`-7 % 3 = 2`) |
| `surreal`, `omnific` | `b` must be a monic ω-power `ω↑e` (else `E_Modulus`); result is the CNF tail strictly below `e` — the Hahn mirror of dropping high digits mod `10↑k`. Non-monic moduli rejected deliberately: every nonzero constant is a unit of No, so `7 % 3` would honestly be `0` — a footgun beside the integer world's `1` |
| poly worlds | `Poly::divrem`; `polyint` divisors monic |
| any field world, `game` | `E_WrongWorld` — a field divides exactly; returning the silent `0` would mislead |

The Euclidean identity is expressible: `(a - a%b)/b ⋅ b + a%b = a`.

### 8.4 `@` — the one application operator

`f@v` substitutes into the hole — `t` in the function worlds, the binders
of a Function — through the substitution homomorphism. Composition is the
non-constant case and is associative: `f@g@x = (f@g)@x = f@(g@x)`.
Engine: `Poly::eval`/`::compose`; ratfunc evaluates `num`/`den`
separately (a pole is `E_DivisionByZero`). Functions: sort-checked
substitution then strict evaluation (§8.6). `@` binds tightest; both
operands are atoms or frames. Non-function scalar worlds reject `@` with
`E_WrongWorld`; **the grammar is world-independent** — literal *forms*
parse everywhere, worlds decide legality at evaluation (the fence
principle).

### 8.5 Relations and binding

A relation is a Bool-valued expression (usable anywhere Bool is legal;
relations stay non-chaining). `=` is value equality in every world
(`PartialEq`; game world: canonicalize-and-compare, §10.6). `<`, `>`,
`∥` are the strict, strict-reversed, and incomparable cells of the
world's canonical partial order, grade-0 only:

| world | order | consequence |
|---|---|---|
| `integer`, `surreal`, `omnific` | the ring's total order | `∥` identically `false` |
| `nimber`, `ordinal` | the game-value order restricted to nimbers — an antichain plus equality | `<`/`>` identically `false`; `a ∥ b ⟺ a ≠ b` |
| `fp*`, `f*`, function worlds | none | `< > ∥` are `E_WrongWorld` |
| `game` | the full CGT partial order | all four cells live; §10.6 for loopy operands and the nine outcome doubles |

Index relations (`= < >`) are the meta-integer total order; Bool `=` is
Bool equality; `f = g` on Functions is `E_FnSort` (function equality is
extensional and not ogham's to decide).

Binding is `name := expr` (any sort; rebinding allowed). An unbound bare
identifier left of a top-level `=` earns "did you mean `name := …`?".

### 8.6 Capture by substitution; sequences

A Function value is a **closed AST over its own binders**, produced by
substitution at definition time. No runtime environments, ever. Captured
Element/Index/Bool bindings substitute in as values (visibly — the echo
shows them; Index captures substitute as `#n`); captured
Functions beta-reduce, so a Function value never references another
function. Definition-time checking is complete: sorts, arities,
shadowing, unbound names, world-legality of every operator. The only
application-time failures are §8.2's partiality and the budgets.

Shadowing: binders may not shadow reserved words, stdlib names, or the
world's generator (`E_Shadow`); duplicate binders are `E_Shadow`; binders
may shadow ordinary bindings.

Sequences: `{ binding ";" } statement`. Intermediates must be bindings
(`E_SeqValue` — with no effects a discarded value is dead code). At top
level, bindings persist and only a final expression prints; a
parenthesized sequence is an expression form (`f := n ↦ (d := n⋅n;
d + 1)`) — `:=` *is* the let. Display preserves let-structure
(closedness, not flatness, is the invariant).

## 9. Recursion — `=:` and fuel

### 9.1 The equation binder

`name =: rhs` binds `name` to a solution of the equation `name = rhs`,
with `name` in scope symbolically on the right. **One glyph, two
polarities, decided by sort**:

- **Function `=:`** — operational recursion: the body unfolds at call
  sites under fuel. `fact =: n ↦ (n = 0 ? 1 : n⋅fact@(n-1))`. No
  denotational fixpoint claim is made; the semantics is unfolding plus an
  attributable budget.
- **Element `=:`** (game world only) — **guarded coinductive graph
  formation**: the equation closes into a finite cyclic game graph, read
  up to bisimilarity (§10.7). `on =: {on |}` *is* Siegel's equation for
  on. Everywhere else an Element self-mention is `E_WrongWorld` — no
  fixpoint theory, no fixpoint syntax (`x =: x + 1` names nothing in ℤ).

Shared rules: `=:` with no self-mention degenerates to `:=` exactly.
`:=` with a self-mention stays `E_Unbound` (hint: "recursive definition?
`=:`"). Local `=:` is allowed in body sequences for both polarities; a
local helper may reference the enclosing μ-name and binders (this covers
most mutual shapes; true mutual groups are 0.4.0, §18). A top-level
Function value carries at most one free name — its own; the bare-name
echo prints the equation form.

### 9.2 Fuel — steps, not depth

Fuel meters **total μ-unfoldings** — every substitution of a μ-bound body
into its call site, all μs draining one shared budget, reset per
top-level statement. Exceeding it is `E_Fuel`, naming the μ that struck
zero and the budget. Depth budgets don't deliver the honesty claim
(`fib@100` has depth ~100 and ~φ¹⁰⁰ unfoldings). Default budget
**2¹⁶ = 65536**; `:fuel n` is the REPL knob; `@fuel n` the corpus
directive. Non-recursive applications are not metered (inlining means
they cannot loop); engine-internal recursion is not metered (terminates
by construction). Element-`=:` runs graph fixpoints, not descent — fuel
is untouched there, and a μ-*function* recursing along an infinite spine
(`len@ones`) is honestly `E_Fuel`.

## 10. The game world

`:world game` — Elements are game forms over the games pillar
(`games/partizan.rs::Game`) and, through Element-`=:`, finite cyclic game
graphs (`games/loopy/`). No metric, no blades. CGT is the recursive
subject; this is where the language and the repo's thesis converge.

### 10.1 The strata

The game world is stratified, and every operator's stratum is part of its
contract. Presentation is named as a stratum of its own:

- **presentation** — option *order* and *multiplicity* as entered.
  Display and indexed access (`left(g, i)`) live here. Never semantic.
- **form** — the constructors' quotient of presentation: sides as
  multisets of forms. `≡`, `⧺`, `hasdraw`, option counts, list structure
  live here. Form operations are **not** congruences for `=`
  (`{-1 | 1} = 0` yet `{-1 | 1} ⧺ l` is `E_Improper`) — this is the
  form/value distinction CGT itself is careful about, load-bearing for a
  future misère mode.
- **value** — the CGT quotient: `= < > ∥`, `canon`.
- **outcome** — who wins the compound under optimal play: the nine
  doubles (§10.6), `hasdraw`, `stopper`. Outcome and value coincide on
  finite forms by theorem and **split on loopy games** — the split is
  taught, not hidden (§10.6).

**`≡`, display recognition, and value keys quotient presentation
by multiset** — matching the engine's own order-independent structural
fingerprint. `{1, 2 | 0} ≡ {2, 1 | 0}` is `true`; `{0, 0 |} ≡ {0 |}` is
`false` (multiplicity is form data; `1 + 1` still displays `{1, 1 |}`).
On cyclic values `≡` is unordered bisimilarity of finite unfoldings
(α-invariant, decidable by synchronized descent with per-pair option
matching — bipartite perfect matching per node side; coinductive cycle
assumptions are branch-local, so a failed candidate match discards its
optimistic assumptions rather than leaking them; a cyclic graph never
compares `≡`-equal to a finite tree — a repeated graph node along the
synchronized path witnesses genuine cyclicity). This repairs the 0.3.0
defect where `≡` and recognition were order-sensitive and the retraction
law below was false.

### 10.2 Form display and recognition

Form display is structural and canonical: `{` + left options joined
`, ` + `|` + right options joined `, ` + `}`; single spaces separate the
bar from each nonempty side; `{|}`, `{0 |}`, `{1, 2 | 0}`. One carve-out,
now with a precedence chain: a form whose option multisets
match what a literal builds displays as that literal —

```text
integer chains → nimber standard forms → up/down → proper spines […] → raw braces
```

`{1 |}` displays `2`; `{0 | 0}` displays `*1`; `{0 | *1}` displays `up`;
`{7 | {8 | 0}}` displays `[7, 8]` — and so does `{5 | 0}` display `[5]`,
because a cons whose tail is nil *is* the one-element list. A form
displays as itself when it is no proper spine: the switch `{1 | -1}`
(the tail position holds `-1`, neither nil nor cons — an improper list,
legal as data, shown raw) or any multi-option side `{1, 2 | 0}`.
Recognition
is structural (multiset), never value-level: `1 + 1` materializes the sum
form and displays `{1, 1 |}`, not `2`. Value identity is said with `=` or
`canon`. Recorded delights (claim level: interpretation, all structural
identities): `[0] ≡ *1`, `[0, 0] ≡ up`, `down ≡ [*1]` — the uptimal
ladder starts inside list notation.

### 10.3 Lists — the cons-cell discipline

Cons is `{h | t}` (singleton sides; the bar distinguishes head from
tail); nil is `{|} = 0`; `[a, b, c]` is the container literal for the
right-nested spine and `[]` for nil (§7.8). A **proper spine** is nil or
a cons whose tail is a proper spine; everything else is Lisp's
dotted/improper case, legal as data. The accessors are a prelude, not
stdlib — definable in-language:

```text
hd := l ↦ left(l, 0)
tl := l ↦ right(l, 0)
isnil := l ↦ nleft(l) = 0 and nright(l) = 0   // structural — l = 0 is NOT a nil test
```

### 10.4 `⧺` — append, coinductively total on the left

`l ⧺ g` walks the left operand's right-spine. Three outcomes, exhaustive:
(1) the walk reaches nil — `g` is evaluated and grafted at the terminal;
(2) the walk cycles — the append **is the left operand** (`l ⧺ g = l`):
an infinite list never reaches its end, so the right operand is never
consulted — the coinductive identity, operational; (3) the walk hits a
node neither cons nor nil — `E_Improper` (improperness is orthogonal to
cyclicity). The right operand is evaluated *only* in case
(1) — `⧺` is one of the language's non-strict positions, so
`ones ⧺ (ones + 0)` is `ones`, not an error; the operational rule *is*
the coinductive rule. The right operand is unrestricted (grafting a
non-list gives an improper list — Lisp's last-argument freedom). Units:
`[] ⧺ l = l`, `l ⧺ [] = l`. Form-level, hence not a `=`-congruence. `+`
is **not** append; no operator concatenates arrays.

### 10.5 The second equality and `canon`

- **`a ≡ b`** — form equality: multiset-structural (§10.1), regular-tree
  bisimilarity on cyclic values. Bool-valued, relop tier, non-chaining.
  Outside the game world `E_WrongWorld`, not an alias for `=`: elsewhere
  forms *are* values and a silently-coinciding second equality would
  mislead (hint: "`=` is already structural here").
- **`canon(E) → E`** — the engine's canonical form (options
  canonicalized, dominated options deleted, reversible options bypassed).
  Finite forms only at 0.3.5 (`E_Loopy` on loopy values — fusion/simplest
  form is 0.4.0's last item, §18).
- The retraction laws, in the language and the corpus:

```text
a = b  ⟺  canon(a) ≡ canon(b)      // canon turns value equality into form equality
canon(canon(x)) ≡ canon(x)          // idempotent
canon(x) = x                        // value-preserving
```

- Cost inversion, noted: `≡` is the cheap walk; `=` is the expensive one
  (canonicalization). The default glyph is the costly one because the
  math owns `=`.

### 10.6 Relations — value singles, outcome doubles

The mover-result atoms are `>` (Left wins that instance), `<` (Right
wins), `‿` (draw — infinite play). An **outcome double** is two atoms —
*result when Left starts*, then *result when Right starts* — giving nine
relops that are the 3×3 outcome grid arranged as its own glyphs:

```text
                Right starts:   L wins    draw    R wins
Left starts:  L wins              >>       >‿       ><
              draw                ‿>       ‿‿       ‿<
              R wins              <>       <‿       <<
```

- **Doubles read the outcome of the formal conjugate sum** `G + (−H)`
  (conventionally written `G − H`; in loopy play `−H` is *not* an
  additive inverse — `G + (−G)` need not equal 0, which is exactly why
  this stratum exists). Total on **all** game operands, loopy included:
  the sum graph is finite, and its nine-cell outcome partition is
  computed by the standard retrograde attractor/draw analysis under
  optimal play — defined operationally: a player *wins* if they can
  force a finite win, the position is *drawn* for a mover who cannot
  force a win but can prevent a loss (infinite play is a draw; each
  player prefers win > draw > loss). Exactly one double holds for any
  pair. On finite forms the five `‿`-cells are identically false (the
  `∥`-in-ordered-worlds precedent). Game world only; `E_WrongWorld`
  elsewhere.
- **Singles are the value stratum, computed as a projection.** On finite
  forms, `= < > ∥` are the classical partition (unchanged). On loopy
  operands the singles require **both presented operands to be stopper
  graphs** — no reachable alternating cycle in the turn-expanded graph
  `(node, mover)`; one-sided pass loops (`over = {0 | over}`) *are*
  stoppers — and then project the double (standard math: Siegel,
  *Combinatorial Game Theory*, GSM 146, Thm VI.2.1 p. 290 with Def
  VI.1.8 p. 284 — `G ≥ H` iff Left, moving second, survives `G − H`,
  where surviving means winning or drawing):

```text
{>>, >‿} → `>`        {><} → `∥`        {<>, <‿, ‿>, ‿‿} → `=`        {‿<, <<} → `<`
```

  The gate is on the **operands, never their difference** — the sum of
  two stoppers need not be a stopper (`over + under`), and the theorem
  holds regardless. Beyond stoppers the singles are `E_Loopy`, and the
  error names the alternating turn-state cycle found and the operand
  side carrying it, rendered closed with the first state repeated
  (`left operand has alternating cycle 0:L→0:R→0:L`) — witness-carrying,
  the house style of `E_NotInvertible` naming the remainder. One-stopper biased
  comparison is future work (§18).
- **Refinement, not contradiction.** The doubles refine the singles: on
  stoppers `G = H` legitimately coexists with any of `<>`, `<‿`, `‿>`,
  `‿‿`. The teaching triple: `over = over` is `true` (survival);
  `over ‿‿ over` is `true` (both players stall in `over + under`);
  `over <> over` is `false`. On finite forms the projection degenerates
  to the bijection `>> ↔ >`, `>< ↔ ∥`, `<> ↔ =`, `<< ↔ <` — conformance
  vectors, not prose. Terminology, used consistently: singles are
  *comparisons*; doubles are *outcome-cell tests*.
- **The glyphs move like the math.** Negation is 180° rotation of the
  grid = string-reverse + atom-flip (`>`↔`<`, `‿` fixed):
  `cell(-G, -H) = rotate180(cell(G, H))`, and operand swap acts
  identically. The self-dual cells are `<>`, `><`, `‿‿`. Read them
  aloud: `<>` is *second player wins*, `><` is *first player wins* — the
  P/N glyphs derive themselves. (Known hazard, documented: `<>` means
  "not equal" in some languages; here, on finite forms, it is true
  exactly when `=` is. The tutor teaches; convention lost, shape won.)
- The CGT glyph collision is settled as before: ogham's `↑` is power;
  up/down are the literal atoms `up`, `down` (§7.5).

### 10.7 Element-`=:` — loopy games are equations

`=:` with an Element-sorted RHS and a self-mention is guarded coinductive
definition, legal exactly here (§9.1):

```text
on   =: {on |}          off =: {| off}         dud =: {dud | dud}
over =: {0 | over}      ones =: {1 | ones}     // streams are loopy games
l    =: [1, 2] ⧺ l      // purely periodic; ⧺ is guardedness-transparent from the left
```

- **Guardedness, checked after definition-time reduction.** The RHS
  reduces with the μ-name symbolic: brace constructors may enclose
  symbolic occurrences; `⧺` reduces structurally (walks only its left
  operand — a closed proper spine unfolds with the tail grafted, a
  closed cyclic spine returns itself and the discarded right operand
  takes its μ-occurrences with it). Every other operator is strict in
  its operands' options: applying one to a μ-containing operand is
  `E_Unfounded`. After reduction every remaining occurrence must sit
  strictly inside a brace constructor; a bare-root occurrence (`g =: g`,
  `h =: [] ⧺ h`, `k =: k ⧺ [1]`, `m =: m + 1`) is `E_Unfounded`.
- **The graph is materialized and classified at definition**: the cyclic
  form becomes a `LoopyPartizanGraph`; outcomes with draws come from the
  retrograde classification. Fuel is untouched.
- **The loopy envelope at 0.3.5** (the 0.3.0 envelope, loosened to the
  engine's verified surface — error → value, never breaking):
  - allowed: binding, display, option access, `≡`, `hasdraw`,
    `stopper`, both operands of `⧺`, the nine outcome
    doubles, singles on stopper operands, `+`
    (the product-graph sum — the result is the sum graph, displayed as a
    program per §10.8) and unary/binary `-` (the L/R graph swap).
  - rejected with `E_Loopy`: singles beyond stoppers (witness-carrying),
    `canon` (fusion is 0.4.0).
  - resource-guarded: product graphs multiply node counts; materialized
    graphs (definition, negation, sums, flattening) draw on an explicit
    node budget — default **2¹⁶ = 65536** nodes, counted per distinct
    node at first discovery, root included; nothing partial escapes on
    failure — firing `E_GraphBudget` when exceeded. `:graph n` is the
    REPL knob (`:graph` alone prints the budget) and `@graph n` the
    corpus directive, both mirroring fuel's plumbing (persist until the
    next directive; `@world`/`:world` resets to default). Graph size is
    a first-class resource axis beside fuel (§17.2), and "total" always
    means *mathematically total, operationally budgeted*.
- **`hasdraw(E) → Bool`** (renamed from 0.3.0 `drawn` — the
  old name read as "the game is drawn"; the predicate means *some*
  starter draws): true iff at least one mover faces a draw — exactly the
  Bool union of the five `‿`-cells against `0`; kept as the one
  ergonomic convenience over the doubles. Identically `false` on finite
  forms. `hasdraw(dud)` is `true`; `hasdraw(on)`, `hasdraw(over)`,
  `hasdraw(ones)` are `false` (alternation: forced returns still hand
  the mover a win).
- **`stopper(E) → Bool`**: the singles' gate predicate,
  user-askable. A **form/graph predicate** — documented as such: singles
  are value-invariant where defined, but the 0.3.5 decision procedure
  requires both *presented* operands to be stopper graphs.

### 10.8 Loopy display

A loopy *root* echoes as its equation (`> on` prints `on =: {on |}`); an
interior node re-roots the equation at itself with the defining name
α-bound (`tl@l` for the period-2 `l` prints `l =: {2 | {1 | l}}`). A
composite value containing cycles it does not root displays as a §8.6
body — one local `=:` per distinct cycle in first-reach order, final
expression the structural form: `(q =: {1 | {2 | q}}; {9 | q})`. Values
not rooted at any user binding — negations, sums — get **synthesized
α-bound names**: `g1, g2, …` in first-reach order (bound
variables of the displayed program, not environment references; a
rebinding can never change the meaning of an old echo). Multi-cycle
bodies emit their equations inner-to-outer, so earlier statements
satisfy later references; well-founded exits collapse back into finite
forms before display, so recognition still fires inside equations
(`-ones` prints `g1 =: {g1 | -1}`, and `on + off` prints dud's own shape
`g1 =: {g1 | g1}`). Round-trips by
construction: the display *is* a program computing the value.

## 11. Stdlib

All thin wrappers; signatures sorted (E = Element, I = Index, B = Bool).
Reserved as identifiers (§3).

| call | worlds | notes |
|---|---|---|
| `rev(E)` | Clifford | `E_GeneralMetric` if `a ≠ ∅` |
| `grade(E, I)` | Clifford | |
| `even(E)` | Clifford | |
| `dual(E)` | Clifford | `None → E_NotInvertible` (pseudoscalar) |
| `coef(E, I)` | Clifford | coefficient of `e_i` (grade-0 result; total in the Element; `i ≥ dim` → `E_BladeIndex`) |
| `tr(E[, I])` | nimber, `f*` | Gold chain: `tr(x ⋅ x↑(2↑a))` |
| `frob(E)` | finite fields | Frobenius |
| `deg(E)` | poly worlds | returns Index; `deg(0)` → `E_Domain` |
| `gcd(E,E)` | poly worlds | monic / positive-primitive results |
| `nleft(E)` / `nright(E)` | game | option counts (Index) |
| `left(E, I)` / `right(E, I)` | game | i-th option, 0-indexed; out of range → `E_Domain` |
| `canon(E)` | game | §10.5; `E_Loopy` on loopy values |
| `hasdraw(E)` | game | §10.7 (renames `drawn`) |
| `stopper(E)` | game | §10.7 |

Removed at 0.3.5: prefix `!` factorial (the equation binder made it a
four-word user definition — v0.1 needed an operator because there was no
recursion; 0.3.0's flagship *is* factorial), `up()`/`down()`/`dim()`
(literal atoms now, §7.5), `drawn` (renamed). Everything else (versors,
sandwiches, contractions, meet, spinor norms, thermography) is
deliberately out — reach it from Rust/Python.

## 12. Display (canonical form, v3)

Every `Display` impl in language scope emits canonical ogham — one
rendering path each.

### 12.1 Scalars

| type | canonical display |
|---|---|
| `Nimber` | `*5` |
| `Ordinal` | star-wrapped: `*5`, `*ω`, `*(ω⋅3)`, `*(ω↑2)`, `*(ω + 1)` |
| `Surreal` / `Omnific` | CNF: `3⋅ω↑2 - ω + 5`, `ω↑-1`, `ω↑(1/2)` — exponent bare iff a signed integer |
| `Integer`, `Fp` | plain int |
| `Fpn` | `3⋅x↑2 + 2⋅x + 1` |
| `Poly` | `1 + 2⋅t` — **explicit coefficient, conformance-pinned** (`1⋅t`, `1⋅t↑2`); coefficient-1 elision is a Multivector-blade rule only; don't "fix" it |
| `RationalFunction` | `(num)/(den)` |

### 12.2 Multivectors

Blades render as wedge expressions `e0∧e1`; coefficients attach
`coeff⋅label` with coefficient-`1` elided and `-1` → `-label` (compared
via `S::one().neg()`, never a literal). **Join rule**: a term rendering
that starts with `-` is stripped and joined with ` - ` (string-level,
char-agnostic). **Zero rule**: the empty multivector renders as
`S::zero()`'s display (`*0` in nim-worlds, `0` elsewhere).
**Atomicity**: a rendering is atomic iff it contains no spaces and no
operator characters outside balanced parens; a single leading `-` is a
sign. Atomic coefficients attach bare; non-atomic ones get parens
(`(x + 1)⋅e0∧e1`).

### 12.3 Game forms

§10.2's structural display + multiset recognition chain. Loopy values:
§10.8 equation/program display.

### 12.4 Index marking

Canonical display marks Index values `#n` at every sort-neutral position
(binding RHS, statement position, argument frames, ternary branches,
lambda bodies) and leaves them bare exactly where the grammar forces
Index (pure-Index exponent slots after `↑`, stdlib I-slots) — the
minimal-mark rule, the sort-space analogue of minimal parens. One slot
is sort-ambiguous rather than forced: the exponent of base `ω` in the
surreal family admits Scalar exponents (§8.1), so Index marks stay
visible there. `grundy@*2` displays `#2`; the game `2` displays `2`.

### 12.5 Functions, Bools, sequences

Functions print `binders ↦ body` (minimal parens; single spaces around
`↦ ? :` and word operators); inlining means composites display expanded
(the REPL is the tutor; deep chains blow up — accepted). Bools print
`true`/`false`. Sequences preserve the user's let-structure. Recursive
functions echo their equation form.

## 13. Error taxonomy

`OghamError { kind, span, message, hint }`. Errors are built
through centralized constructors; guidance lives in the `hint` field, not
the message tail, and focused tests assert hints (the 0.3.0 drift —
E_Modulus advice in the message, hintless `≡`— is repaired). Kinds:

| kind | trigger | canonical hint example |
|---|---|---|
| `E_Parse` | token/grammar violation | site-specific teaching hints: STAR after a complete operand — "`*` is the nimber prefix; the product is `⋅` (sugar `.`)"; `IDENT(args) :=` — "functions are lambdas: `name := x ↦ …`"; `!=` — "not-equal is `not (a = b)`; `!` is fuzzy `∥`"; lone `‿`/`_` — "mover-result atoms come in pairs"; barless braces — "`[a, b]` is the list; braces are game forms"; relop-tier `\|` — "the braceform bar is structural; fuzzy is `∥` (sugar `!`)" |
| `E_Reserved` | `↑↑`, `O(` | "reserved for future precision syntax" |
| `E_ExpSort` | non-Index exponent | "`↑`/`^` is power; the wedge product is `∧`/`&`" |
| `E_IndexSort`, `E_BoolSort`, `E_FnSort` | sort discipline (§6) | |
| `E_Shadow` | binder shadows reserved/stdlib/generator; duplicate binders | poly worlds: "`t` is the indeterminate here; `5⋅t + 1` is already a function" |
| `E_SeqValue` | discarded intermediate value | |
| `E_BareInt` | bare integer at Element position in nim-worlds | "did you mean `*3`?" |
| `E_BareOrdinal` | bare `ω` in ordinal world | "values are starred here: `*ω`" |
| `E_WrongWorld` | literal/operator foreign to the session world; unknown world name | unknown `:world` lists the menu and near-matches |
| `E_CnfOrder` | star-literal exponents not descending | "CNF indices are structural: `*(ω + 1)`, not `*(1 + ω)`" |
| `E_KummerEscape` | ordinal mul/inv past the tower | "below ω^(ω^ω), primes ≤ 709 — see docs/OPEN.md" |
| `E_NotInvertible` | failed inverse/exact division | per-world math; remainder named |
| `E_DivisionByZero` | `/0`, `% 0`, ratfunc pole | |
| `E_BladeIndex` | `e‹i›`/`coef` with `i ≥ dim` | |
| `E_DimMismatch` | container length ≠ dim (Clifford) | |
| `E_GeneralMetric` | `rev`/`dual` with `a ≠ ∅` | "reverse is undefined for the Chevalley construction" |
| `E_Unbound` | unknown identifier | "did you mean `q := 5`?"; self-mention: "recursive definition? `=:`"; `omega`: "ω is `ω` (sugar `w`)"; `outcome`/`winner`/`who` as unknown calls: "outcomes are relations against 0: `g > 0` Left wins, `g < 0` Right, `g = 0` second player, `g ∥ 0` first player; draws: the `‿` doubles" |
| `E_Arity`, `E_UnknownFn` | call errors | `up()`/`dim()`/`drawn()`: "`up` is a literal now" / "`hasdraw`" |
| `E_Grade0` | grade > 0 where grade-0 required | |
| `E_Modulus` | `%` modulus outside the world's scope | "moduli here are monic ω-powers: `% ω↑2` truncates the CNF below it" |
| `E_Overflow` | payload past its carrier | |
| `E_Domain` | operand outside an operator's domain (option index out of range) | |
| `E_Fuel` | μ-budget exhausted (§9.2); also the depth-guard firing, named as such | |
| `E_Unfounded` | unguarded Element-`=:` (§10.7) | |
| `E_Improper` | `⧺` left walk hits a non-list node | |
| `E_Loopy` | value-stratum operation beyond its loopy envelope (§10.7) | witness-carrying: names the alternating cycle |
| `E_GraphBudget` | materialized graph past the node budget | distinct from `E_Loopy` — a resource, not a theory boundary |

## 14. REPL and files

`examples/ogham_repl.rs` drives `src/ogham/`'s `OghamSession`. Default
world `integer 0`; the banner names the version and world. Colon
commands: `:world …`, `:fuel [n]`, `:graph [n]`, `:env`, `:help`,
`:quit`. A failed `:world` preserves the current world, its bindings,
and the worker.

**The REPL earns the tutor principle**: `:help` is a task-first
screen — the world menu (§7.1) plus one seed line per family (a nim
product, a game form + an outcome relation against 0, a `=:` function, a
stream via `⧺`). Comment-only lines are no-ops; EOF flushes a pending
continuation; unknown worlds list the menu.

`.og` files are piped sessions: the same statement syntax, `:world`
directive lines included — `cargo run --example ogham_repl < file.og` is
the runner. One statement per line at depth 0; continuation while
delimiters are open.

## 15. Host operator alignment (Rust + Python)

The host overloads speak the same dialect as the display; the table is
unchanged from 0.3.0 except the deletions. Highlights:

| op | Rust | Python |
|---|---|---|
| wedge | `impl BitAnd` (`a & b`) | `__and__`; `__xor__` raises with the `E_ExpSort` hint |
| power | scalars: `impl BitXor<u128>` (RHS is the meta-integer type — `Nimber ^ Nimber` does not compile, by design); multivectors: `CliffordAlgebra::pow` only | `**`; never `__xor__` |
| ordinal power | no operator; `nim_pow -> Option` | `pow()` raising honestly |
| remainder | no `Rem` impl (Rust `%` truncates; ogham's is Euclidean) — methods only | `__mod__` (Python `%` agrees) |
| evaluation | inherent `Poly::eval`/`compose` | `__matmul__` |
| relations | `Ord` on ordered scalars; `fuzzy()` on nim types; no `PartialOrd` on nim types, no `BitOr`-as-fuzzy | rich comparisons / `fuzzy()`; `Ordinal.__richcmp__` speaks CNF *address* order, the language speaks value order — documented, not unified |
| `↦ ? : and/or/not =: ⧺ ≡ {L\|R} # ‿`-doubles | **none** — ogham spelling only | none |

Factorial rows are gone with the operator. Game-world exposure to Python
remains a binding-scope-policy decision (`src/py/AGENTS.md`), not part of
0.3.5.

## 16. Conformance corpus

[`docs/ogham/conformance.txt`](conformance.txt), UTF-8, line-based:

```text
@world ‹world-decl args›     // resets bindings
@fuel ‹u128›                 // per-statement μ-step budget
@graph ‹u128›                // graph node budget (§10.7)
> ‹input line›               // statement, exactly as typed (may use sugar)
>> ‹continuation line›
~ ‹canonical unparse›        // optional: expected canonical echo
= ‹expected display›         // value line; or:
! E_Kind: ‹message substring›
```

Corpus files use `//` comments (the language's own), on their
own lines or trailing input. Blocks separated by blank lines. The harness
is `tests/ogham_conformance.rs` (pure Rust); it also asserts hint fields
on the vectors that pin them. The corpus is reorganized thematically at
0.3.5 (by world and feature, one pass; version provenance lives in the
retained staging files `conformance_v0.2.txt`, `conformance_v0.3.txt`,
`conformance_v0.3.5.txt` and the history appendix). Blessing remains an
operator workflow: the engine can suggest values, the spec stays the
oracle.

**0.3.5 vector obligations** (the build-invariant pin list from the
codex-seat review, in addition to the per-section vectors): all nine
outcome cells with explicit graph witnesses; negation-rotation and
operand-swap laws across every cell; finite forms hitting only the four
corners; the nine-to-four projection table exhaustively on stopper pairs;
the `over` triple (`over = over`, `over ‿‿ over`, `not (over <> over)`);
`over`/`under` stoppers, their sum not; singles gating on operands never
the difference; stopper witnesses naming an alternating turn-state cycle;
retrograde agreement with an independent oracle on random small graphs;
product-graph commutativity up to outcome; `E_GraphBudget` distinct from
`E_Loopy`; the reordered-options `≡`/`canon` family; the `⧺` laziness
counterexample; `#`-capture round-trips; container/brace migrations.

## 17. Implementation contract

### 17.1 Architecture

One shared evaluation core, per-world thin implementations: the
function/binding machinery (closure by substitution, definition-time
validation, application, composition, sequencing, μ bookkeeping, fuel)
lives once, generic over a world-ops trait (literal mapping, operator
dispatch, relations, stdlib, display); `Runtime<S>`, `PolyRuntime`,
`RatFuncRuntime`, and `GameRuntime` shrink to world-ops impls; the
`World` dispatch enum keeps one arm per monomorphised world (that enum
*is* how rule 5 is preserved) with its forwarding generated by macro.
The 0.3.0 shape — four near-parallel copies of the machinery, 44% of
`eval.rs` — was copy-drift risk, not principle. (`eval_index` remains
per-world: the worlds carry genuinely different Index call surfaces —
`deg`, `dim`, option counts; a candidate consolidation for 0.3.6.)

Behavior the architecture pins, worded here so the code stops being the
only record: game Elements enter recursive calls by *temporary binding*
rather than substitution lowering (loopy graph values cannot lower
through a substituted AST; the shared application shell owns arity,
fuel, μ bookkeeping, and restoration, and the game world supplies the
binding hook). Definition-time validation samples binder sorts with
fixed representative values (`0`/`1`/`true`-class) under the static
partiality allowlist — validation proves sorts and world-legality, not
value-level totality (§8.6's completeness claim is about checking, not
evaluation).

### 17.2 Host-resource guards

The abstract semantics never aborts the host. Statement evaluation runs
on a dedicated **64 MiB** persistent worker (REPL, `ogham_eval`,
harness — identical headroom; per-statement thread spawn
retired, and **world declarations parse under the same boundary**);
μ-descent carries a **1024**-frame guard firing `E_Fuel` naming the
depth guard; source delimiters and constructed ASTs are audited against
a **1536**-node ceiling before recursive consumers run (`E_Parse`);
materialized loopy graphs (definition, negation, and
especially product-graph sums) draw on the §10.7 node budget (default
65536, `:graph`/`@graph`, discovery-time counting, nothing partial on
failure) firing `E_GraphBudget`. A failed world declaration preserves
the current world and worker. These guards are deliberately stricter
than the abstract model; the trampoline route that would retire the
depth guard is 0.4.0 floor work (§18).

### 17.3 Validation gates

`cargo test` (unit + conformance + property suites; run proptest with
`OGDOAD_PROPTEST_CASES=N` before trusting arithmetic changes),
`cargo clippy --all-targets`, `cargo fmt`, cold `cargo doc --no-deps`,
`cargo check --features python` after any surface the bindings touch,
rebuilt `demo.py` after display changes. The staged corpus gates every
build stage; the hand-verified prefix is never machine-edited.

## 18. v0.4.0 — the standing sketch (slimmed at 0.3.5)

The 0.3.5 envelope pull-in (outcome doubles, stopper singles, total
loopy `+`/`-`, `stopper`/`hasdraw`) absorbed the §20.2–20.3 program of
the old sketch. What remains, in order:

1. **The higher-order gate** (0.4.0 opens here): map/fold,
   functions-as-values — decided against the Index-recursion pain 0.3.x
   makes measurable. No Sequence sort: a third container would weaken
   the native-shape thesis; if Function is promoted it earns it through
   one symmetric map/fold story over the existing fixed and free shapes.
2. **Mutual `=:` groups** — adjacent-binding grammar (forward reference
   among adjacent bindings is `E_Unbound` today, so meaning is pure
   error → value); guardedness generalizes with the group name-set
   symbolic; display re-roots one graph / echoes a §8.6 body.
3. **`canon` on stoppers** — the fusion/simplest-form algorithm; the
   largest genuinely-new math item; nothing depends on it; last.
4. **One-stopper biased comparison** (the Hwa/Siegel sided machinery) —
   loosens the singles' both-stoppers gate; onside/offside sidling for
   non-stoppers stays open beyond that.
5. **The floor**: trampoline vs `stacker` vs targeted work-stacks
   (dependency question is a9's), retiring the depth guard; array-side
   envelope (blade-bitmask `coef`, poly-world `coef`) on measured pain.

## 19. Version history

| version | date | delta |
|---|---|---|
| 0.1 | 2026-06-12 | core: worlds, scalar literals, Clifford operators, Display v2, conformance harness |
| 0.1.1 | 2026-06-12 | function-shaped poly/ratfunc worlds; `@` `%` exact-division; `deg`/`gcd` |
| 0.2.0 | 2026-06-12 | sorts (Bool, Function), lambdas by substitution, ternary + word operators, relations as values |
| 0.2.1 | 2026-06-12 | `;` sequences/programs; let-bodies; continuation lines |
| 0.3.0 | 2026-07-09 | `=:` + fuel; containers (`coef`/`dim`; game lists); the game world (forms, `⧺`, `≡`, `canon`, four-way relations); loopy Element-`=:`, streams, coinductive append; host guards |
| 0.3.5 | 2026-07-09/10 | **the reflection release**: unified spec + identity rewrite; multiset `≡`/recognition/`canon` (retraction laws now true); `#` Index literals + `//`,`/* */` comments; `[…]` container in both faces, braces always barred; prefix `!` factorial removed, `!` = fuzzy sugar; `up`/`down`/`dim` literal atoms; full-expression ternary branches; right-lazy `⧺`; nine-cell outcome relations + stopper-projected singles; total loopy `+`/`-`; `hasdraw`/`stopper`; runtime unification + persistent worker + guarded world-decl; `E_GraphBudget`; tutor REPL + hint package |

Provenance: the pre-merge staging corpora (`conformance_v0.2.txt`,
`conformance_v0.3.txt`, `conformance_v0.3.5.txt`) and the ledgers
(`docs/DONE.md`, `docs/CONTINUATIONS.md`). The reflection pass's review
record (four perspectives + the codex seat's adversarial verification of
the nine-cell design, with the Siegel pins) lives in the session record
and the `ogham-reflect-*` gaslamp threads, 2026-07-09.
