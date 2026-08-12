# grundy — language specification

Status: **v0.3.6 implemented** (spec'd 2026-07-10 at the second adversarial
pass: seven-perspective sweep — four codex seats over the gaslamp
`ogham-036-*` threads, three independent implementation reviews, a9 + fable
deciding; built the same day over the gaslamp `ogham-v36` thread in
eight gated stages — A–G sol implementing, H the lead close-out — fable
gating and committing throughout). This document is the **normative language
contract and nothing else**: identity, syntax, sorts, semantics, errors,
display. The runtime architecture and resource guards live in
[`implementation.md`](implementation.md); the roadmap lives in
[`docs/CONTINUATIONS.md`](../../docs/CONTINUATIONS.md) (the version ladder:
0.3.6 → 0.3.7 → 0.3.8 → **0.4.0 = the public release** → 1.0.0 higher-order);
history lives in [`docs/DONE.md`](../../docs/DONE.md) and §17.

Every observable semantic rule in this document is pinned by the
**conformance suite** (§16): exact corpus vectors, law tests, or differential
oracles. Implementing agents work until the suite is green; judgment calls go
back to the spec, not into the code.

File extension `.og` (after ogdoad, the crate that ships it). The name honors
P. M. Grundy of the Sprague–Grundy theorem — a person-name in the Haskell
tradition, for the value the language deliberately keeps as four lines of user
code rather than a primitive (§1). Born **ogham** (through 0.3.6, named for
og(doad) + the ancient stroke-script); renamed 2026-07-15, provisionally —
finalization is 0.3.8 release dress
([`docs/CONTINUATIONS.md`](../../docs/CONTINUATIONS.md)).

---

## 1. Identity

grundy is a **lisp for games with weird numbers**: a small language whose data
model is Conway's ontology and whose computation model is as thin as the data
model is rich. Most languages are the other way around — elaborate control,
impoverished numbers. grundy inverts the profile. The values are the richest
objects in the language (nimbers addressed by ordinals, Hahn-series surreals,
multivectors over either, game forms over everything); computation is exactly
three things — substitution you can see, one equation binder, and
non-strictness exactly where the mathematics never looks. In the algebraic
worlds grundy is a coordinate calculus over unusually rich scalars; in the game
world it becomes a first-order recursive-equation language; the two faces
share one fenced grammar, one canonical executable display, and explicit
boundaries.

Because the values are rich, the language needs almost no machinery to be
expressive: mex and Grundy are four lines of user code, not primitives.
Because computation is thin, every construct can afford to coincide with a
piece of mathematics. The coincidences are the language:

- **The cons cell and the game form are one constructor.** `{h | t}` read
  with singleton sides is Lisp's pair; nil is `{|}` = `0` — *list exhausted,
  game ended, additive identity* are one object. This is a productive
  structural coincidence, stated as such (claim level: interpretation): the
  deeper true reading is that a proper list is a *polarized game* — Left
  selects the head, Right advances the tail. Negation swaps the player
  polarity **and negates the continuations**; proper spines are not closed
  under it (`-[a, b] = {{0 | -b} | -a}`).
- **The relation set is the outcome partition.** The four value relations
  `= < > ∥` are the four cells of the finite CGT order; relate a game to `0`
  and you have read out its outcome class. There is no `≠` because the
  partition has no fifth cell. Where draws exist the partition grows to nine
  cells and the notation grows with it — the outcome relations of §10.6,
  whose glyphs *are* the 3×3 outcome grid.
- **`=:` is the equation binder — one glyph, two polarities.** Written to a
  function it unfolds inductively under fuel; written to a game Element it
  closes coinductively into a finite cyclic graph — and an adjacent run of
  such equations closes as one simultaneous system (§9.3), so Siegel's loopy
  games are recursive equations and grundy writes them as such: `on =: {on |}`
  directly executes Siegel's defining equation `on = {on |}`. Assignment `:=`
  flows the past in; `=:` states an equation the name satisfies. The notation
  mirror is the semantics; the polarity is decided by the sort.
- **Non-strictness sits exactly where the mathematics never looks — and it
  skips evaluation, never checking.** The branches of `if` and the right
  operands of `and`/`or` (play one branch); the right operand of `⧺`
  (coinduction never reaches it until the left spine ends). The list is exhaustive, and
  every skipped operand is still sort-checked (§8.6): laziness is about
  *work*, not about *meaning*.
- **Partiality is attributable.** A program terminates or errors with the
  mathematics in the message — `E_KummerEscape` naming the tower,
  `E_NotInvertible` naming the remainder, `E_Fuel` naming the μ that struck
  zero — never a silent hang, never a coerced answer. Where non-termination
  *has* a mathematical value — loopy games, draws — it is a value, not an
  error.
- **One container glyph, three native shapes — fixed, graded, free.** `[…]`
  is the world's native presentation of finite support: in the Clifford
  worlds the world-fixed coordinate array (bulk algebra, random access); in
  the polynomial worlds the graded coefficient spine (finite support over
  degrees); in the game world the free cons spine (option descent,
  μ/coinduction). The empty container is the additive zero in all three. The
  repo's founding scope boundary — ring versus group — reappears as
  shape-with-algebra versus shape-with-recursion. (An architectural rhyme,
  not a theorem.)

The discipline (unchanged since v0.1, in service of the identity above):

1. **Weird numbers first.** Scalar literals are the richest part of the
   grammar. `*` belongs to nimbers, not to multiplication.
2. **Two display laws.** `parse ∘ unparse = id` on parser-produced ASTs, and
   `eval ∘ parse ∘ display ≃ value` — structural `≡` for game forms,
   α-equivalence for recursive equations. Display emits canonical grundy; the
   parser's input language is a superset. Every value's display is a
   **self-contained program** that rebuilds it in a fresh session, up to and
   including loopy values, which display as the equation systems that define
   them (§10.8).
3. **Two layers: canonical and sugar.** Canonical uses the unicode math
   glyphs where ASCII is contested (`ω ↑ ∧ ⋅ ∥ ↦ ⧺ ≡ ‿`); ASCII stays
   canonical where it is uncontested (`* e # + - / = := < > [ ] ( )` and the
   four ASCII outcome corners `>> >< <> <<`, plus `|` as the structural
   braceform bar — its only role). Sugar is input-only; the REPL echoes
   canonical (the REPL is the tutor).
4. **Context is fenced, never guessed.** A world declaration chooses the
   laws; `*(…)` and `#(…)` and `{… | …}` visibly fence structural
   subgrammars; sort positions are explicit in the grammar, and where
   position is silent the rule is declared, not inferred (§6: the unmarked
   binder *is* Element, by law). No juxtaposition anywhere, no coercions, no
   inferred worlds.
5. **One active world at a time.** Mixing is a parse/eval-time error, never a
   coercion.
6. **Display never canonicalizes.** Forms display as built (up to
   presentation, §10.1); value identity is said with `=` or `canon`.
7. **Errors are mathematical content.**
8. **Pure Rust, zero deps, no pyo3 outside `src/py/`** (core rule 1).

Non-goals, permanent: quote/macros (code-as-data would blur the
structural/arithmetic fence the grammar fights hardest to keep); mutation,
I/O, strings (rebinding is the only state, the REPL the only effect); floats;
juxtaposition; coercions. Transfinite/ω-length games: out — the game world is
the finite-graph pillar.

**Recorded refusals** (asked and answered; the writeup carries the
arguments): no bare `#` (`#` alone has no referent — typographic symmetry
with bare `*` would be empty); no `on`/`off`/`dud` literal atoms (they would
erase the loopy-games-are-equations thesis); no value-dependent operator
legality (no `⋅`/`/` in the game world "when the operands happen to be
numbers" — dyadic *literals* obtain the useful part without moving the
group/ring fence, §7.7); no `deg` on rational functions (map degree,
num−den degree, and order at infinity are three inequivalent notions); no
polynomial `⧺` (coefficient concatenation is no algebra operation); no
`number(E)` yet (its stratum is genuinely ambiguous on stoppers); Norton
multiplication never as `⋅` (an explicit call may join a later thermography
tranche); misère play never as a mode toggle (it deserves a separately
specified world with an explicit universe, §10.9).

## 2. Symbols and codepoints

| meaning | canonical | codepoint | ASCII sugar | notes |
|---|---|---|---|---|
| omega | `ω` | U+03C9 | `w` | atom; also inside star-literals |
| power | `↑` | U+2191 | `^` | right-assoc; Knuth's arrow |
| wedge | `∧` | U+2227 | `&` | exterior product |
| product | `⋅` | U+22C5 | `.` | the algebra's product; U+00B7 `·` also accepted on input |
| nimber prefix | `*` | — | — | value marker in nim-worlds (§7.3) |
| index prefix | `#` | — | — | meta-integer marker (§7.6): `#5`, `#(2⋅3)`; also the Index **binder mark** (§6): `#i ↦ …` |
| bool binder mark | `?` | — | — | `?p ↦ …` declares a Bool binder (§6); its **only** role |
| blade prefix | `e` | — | — | `e0`, `e1`, … basis 1-blades |
| neg / sub | `-` | — | — | unary and binary |
| recip / div | `/` | — | — | unary and binary; a literal-shaped ratio is a **fraction literal** (§7.7) |
| add | `+` | — | — | |
| remainder | `%` | — | — | Euclidean / CNF-truncation remainder (§8.3) |
| evaluate | `@` | — | — | substitution/application, binds tightest (§8.4) |
| equality | `=` | — | `==` | Bool-valued value relation (§8.5, §10.6) |
| less / greater | `<` `>` | — | — | Bool-valued strict order relations |
| fuzzy | `∥` | U+2225 | `!` | incomparable, CGT ∥ (`a != b` earns a hint: not-equal is `not (a = b)`) |
| draw atom | `‿` | U+203F | `_` | the undertie — the tie glyph; occurs only inside outcome doubles (§10.6); a lone `‿` errors with "mover-result atoms come in pairs" |
| outcome relations | `>> >‿ >< ‿> ‿‿ ‿< <> <‿ <<` | — | `_`-forms | the nine-cell grid as its own glyphs (§10.6); game world only |
| structural equality | `≡` | U+2261 | `===` | relop tier, non-chaining; game world only (§10.5) |
| append | `⧺` | U+29FA | `++` | right-assoc, looser than `+ -`, tighter than relations; game world only (§10.4) |
| game form | `{L\|R}` | — | — | braces are real; `\|` and `,` structural inside; the bar is mandatory |
| container | `[a,b,c]` | — | — | the world-shaped container (§7.8): Clifford coordinates / polynomial coefficients / game spine |
| binding | `:=` | — | — | `name := expr`; rebinding allowed |
| fixpoint binding | `=:` | — | — | the equation binder (§9); munches before `=`; adjacent runs form systems (§9.3) |
| lambda | `↦` | U+21A6 | `~` | first-order Function value (§6) |
| conditional | `if a then b else c` | — | — | words, like the rest of the Bool tier; lazy branches, `else` mandatory, else-if chains flat (§4) |
| bool words | `and or not` | — | — | lazy word operators; reserved |
| comment | `//` and `/* … */` | — | — | line and block; block comments nest |

Reserved, must lex but reject with `E_Reserved`: `↑↑` and `O(` (precision
tails). The name `t` is reserved only inside poly/ratfunc worlds (the
indeterminate); `x` inside `f*` worlds (the field generator). Bare `:` has
no expression role at 0.3.6 — it is held for 0.3.7's ordinal sum `G:H`,
Conway's own colon (the conditional-word move freed it; see
`docs/CONTINUATIONS.md`).

**Unary-fill principle**: a unary form of a binary operator fills the left
operand with the operator's identity. `-a = 0 - a`, `/a = 1/a`. Only the two
inverse-taking operators have unary forms; no other operator gets one.

## 3. Lexical structure

- Tokens are self-delimiting; there are **zero juxtaposition rules**.
  Whitespace separates tokens but is **never semantic** — in particular there
  is no adjacency requirement anywhere in the grammar (the 0.3.5 "tight
  signed exponent" rule is repealed: `2 ↑ - 3` and `2↑-3` are the same
  program; the latter is canonical display).
- `INT`: `[0-9]+`, value must fit `u128`. No sign (sign is unary `-`).
- `IDENT`: `[a-z][a-z0-9_]*`, excluding reserved words. Reserved everywhere:
  `w`, `and`, `or`, `not`, `if`, `then`, `else`, the literal atoms
  (`true false up down dim`), and stdlib function names (§11). Interior `_` stays identifier material:
  `foo_bar` is an IDENT; the draw atom is only recognized where an IDENT
  cannot start.
- `e` followed immediately by digits lexes as a BLADE token. `e` alone is an
  error. `*` followed by anything lexes as the STAR prefix; `*` is never
  infix. `#` followed by an INT or `(` lexes as the INDEX prefix; `#`
  followed by an IDENT is legal only in binder position (§4, §6); `#` is
  never infix and does not open a comment.
- Comments: `//` to end of line; `/* … */` nesting block comments. Both are
  whitespace to the lexer. The sequence `/*` always opens a comment, so the
  reciprocal of a star-literal takes parens: `/(*2)` — display emits the
  parenthesized form (the one place comment syntax touches canonical output).
- Sugar substitution happens in the lexer: `w→ω`, `^→↑`, `&→∧`, `.→⋅`,
  `·→⋅`, `!→∥`, `==→=`, `~→↦`, `++→⧺`, `===→≡`, `_→‿`, and the `_`-spelled
  outcome doubles (`>_ → >‿`, `_> → ‿>`, `<_ → <‿`, `_< → ‿<`, `__ → ‿‿`).
  After the lexer, only canonical tokens exist.
- Multi-char tokens munch longest-first: `=:` before `=`, `===` before `==`,
  `++` before `+`, the nine outcome doubles before the relational singles
  (`>>` before `>`, `<>` before `<`, …). `a + + b` stays `E_Parse`; `a > > b`
  stays two tokens and errors as chained relations (the message says so).
- The braceform bar is not a relation: `|` is canonical as the structural
  separator and has no relop reading (a relop-tier `|` earns the §13 hint),
  and `∥` is refused as the bar in turn.
- `!` lexes to `∥`. The sequence `!=` therefore lexes as `∥` `=` —
  ungrammatical, and the error carries the hint: "not-equal is `not (a = b)`;
  `!` is fuzzy `∥`".
- **Continuation**: the lexer consumes continuation lines while `(`/`[`/`{`
  are unbalanced, **and** after any line whose last token cannot end a
  statement — `↦`, `:=`, `=:`, `;`, `,`, `if`, `then`, `else`, `and`, `or`,
  `not`, and every binary operator. A line ending in a complete statement is
  complete.

## 4. Grammar (EBNF)

Statements (one per line at depth 0; blank and comment-only lines are no-ops):

```ebnf
statement   = binding | expression | lambda ;
binding     = IDENT (":=" | "=:") ( lambda | expression ) ;
lambda      = binders "↦" expression ;        (* ↦ grabs maximally rightward *)
binders     = binder | "(" binder { "," binder } ")" ;
binder      = [ "#" | "?" ] IDENT ;           (* sort marks, §6 *)
sequence    = { binding ";" } statement ;     (* top level; bodies via parens *)
            (* a maximal adjacent run of "=:" bindings in a sequence is one
               equation system, §9.3 *)

expression  = "if" expression "then" expression "else" expression
            | orexpr ;                        (* branches full expressions; else mandatory *)
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

- **The written grammar is the canonical core; the parser accepts a
  superset at sort-fenced positions.** Exponents, brace items, and
  argument frames parse as general expressions and are *sort-checked at
  definition/evaluation* (`*3 ↑ *2` parses and then errors `E_ExpSort`;
  `{a ↦ a | 0}` parses and then errors `E_FnSort`). This is the fence
  principle working as designed — position decides legality, the grammar
  stays world- and sort-independent.
- **Star-literals are structural, not arithmetic.** Inside `*(…)` the symbols
  `+ ⋅ ↑` build a CNF ordinal *index* (the nimber's address in On₂); they do
  not evaluate. `*(ω + 1)` is the nimber at ordinal ω+1; `*ω + *1` is a
  nim-sum that happens to equal it. Unparenthesized star applies only to
  `INT` and bare `ω`; the star binds tighter than `↑` (`*ω↑2 = (*ω)↑2`).
- **Index-literals are the meta mirror**: `#5`, `#(2⋅3)`. The interior is an
  Index expression (`+ - ⋅ ↑`, parens). `*` marks an Element address; `#`
  marks the spectator's integer. Bare `INT` remains input sugar at
  Index-*forced* positions (exponents, stdlib I-slots); display marks Indexes
  minimally (§12.4).
- The surreal-family worlds allow CNF **at expression level, unstarred and
  live**: `3⋅ω↑2 - ω + 5` is ordinary arithmetic over monomials.
- **Conditional**: `if a then b else c` — condition Bool-sorted; branches
  are full expressions agreeing in sort; `else` is mandatory (every grundy
  expression has a value), which dissolves dangling-else by construction —
  each `else` binds the nearest open `if`, and the else-if chain is flat
  and parens-free: `if a then x else if b then y else z`. Relations,
  boolean words, appends, and nested conditionals all sit in branches bare.
  (v0.3.6 retires the C-shaped `? :`: the conditional joins
  `and`/`or`/`not`, so the Bool tier is all words and the glyphs stay
  mathematics — `:` freed for ordinal sum, `?` solely the binder mark.)
- Relations stay non-chaining. A parenthesized relation is a Bool atom.
- **Multi-param application is an argument frame** — `b@(u, v)`,
  arity-checked; not a value, not a container, cannot be bound. One-param
  keeps the atom rule: `f@7`, `f@(u + 1)`. No currying.

## 5. Precedence (tight → loose)

```text
atoms:  INT, *‹i›, #‹i›, ω, e‹i›, […], {L|R}, f(…), true/false/up/down/dim, (…)
@            evaluation/application, left-assoc; operands atoms/frames
↑            power, right-assoc; signed INT exponent ok (ω↑-1); whitespace-agnostic
unary - /    neg, reciprocal
∧            wedge
⋅  /  %      product, division, remainder, left-assoc
+  -         add, subtract
⧺            append, right-assoc (game world)
relations    = ≡ < > ∥ and the nine outcome doubles — non-chaining, one per relexpr
not
and
or
if then else conditional; else grabs maximally rightward (flat else-if chains)
↦            lambda, grabs maximally rightward
```

Wedge tighter than `⋅` follows Hestenes. Display v4 relies on the blade row:
blade terms print unparenthesized (`*3⋅e0∧e1`).

**Host-language caveat** (§15): Rust and Python cannot reproduce this table
for the overloaded operators. The precedence above is grundy's, full stop;
host code parenthesizes.

## 6. Sorts

grundy has **three first-order data sorts** — **Element** (the world's values:
multivectors, polynomials, game forms), **Index** (meta-integers, `i128`),
**Bool** (verdicts) — plus **closed Function abstractions**, which may be
bound, displayed, composed, and applied but not passed, returned, or stored.
Position determines sort; there are no coercions.

- **Function** = a binder-AST, closed over its own binders by substitution at
  definition time (§8.6). The first-order discipline is one rule: a
  Function-sorted term appears only as (a) the RHS of `:=`/`=:`, (b) an
  operand of `@`, (c) a whole statement. Everything else is `E_FnSort`.
  (Higher-order is 1.0.0's question — see the ladder.)
- **Bool** is a full citizen: verdicts are first-class, composable, bindable,
  and drive the non-strict operators. Bool values are *permitted* at every
  sort-neutral position (binding RHS, statement position, argument frames,
  conditional branches, lambda bodies) and *forced* at `if` conditions and
  `and`/`or`/`not` operands. Bool is banned in containers, arithmetic, and
  exponents: `E_BoolSort`.

### 6.1 Binder sorts — the mark triad

Binder sorts are decided at definition, by declaration and inference
together, and **never guessed**:

1. **Marks declare.** `#name` declares an Index binder; `?name` declares a
   Bool binder; a bare binder is *Element by law* unless its occurrences
   force otherwise. The triad is one mark per non-Element sort — bare for
   the world's own stuff, `#` for the spectator's integer, `?` for the
   verdict — extending the value-land marker rhyme (`*` the world's address,
   `#` the meta-integer) into binder-land, where Index captures already
   substitute as `#n` (§8.6).
2. **Forcing occurrences infer.** An occurrence at a sort-forced position
   (an exponent slot, a stdlib I-slot, an `and` operand, a world-operator
   operand, …) fixes the binder's sort. The flagship:
   `gold := (a, u) ↦ tr(u ⋅ u↑(2↑a))` infers `a : Index` (exponent slot),
   `u : Element` (product operand) — no marks needed.
3. **Conflicts are definition errors.** A mark contradicted by a forcing
   occurrence, or two occurrences forcing different sorts, is
   `E_IndexSort`/`E_BoolSort` *at definition* (`#x ↦ x ⋅ e0` errors: the
   mark says Index, the product says Element).
4. **Unforced bare binders are Element — by rule, not by accident.** A
   binder with no mark and no forcing occurrence is Element. This is the
   declared default of a language whose subject is Elements (the same shape
   as bare `INT` belonging to the world, §7.2): `succ := n ↦ n + 1` is the
   world's successor; `less := (i, j) ↦ i < j` is an Element comparator, and
   the Index one is `(#i, #j) ↦ i < j`. An application that then feeds a
   mismatched sort fails honestly at the frame (`less@(#1, #2)` →
   `E_IndexSort`) with the teaching hint: *declare the binder —
   `(#i, #j) ↦ …`*.

Display of binders is minimal-mark (§12.4's law, mirrored): the canonical
echo shows a binder's mark iff its occurrences do not force its sort — so
`gold`'s `a` echoes bare (the exponent already says Index), while
`same := (?p, ?q) ↦ p = q` keeps its marks (nothing else says Bool). Marks
round-trip: they are AST, not commentary.

- Bindings bind any sort; a bare statement of any sort evaluates and prints.
  An Index value *stays* Index through capture, binding, and application —
  the substituted literal is `#n`, so the sort is visible and the round-trip
  exact.

## 7. Worlds and literals

A session holds exactly one world plus environment (cleared on `:world`).
Clifford-capable worlds monomorphise a scalar backend into a
`CliffordAlgebra<S>`; the polynomial/ratfunc worlds are function-shaped
evaluators; the game world is the first non-scalar world. Declaration:

```text
:world ‹name› ‹dim› q=[s0,…] [b=[(i,j):s,…]] [a=[(i,j):s,…]]
:world ‹name› ‹dim› grassmann
:world nimber gold(m,a)
:world ‹scalar name›              // dim-0 shorthand: :world nimber = :world nimber 0
:world ‹poly/ratfunc name›
:world game
```

`q`/`b`/`a` mirror `Metric::diagonal`/`::new`/`::general`. Declaring `a≠∅`
warns that `rev`/`dual` are unavailable (`E_GeneralMetric`). `dim ≤ 128`.
World declarations parse under the same host guards as statements — a
pathological metric literal is an honest `E_Parse`, never a host abort.
**Dim-0 shorthand**: a scalar world named with no dimension is dimension 0 —
the visible `0` was engine configuration leaking into the first encounter.

### 7.1 The world menu (fixed dispatch)

World names are the mathematics: the polynomial ring and its fraction field
are spelled as themselves, with the square/round fence *being* the ring/field
distinction — and the square bracket then rhymes as the coefficient container
(§7.8). The 0.3.5 names remain as input aliases; canonical output (banners,
`:env`, errors) uses the mathematical spelling.

| world name(s) | alias | backend | field? | notes |
|---|---|---|---|---|
| `nimber` | — | `Nimber` (u128) | yes | F_{2^128} |
| `ordinal` | — | `Ordinal` | partial | Kummer-checked (§8.2) |
| `surreal` | — | `Surreal` | partial | monomial inverses only |
| `omnific` | — | `Omnific` | no (units ±1) | |
| `integer` | — | `Integer` (i128) | no (units ±1) | |
| `fp2 fp3 fp5 fp7` | — | `Fp<p>` | yes | |
| `f4 f8 f16 f9 f27 f25` | — | `Fpn<p,n>` | yes | generator `x` |
| `fp2[t] fp3[t] fp5[t] fp7[t]` | `poly2` … | `Poly<Fp<p>>` | no | `F_p[t]`, function-shaped |
| `integer[t]` | `polyint` | `Poly<Integer>` | no | `ℤ[t]`, monic division boundary |
| `fp2(t) fp3(t) fp5(t) fp7(t)` | `ratfunc2` … | `RationalFunction<Fp<p>>` | yes | `F_p(t)` |
| `game` | — | `games::Game` + loopy graphs | no (group) | forms, lists, loopy values; no metric, no blades |

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
| `fp*[t]`, `integer[t]`, `fp*(t)` | constant polynomial / rational function |
| `game` | the integer game — the canonical CGT embedding; the one world where bare-literal `from_int` is honest |

Bare `INT` at Index-forced position is a meta-integer in every world;
elsewhere `#n` says so explicitly (§7.6).

### 7.3 Star-literals

- `nimber`: `*n` = `Nimber(n)`; bare `*` is sugar for `*1` (canonical prints
  `*1`).
- `ordinal`: `*n`, `*ω`, `*(cnf)`; the star is the value marker; there are no
  unstarred Element literals in this world. Bare `ω` is `E_BareOrdinal`
  (hint: `*ω`).
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
forms `{0 | *1}` and `{*1 | 0}`; `E_WrongWorld` elsewhere); `dim` (Index: the
world's dimension in Clifford worlds, `#0` in dim-0 worlds, `E_WrongWorld` in
function and game worlds). No nullary calls exist; the old spellings
`up()`/`down()`/`dim()` earn hints. `-up ≡ down` holds structurally (nimber
forms are self-negative), so the literal family is closed under negation for
free.

### 7.6 Index-literals

`#5`, `#(2⋅3 + 1)` — the Index sort made audible. Two prefix markers, two
sorts: `*` is the world's address, `#` is the spectator's integer. Input may
still write bare ints where the position forces Index; canonical display
marks exactly the positions that don't (§12.4).

### 7.7 The game world's literals — integers, dyadics, nimbers

Bare `INT` = the integer game; `up`/`down`; `*n` = the nimber game; `[…]`
lists (§7.8); `{L | R}` forms (§10). `ω`, blades: `E_WrongWorld`.

**Dyadic fraction literals.** A literal-shaped ratio — `INT / INT`, either
operand carrying unary minus, both *literals* — is a **fraction literal**: a
structural literal form, not an arithmetic expression (the same move as
`*(ω + 1)`: the notation is fenced by its shape). Its meaning is per world:

- in the division-capable worlds it denotes exactly what the division always
  denoted (`1/2` in `surreal`, `fp5`, `fp2(t)` — unchanged);
- in the **game world** it denotes the canonical dyadic game — Conway's
  construction of `n/2^k` in lowest terms: `1/2` is `{0 | 1}`, `-3/4`,
  `5/8`, … A reduced denominator that is not a power of two is `E_Domain`
  ("only dyadics are short games; `1/3` is not born on any finite day");
  denominator zero is `E_DivisionByZero`.
- **No dynamic game division exists.** `g/2`, `/g`, `(1+1)/2`, and `⋅`
  remain `E_WrongWorld` in the game world — the literal closes the Conway
  parallel ("numbers are games" now true past ℤ) without pretending games
  form a field.

Recognition (§10.2) gains the matching rung: a form whose option multisets
match Conway's canonical construction of a non-integer dyadic displays as the
fraction literal.

### 7.8 The container

`[a0,…,a(n-1)]` is the world's native presentation of finite support — one
glyph, three shapes:

| | Clifford worlds | polynomial worlds | game world |
|---|---|---|---|
| shape | **fixed**: length must equal `dim` (else `E_DimMismatch`); `[]` legal only at `dim 0` | **graded**: any length; entry `i` is the coefficient of `t↑i` | **free**: any length; `[]` is nil `= {|} = 0` |
| builds | `Σ aᵢ⋅eᵢ` (grade-1) | `Σ aᵢ⋅t↑i` — `[1, 2, 3]` is `3⋅t↑2 + 2⋅t + 1` | the right-nested spine `{a0 | {a1 | … {a(n-1) | 0}…}}` |
| empty | the empty sum (dim 0) | `0` | nil |
| entries | grade-0 elements | **constant** elements — `[1, t]` is `E_Domain` ("container entries are coefficients; `t` is not a coefficient") | any game |
| access | random: `coef(v, i)` | random: `coef(p, i)` | sequential: option descent (`left`/`right`) |
| algebra | `+` is zip-with-add; `⋅` exists (ring) | `+`/`⋅` the polynomial ring | `+` is game sum, **not** append; `⋅` is `E_WrongWorld` (group) |
| iteration | Index recursion, bounded by `dim` | Index recursion, bounded by `deg` | μ-recursion / coinduction |

In the ratfunc worlds the container builds the same polynomial and injects it
into the fraction field. `coef` on rational functions stays unavailable
(`E_WrongWorld`) until a restriction to integral values is specified —
deliberate, recorded. Braces take no part in list sugar: `{a, b}` without a
bar is `E_Parse` with the hint "`[a, b]` is the list; braces are game forms
`{L | R}`".

## 8. Semantics

Evaluation is strict, left-to-right, **except** the non-strict positions
(§1): `if` branches, `and`/`or` right operands, and the right operand of
`⧺` (evaluated only if the left walk reaches nil, §10.4). Bindings live in a
per-world environment. A bare expression statement evaluates and prints
canonical display; non-canonical input is first echoed canonically (the
unparser).

### 8.1 Operator → engine desugaring

| grundy | engine call |
|---|---|
| `a + b` | `Multivector::add`; poly worlds: ring add; game world: disjunctive sum (form-level materialization; total on loopy operands via the product graph, §10.7) |
| `a - b`, `-a` | `sub`/`neg` — scalar `neg()` underneath, never literal −1 (core rule 3); game world: game negation (total on loopy operands — the L/R graph swap) |
| `a ⋅ b` | `alg.mul` / ring product; game world `E_WrongWorld` (group, not ring) |
| `a ∧ b` | `alg.wedge`; game world hint points at `⧺` |
| `a / b` | `a ⋅ inv(b)` — right division; at grade 0 in non-field worlds, exact division (unique `x` with `x ⋅ b = a`), remainder named on failure; literal-shaped ratios are fraction literals (§7.7) |
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
| `ordinal` mul/inv past the verified Kummer tower | `E_KummerEscape` ("below ω^(ω^ω), primes ≤ 727 — see docs/OPEN.md") |
| `surreal` inverse of a non-monomial | `E_NotInvertible` ("only CNF monomials invert exactly; 1/(ω+1) is an infinite Hahn series") |
| `integer`/`omnific` non-unit inverse, non-exact division | `E_NotInvertible`, remainder named |
| `/0`, `% 0`, zero-denominator fraction literal | `E_DivisionByZero` |
| non-dyadic fraction literal in the game world | `E_Domain` (§7.7) |
| grassmann/degenerate inverses | `E_NotInvertible` |
| μ-unfolding past the budget | `E_Fuel` (§9.2) |
| μ-descent past the host frame guard | `E_StackDepth` (§13; a host resource, not fuel) |
| materialized graphs past the node budget — including the finite→loopy embedding of shared-DAG operands | `E_GraphBudget` (§10.7) |

### 8.3 `%` — remainder (the integrality column's operator face)

| world | semantics |
|---|---|
| `integer` | Euclidean remainder, `0 ≤ r < \|b\|` (`-7 % 3 = 2`) |
| `surreal`, `omnific` | `b` must be a monic ω-power `ω↑e` (else `E_Modulus`); result is the CNF tail strictly below `e` — the Hahn mirror of dropping high digits mod `10↑k`. Non-monic moduli rejected deliberately: every nonzero constant is a unit of No, so `7 % 3` would honestly be `0` — a footgun beside the integer world's `1` |
| poly worlds | `Poly::divrem`; `integer[t]` divisors monic |
| any field world, `game` | `E_WrongWorld` — a field divides exactly; the game world has no division at all |

The Euclidean identity is expressible: `(a - a%b)/b ⋅ b + a%b = a`.

### 8.4 `@` — the one application operator

`f@v` substitutes into the hole — `t` in the function worlds, the binders of
a Function — through the substitution homomorphism. Composition is the
non-constant case and is associative: `f@g@x = (f@g)@x = f@(g@x)`. Engine:
`Poly::eval`/`::compose`; ratfunc evaluates `num`/`den` separately (a pole is
`E_DivisionByZero`). Functions: sort-checked substitution then strict
evaluation (§8.6). `@` binds tightest; both operands are atoms or frames.
Non-function scalar worlds reject `@` with `E_WrongWorld`; **the grammar is
world-independent** — literal *forms* parse everywhere, worlds decide
legality at evaluation (the fence principle).

### 8.5 Relations and binding

A relation is a Bool-valued expression (usable anywhere Bool is legal;
relations stay non-chaining). `=` is value equality in every world
(`PartialEq`; game world: §10.5–10.6). `<`, `>`, `∥` are the strict,
strict-reversed, and incomparable cells of the world's canonical partial
order, grade-0 only:

| world | order | consequence |
|---|---|---|
| `integer`, `surreal`, `omnific` | the ring's total order | `∥` identically `false` |
| `nimber`, `ordinal` | the game-value order restricted to nimbers — an antichain plus equality | `<`/`>` identically `false`; `a ∥ b ⟺ a ≠ b` |
| `fp*`, `f*`, function worlds | none | `< > ∥` are `E_WrongWorld` |
| `game` | the full CGT partial order | all four cells live; §10.6 for loopy operands and the nine outcome doubles |

Index relations (`= < >`) are the meta-integer total order; Bool `=` is Bool
equality; `f = g` on Functions is `E_FnSort` (function equality is
extensional and not grundy's to decide).

Binding is `name := expr` (any sort; rebinding allowed). An unbound bare
identifier left of a top-level `=` earns "did you mean `name := …`?".

### 8.6 Capture by substitution; sequences; total sort-checking

A Function value is a **closed AST over its own binders**, produced by
substitution at definition time. No runtime environments, ever. Captured
Element/Index/Bool bindings substitute in as values (visibly — the echo shows
them; Index captures substitute as `#n`); captured Functions beta-reduce, so
a Function value never references another function. Definition-time checking
is complete: sorts, arities, shadowing, unbound names, world-legality of
every operator. The only application-time failures are §8.2's partiality, the
budgets, and sort mismatches at the frame against a declared-default binder
(§6.1).

**Sort-checking is total; non-strictness is not an exemption.** Every operand
of every construct is sort-checked, including operands that evaluation will
skip: `if` branches, `and`/`or` right operands, and the right operand of
`⧺`. `ones ⧺ true` is `E_BoolSort` and `ones ⧺ (x ↦ x)` is `E_FnSort` even
though the append's left walk would never consult them — laziness defers
work, never meaning.

Shadowing: binders may not shadow reserved words, stdlib names, or the
world's generator (`E_Shadow`); duplicate binders are `E_Shadow` (marks do
not distinguish: `(#a, a)` duplicates); binders may shadow ordinary bindings.

Sequences: `{ binding ";" } statement`. Intermediates must be bindings
(`E_SeqValue` — with no effects a discarded value is dead code). At top
level, bindings persist and only a final expression prints; a parenthesized
sequence is an expression form (`f := n ↦ (d := n⋅n; d + 1)`) — `:=` *is*
the let. Display preserves let-structure (closedness, not flatness, is the
invariant).

## 9. Recursion — `=:` and fuel

### 9.1 The equation binder

`name =: rhs` binds `name` to a solution of the equation `name = rhs`, with
`name` in scope symbolically on the right. **One glyph, two polarities,
decided by sort**:

- **Function `=:`** — operational recursion: the body unfolds at call sites
  under fuel. `fact =: n ↦ (if n = 0 then 1 else n⋅fact@(n-1))`. No
  denotational fixpoint claim is made; the semantics is unfolding plus an
  attributable budget.
- **Element `=:`** (game world only) — **guarded coinductive graph
  formation**: the equation closes into a finite cyclic game graph, read up
  to bisimilarity (§10.7). `on =: {on |}` directly executes Siegel's
  defining equation. Everywhere else an Element self-mention is
  `E_WrongWorld` — no fixpoint theory, no fixpoint syntax (`x =: x + 1`
  names nothing in ℤ).
- **Bool and Index `=:`** with a self-mention is `E_FixpointSort`:
  `b =: not b` has no theory here — recursion is for Functions (unfolding)
  and game Elements (graphs). The error says so; it is not a guardedness
  failure and does not speak Element.

Shared rules: `=:` with no self-mention degenerates to `:=` exactly. `:=`
with a self-mention stays `E_Unbound` (hint: "recursive definition? `=:`").
Local `=:` is allowed in body sequences for both polarities; a local helper
may reference the enclosing μ-name and binders. A top-level Function value
carries at most one free name — its own; the bare-name echo prints the
equation form.

### 9.2 Fuel — steps, not depth

Fuel meters **total μ-unfoldings** — every substitution of a μ-bound body
into its call site, all μs draining one shared budget, reset per top-level
statement. Exceeding it is `E_Fuel`, naming the μ that struck zero and the
budget. Depth budgets don't deliver the honesty claim (`fib@100` has depth
~100 and ~φ¹⁰⁰ unfoldings). Default budget **2¹⁶ = 65536**; `:fuel n` is the
REPL knob; `@fuel n` the corpus directive. Non-recursive applications are not
metered (inlining means they cannot loop); engine-internal recursion is not
metered (terminates by construction). Element-`=:` runs graph fixpoints, not
descent — fuel is untouched there, and a μ-*function* recursing along an
infinite spine (`len@ones`) is honestly `E_Fuel`. The host's frame guard is a
separate resource with a separate error (`E_StackDepth`, §13): fuel is steps;
the stack is depth; the kinds never blur.

### 9.3 Equation systems — mutual `=:` groups

A **maximal adjacent run of `=:` bindings** in a sequence (at top level:
consecutive `=:` statements joined by `;`; in a body: the same shape) is one
**simultaneous equation system**: every name in the run is in scope
symbolically in every RHS of the run.

```text
a =: {b |}; b =: {| a}          // one system, two equations
twos =: {2 | woes}; woes =: {2 | twos}   // a period-2 pair, mutually
```

- Game-world Element systems close into **one** cyclic graph with one node
  per equation, guardedness checked with the whole name-set symbolic
  (§10.7): every surviving occurrence of *any* group name must sit strictly
  inside a brace constructor. `E_Unfounded` names the offending equation and
  name.
- A `:=` binding, an expression statement, or a blank line ends the run; two
  runs separated by any of these are two systems (`E_Unbound` across them,
  as ever — the adjacency *is* the grouping, visible in the text).
- Mixed-sort runs: a run whose equations are not all game Elements is
  resolved equation-by-equation (Function `=:` never joins a system —
  mutual *function* groups wait for higher-order at 1.0.0, where Function
  representation changes anyway; the local-helper rule of §9.1 covers most
  shapes today). A Function `=:` adjacent to Element `=:`s simply ends the
  Element run.
- Multi-line entry: a trailing `;` continues the line (§3), so systems are
  writable interactively.
- One-equation systems are exactly the old rule — nothing changes for
  `on =: {on |}`.

## 10. The game world

`:world game` — Elements are game forms over the games pillar
(`games/partizan.rs::Game`) and, through Element-`=:`, finite cyclic game
graphs (`games/loopy/`). No metric, no blades. CGT is the recursive subject;
this is where the language and the repo's thesis converge.

### 10.1 The strata

The game world is stratified, and every operator's stratum is part of its
contract:

- **presentation** — option *order* as entered. Display and indexed access
  (`left(g, i)`) live here. Never semantic.
- **multiform** — the constructors' quotient of presentation: sides as
  **multisets** of multiforms. This is grundy's own stratum, named honestly:
  Conway's form is set-like (duplicate moves to one option are not form
  data), grundy's is deliberately multiplicity-enriched (claim level:
  interpretation) — `{0, 0 |} ≢ {0 |}`, and `1 + 1` displays `{1, 1 |}`. We
  write "form" as shorthand below; the multiset is always meant. `≡`, `⧺`,
  option counts, list structure, `birthday`, and the `stopper` predicate
  live here. Multiform operations are **not** congruences for `=`
  (`{-1 | 1} = 0` yet `{-1 | 1} ⧺ l` is `E_Improper`) — the form/value
  distinction CGT itself is careful about, and the raw structure a future
  misère world needs preserved (§10.9).
- **value** — the CGT quotient: `= < > ∥`, `canon`.
- **outcome** — who wins under optimal play. Outcome is not a fourth
  quotient in a chain; it is a **pairwise observation**: the nine outcome
  doubles (§10.6) read the outcome partition of the conjugate sum
  `G + (-H)`, and `hasdraw` lives here. On finite forms the outcome of
  `G - H` determines *exactly one* of `G > H`, `G ∥ H`, `G = H`, `G < H` —
  outcome observations recover the value relations pairwise (standard
  math), which is emphatically not "outcome and value coincide" (`1` and
  `2` share an outcome class and differ in value). On loopy games even the
  pairwise recovery needs the stopper gate — the split is taught, not
  hidden (§10.6).

Predicate strata, stated exactly: **`stopper` is a presented-graph
predicate** (a property of the graph you built, §10.7); **`hasdraw` is an
outcome predicate** (at least one starting player's optimal result is a
draw). Neither implies the other's stratum: `g =: {0, g | g}` is not a
stopper, has no draws, and `g >> 0` — non-stopper does not mean drawn.

**`≡`, display recognition, and value keys quotient presentation by
multiset** — matching the engine's own order-independent structural
fingerprint. `{1, 2 | 0} ≡ {2, 1 | 0}` is `true`; `{0, 0 |} ≡ {0 |}` is
`false` (multiplicity is multiform data). On cyclic values `≡` is unordered
(graded) bisimilarity of finite unfoldings — α-invariant, decidable by
synchronized descent with per-pair option matching (bipartite perfect
matching per node side; coinductive cycle assumptions are branch-local, so a
failed candidate match discards its optimistic assumptions rather than
leaking them; a cyclic graph never compares `≡`-equal to a finite tree — a
repeated graph node along the synchronized path witnesses genuine
cyclicity). `≡` is **total and terminating on every value**, including
finite forms presented as shared DAGs (the walk is memoized on shared
structure — `g ≡ g` on a 2³⁰-leaf DAG returns, fast; see
`implementation.md`).

### 10.2 Form display and recognition

Form display is structural and canonical: `{` + left options joined `, ` +
`|` + right options joined `, ` + `}`; single spaces separate the bar from
each nonempty side; `{|}`, `{0 |}`, `{1, 2 | 0}`. One carve-out, with a
precedence chain — a form whose option multisets match what a literal builds
displays as that literal:

```text
integer chains → dyadic fractions → nimber standard forms → up/down
  → proper spines […] → raw braces
```

`{1 |}` displays `2`; `{0 | 1}` displays `1/2` (Conway's canonical dyadic
construction, §7.7 — the new rung); `{0 | 0}` displays `*1`; `{0 | *1}`
displays `up`; `{7 | {8 | 0}}` displays `[7, 8]` — and so does `{5 | 0}`
display `[5]`, because a cons whose tail is nil *is* the one-element list. A
form displays as itself when it matches no literal: the switch `{1 | -1}`
(the tail position holds `-1`, neither nil nor cons — an improper list,
legal as data, shown raw) or any multi-option side `{1, 2 | 0}`. Recognition
is structural (multiset), never value-level: `1 + 1` materializes the sum
form and displays `{1, 1 |}`, not `2`; a form merely *equal* to `1/2` stays
braces until `canon`. Value identity is said with `=` or `canon`. Recorded
delights (claim level: interpretation, all structural identities):
`[0] ≡ *1`, `[0, 0] ≡ up`, `down ≡ [*1]` — the uptimal ladder starts inside
list notation.

### 10.3 Lists — the cons-cell discipline

Cons is `{h | t}` (singleton sides; the bar distinguishes head from tail);
nil is `{|} = 0`; `[a, b, c]` is the container literal for the right-nested
spine and `[]` for nil (§7.8). A **proper spine** is nil or a cons whose
tail is a proper spine; everything else is Lisp's dotted/improper case,
legal as data. The accessors are a prelude, not stdlib — definable
in-language:

```text
hd := l ↦ left(l, 0)
tl := l ↦ right(l, 0)
isnil := l ↦ nleft(l) = 0 and nright(l) = 0   // structural — l = 0 is NOT a nil test
```

### 10.4 `⧺` — append, coinductively total on the left

`l ⧺ g` walks the left operand's right-spine. Three outcomes, exhaustive:
(1) the walk reaches nil — `g` is evaluated and grafted at the terminal;
(2) the walk cycles — the append **is the left operand** (`l ⧺ g = l`): an
infinite list never reaches its end, so the right operand is never
consulted — the coinductive identity, operational; (3) the walk hits a node
neither cons nor nil — `E_Improper` (improperness is orthogonal to
cyclicity). The right operand is evaluated *only* in case (1) — `⧺` is one
of the language's non-strict positions, so `ones ⧺ (ones + 0)` is `ones`,
not an error — but it is **sort-checked always** (§8.6): `ones ⧺ true` is
`E_BoolSort`. The right operand is otherwise unrestricted (grafting a
non-list gives an improper list — Lisp's last-argument freedom). Units:
`[] ⧺ l = l`, `l ⧺ [] = l`. Multiform-level, hence not a `=`-congruence.
`+` is **not** append; no operator concatenates arrays.

### 10.5 The second equality and `canon`

- **`a ≡ b`** — multiform equality: multiset-structural (§10.1),
  regular-tree bisimilarity on cyclic values. Bool-valued, relop tier,
  non-chaining. Outside the game world `E_WrongWorld`, not an alias for
  `=`: elsewhere forms *are* values and a silently-coinciding second
  equality would mislead (hint: "`=` is already structural here").
- **`canon(E) → E`** — the engine's canonical form (options canonicalized,
  dominated options deleted, reversible options bypassed). Finite forms
  only until 0.3.8 (`E_Loopy` on loopy values — fusion/simplest form is the
  0.3.8 envelope item).
- The retraction laws, in the language and the corpus:

```text
a = b  ⟺  canon(a) ≡ canon(b)      // canon turns value equality into form equality
canon(canon(x)) ≡ canon(x)          // idempotent
canon(x) = x                        // value-preserving
```

- Cost note, stated as the code has it: `≡` is the cheap structural walk;
  `=` runs mutual order-recursion on finite forms and the nine-cell
  projection on stopper graphs (§10.6) — no canonicalization is performed
  by either; `canon` is the expensive normalization and only ever explicit.
  The default glyph is the mathematically-owned one: the math owns `=`.

### 10.6 Relations — value singles, outcome doubles

The mover-result atoms are `>` (Left wins that instance), `<` (Right wins),
`‿` (draw — infinite play). An **outcome double** is two atoms — *result
when Left starts*, then *result when Right starts* — giving nine relops that
are the 3×3 outcome grid arranged as its own glyphs:

```text
                Right starts:   L wins    draw    R wins
Left starts:  L wins              >>       >‿       ><
              draw                ‿>       ‿‿       ‿<
              R wins              <>       <‿       <<
```

- **Doubles read the outcome of the formal conjugate sum** `G + (−H)`
  (conventionally written `G − H`; in loopy play `−H` is *not* an additive
  inverse — `G + (−G)` need not equal 0, which is exactly why this stratum
  exists). Total on **all** game operands, loopy included: the sum graph is
  finite, and its nine-cell outcome partition is computed by the standard
  retrograde attractor/draw analysis under optimal play — defined
  operationally: a player *wins* if they can force a finite win, the
  position is *drawn* for a mover who cannot force a win but can prevent a
  loss (infinite play is a draw; each player prefers win > draw > loss).
  Exactly one double holds for any pair. On finite forms the five `‿`-cells
  are identically false (the `∥`-in-ordered-worlds precedent). Game world
  only; `E_WrongWorld` elsewhere.
- **Singles are the value stratum, computed as a projection.** On finite
  forms, `= < > ∥` are the classical partition (unchanged). On loopy
  operands the singles require **both presented operands to be stopper
  graphs** — no reachable alternating cycle in the turn-expanded graph
  `(node, mover)`; one-sided pass loops (`over = {0 | over}`) *are*
  stoppers — and then project the double (standard math: Siegel,
  *Combinatorial Game Theory*, GSM 146, Thm VI.2.1 p. 290 with Def VI.1.8
  p. 284 — `G ≥ H` iff Left, moving second, survives `G − H`, where
  surviving means winning or drawing):

```text
{>>, >‿} → `>`        {><} → `∥`        {<>, <‿, ‿>, ‿‿} → `=`        {‿<, <<} → `<`
```

  The gate is on the **operands, never their difference** — the sum of two
  stoppers need not be a stopper (`over + under`), and the theorem holds
  regardless. Beyond stoppers the singles are `E_Loopy`, and the error names
  the alternating turn-state cycle found and the operand side carrying it,
  rendered closed with the first state repeated
  (`left operand has alternating cycle 0:L→0:R→0:L`) — witness-carrying, the
  house style of `E_NotInvertible` naming the remainder. One-stopper biased
  comparison is 0.3.8 envelope work.
- **Refinement, not contradiction.** The doubles refine the singles: on
  stoppers `G = H` legitimately coexists with any of `<>`, `<‿`, `‿>`,
  `‿‿`. The teaching triple: `over = over` is `true` (survival);
  `over ‿‿ over` is `true` (both players stall in `over + under`);
  `over <> over` is `false`. On finite forms the projection degenerates to
  the bijection `>> ↔ >`, `>< ↔ ∥`, `<> ↔ =`, `<< ↔ <` — conformance
  vectors, not prose. Terminology, used consistently: singles are
  *comparisons*; doubles are *outcome-cell tests*.
- **The glyphs move like the math.** Negation is 180° rotation of the grid
  = string-reverse + atom-flip (`>`↔`<`, `‿` fixed):
  `cell(-G, -H) = rotate180(cell(G, H))`, and operand swap acts identically.
  The self-dual cells are `<>`, `><`, `‿‿`. Read them aloud: `<>` is
  *second player wins*, `><` is *first player wins* — the P/N glyphs derive
  themselves. (Known hazard, documented: `<>` means "not equal" in some
  languages; here, on finite forms, it is true exactly when `=` is. The
  tutor teaches; convention lost, shape won.)
- The CGT glyph collision is settled as before: grundy's `↑` is power;
  up/down are the literal atoms `up`, `down` (§7.5).

### 10.7 Element-`=:` — loopy games are equations

`=:` with an Element-sorted RHS and a self-mention (or a mention of any name
in its adjacent system, §9.3) is guarded coinductive definition, legal
exactly here:

```text
on   =: {on |}          off =: {| off}         dud =: {dud | dud}
over =: {0 | over}      ones =: {1 | ones}     // streams are loopy games
l    =: [1, 2] ⧺ l      // purely periodic; ⧺ is guardedness-transparent from the left
a    =: {b |}; b =: {| a}                      // a mutual system (§9.3)
```

- **Guardedness, checked after definition-time reduction — with the
  language's own reduction rules.** The RHS reduces with the system's names
  symbolic, and the reduction honors every non-strict position exactly as
  evaluation does:
  - brace constructors may enclose symbolic occurrences;
  - `⧺` reduces structurally along its **left right-spine only**: a closed
    proper spine unfolds with the tail grafted — symbolic occurrences in
    *head* position are fine, because the walk never inspects heads
    (`g =: [g] ⧺ []` reduces to `[g]`, guarded); a closed cyclic spine
    returns itself and the discarded right operand takes its μ-occurrences
    with it;
  - a **closed** `if` condition or `and`/`or` left operand reduces first,
    and only the surviving branch is examined
    (`dead =: {if true then 0 else dead |}` reduces to `{0 |}` — the dead
    branch's occurrence is discarded, and the equation degenerates to `:=`);
  - every other operator is strict in its operands' options: applying one
    to a μ-containing operand is `E_Unfounded`.
  After reduction every remaining occurrence of every system name must sit
  strictly inside a brace constructor; a bare-root occurrence (`g =: g`,
  `h =: [] ⧺ h`, `k =: k ⧺ [1]`, `m =: m + 1`) is `E_Unfounded`, naming the
  equation and the name.
- **The graph is materialized and classified at definition**: the cyclic
  system becomes a `LoopyPartizanGraph`; outcomes with draws come from the
  retrograde classification. Fuel is untouched.
- **The loopy envelope** (error → value, never breaking):
  - allowed: binding, display, option access, `≡`, `hasdraw`, `stopper`,
    both operands of `⧺`, the nine outcome doubles, singles on stopper
    operands, `+` (the product-graph sum — the result is the sum graph,
    displayed as a program per §10.8) and unary/binary `-` (the L/R graph
    swap).
  - rejected with `E_Loopy`: singles beyond stoppers (witness-carrying),
    `canon` (fusion is 0.3.8).
  - resource-guarded: **every** graph materialization draws on an explicit
    node budget — default **2¹⁶ = 65536**, counted per distinct node at
    first discovery, root included, nothing partial escaping on failure —
    firing `E_GraphBudget` when exceeded. This includes the finite→loopy
    embedding: a finite form enters loopy operations by budget-counted
    expansion, so a shared-DAG operand whose tree unfolding exceeds the
    budget is an honest `E_GraphBudget`, never a hang (the 0.3.5 hole,
    closed). `:graph n` is the REPL knob (`:graph` alone prints the budget)
    and `@graph n` the corpus directive (persist until the next directive;
    `@world`/`:world` resets to default). Graph size is a first-class
    resource axis beside fuel, and "total" always means *mathematically
    total, operationally budgeted*.
- **`hasdraw(E) → Bool`** — an **outcome** predicate (§10.1): true iff at
  least one mover faces a draw — exactly the Bool union of the five
  `‿`-cells against `0`; kept as the one ergonomic convenience over the
  doubles. Identically `false` on finite forms and on every stopper.
  `hasdraw(dud)` is `true`; `hasdraw(on)`, `hasdraw(over)`, `hasdraw(ones)`
  are `false` (alternation: forced returns still hand the mover a win).
- **`stopper(E) → Bool`** — a **presented-graph** predicate (§10.1), the
  singles' gate made user-askable: no reachable alternating cycle in the
  turn-expanded graph. Singles are value-invariant where defined, but the
  decision procedure requires both *presented* operands to be stopper
  graphs.

### 10.8 Loopy display — equation systems, self-contained

Display of loopy values emits **programs**: a value displays as the equation
system that defines it, and the display law (§1 discipline 2) demands the
program be self-contained — evaluating it in a *fresh* session rebuilds the
value up to `≡`. The rules:

- **Anchors.** Every reachable cyclic component gets its equations — on
  every display path (a named root's external cycles included). The grain
  is the component, not the node: a single-name cycle stays one nested
  equation (`l =: {1 | {2 | l}}`, never split in two), while every root of
  a mutual source system keeps its own equation. Well-founded exits
  collapse back into finite forms before display, so recognition still
  fires inside equations (`-ones` prints `g1 =: {g1 | -1}`, and `on + off`
  prints dud's own shape `g1 =: {g1 | g1}`).
- **Names are α-bound, never environment references.** The displayed
  program binds every name it uses; a rebinding can never change the
  *meaning* of an old echo, and the same value displays the same program
  up to α-renaming. Provenance names (user roots, local `=:` names) are
  *reused* for readability so long as the live environment does not bind
  the same name to a **different** graph — a rebound name synthesizes
  instead, which is exactly what keeps rebinding histories honest; a local
  name that has simply left scope keeps its provenance
  (`(q =: {1 | {2 | q}}; {9 | q})` keeps `q`). Synthesized names
  `g1, g2, …` cover the rest — allocated in first-reach order against a
  **collision set**: names already used in this display, provenance names
  in this display, and the current environment's bindings.
- **Systems, emitted in dependency order.** The anchor graph's SCC
  condensation is emitted in reverse-topological order — dependencies
  first — so earlier equations satisfy later references; each nontrivial
  SCC emits as **one adjacent `=:` run** (§9.3), so mutual cycles display
  as the mutual systems they are. A single self-cycle is the degenerate
  one-equation system — the 0.3.5 form, unchanged.
- **Roots.** A loopy *root* echoes as its equation (`> on` prints
  `on =: {on |}`); an interior node re-roots the equation at itself with
  the defining name α-bound (`tl@l` for the period-2 `l` prints
  `l =: {2 | {1 | l}}`); a composite value containing cycles it does not
  root displays as a §8.6 body — the equations, then the structural form:
  `(q =: {1 | {2 | q}}; {9 | q})`. A value needing both a mutual system and
  a final form nests the same way:
  `(a =: {b | a}; b =: {| a}; {9 | b})`.

Round-trips by construction, and by law test (§16): display → fresh session
→ `≡`, across multi-SCC graphs, shared subgraphs, duplicate edges, ambient
name collisions, and rebinding histories.

### 10.9 Misère — the standing boundary

The multiform stratum **preserves the raw move structure a future,
separately specified misère world requires** — multiplicity, list structure,
sums as built. No misère equality or canonical-form claim follows: misère
changes the terminal observation (`{|}` is an N-position), misère equality
is indistinguishability relative to a chosen universe, and normal-play
domination, reversibility, order, and `canon` do not survive the crossing.
When it comes, it comes as `:world game misere ‹universe›` with outcome
relations available before any equality — never as a flag on this world.
`0 = nil = {|} = additive identity` survives; "game ended = second player
wins" does not.

## 11. Stdlib

All thin wrappers; signatures sorted (E = Element, I = Index, B = Bool).
Reserved as identifiers (§3).

| call | worlds | notes |
|---|---|---|
| `rev(E)` | Clifford | `E_GeneralMetric` if `a ≠ ∅` |
| `grade(E, I)` | Clifford | |
| `even(E)` | Clifford | |
| `dual(E)` | Clifford | `None → E_NotInvertible` (pseudoscalar) |
| `coef(E, I)` | Clifford, poly | coefficient of `e_i` / of `t↑i` (grade-0/constant result; total in the Element; out of range → `E_BladeIndex` / zero beyond `deg`); ratfunc: `E_WrongWorld` (deliberate, §7.8) |
| `tr(E[, I])` | nimber, `f*` | Gold chain: `tr(x ⋅ x↑(2↑a))` |
| `frob(E)` | finite fields | Frobenius |
| `deg(E)` | poly worlds | returns Index; `deg(0)` → `E_Domain`; ratfunc: `E_WrongWorld` (recorded refusal, §1) |
| `gcd(E,E)` | poly worlds | monic / positive-primitive results |
| `integral(E)` | `surreal`, `fp*(t)`; ring legs | the (K, 𝒪_K) spine's operator face beside `%`: membership in the ring of integers — `integral(ω)` true, `integral(1/2)` false in `surreal` (𝒪 = Oz); `integral(1/t)` false, `integral([1, 0, 1])` true in `fp2(t)` (𝒪 = F₂[t]). On the ring legs (`integer`, `omnific`, poly worlds) identically `true` — the ring answers yes about itself. Worlds with no shipped pairing (`nimber`, `ordinal`, `fp*`, `f*`, `game`): `E_WrongWorld` — the pairing is structure, not a default |
| `nleft(E)` / `nright(E)` | game | option counts (Index) |
| `left(E, I)` / `right(E, I)` | game | i-th option, 0-indexed; out of range → `E_Domain` |
| `birthday(E)` | game | the **presented** (multiform-stratum) birthday: `0` for `{|}`, else `1 + max` over options — Conway's formation day, read off the form as built. Value birthday is said compositionally: `birthday(canon(g))`. The teaching pair: `birthday({0 \| 2}) = #3` but `birthday(canon({0 \| 2})) = #1` — `{0 \| 2}` *is* `1`, born on day 1; the form/value distinction in Conway's own vocabulary. Loopy: `E_Loopy` (no finite formation day) |
| `canon(E)` | game | §10.5; `E_Loopy` on loopy values until 0.3.8 |
| `hasdraw(E)` | game | outcome predicate, §10.7 |
| `stopper(E)` | game | presented-graph predicate, §10.7 |

Everything else (versors, sandwiches, contractions, meet, spinor norms,
thermography) is deliberately out — reach it from Rust/Python. Stops and
`temperature`/`mean` are 0.3.8 items (after dyadic display beds in); ordinal
sum `G:H` is 0.3.7's headline — the conditional-word move freed the colon
for it, so what remains is its precedence/associativity choice and corpus.

## 12. Display (canonical form, v4)

Every `Display` impl in language scope emits canonical grundy — one rendering
path each. v4 (this version) unifies the monomial families and adds dyadic
fractions and binder marks.

### 12.1 Scalars — one monomial family

Every graded scalar family renders the same way: **descending exponents,
unit coefficients elided on nonconstant terms** (`1⋅t↑2` → `t↑2`, `-1⋅t` →
`-t`; compared via `S::one()`/`S::one().neg()`, never a literal), **the
sign-aware join** (a term rendering that starts with `-` is stripped and
joined with ` - `).

| type | canonical display |
|---|---|
| `Nimber` | `*5` |
| `Ordinal` | star-wrapped: `*5`, `*ω`, `*(ω⋅3)`, `*(ω↑2)`, `*(ω + 1)` |
| `Surreal` / `Omnific` | CNF: `3⋅ω↑2 - ω + 5`, `ω↑-1`, `ω↑(1/2)` — exponent bare iff a signed integer |
| `Integer`, `Fp` | plain int |
| `Fpn` | `3⋅x↑2 + 2⋅x + 1` |
| `Poly` | **joins the family at v4**: `t↑2 - t + 1`, `2⋅t↑3 + t`, not `1 + -1⋅t + 1⋅t↑2` (the v3 ascending explicit-coefficient rule is repealed — it was intentional but not earned; the corpus pins the new law) |
| `RationalFunction` | `(num)/(den)`, each side v4 |

### 12.2 Multivectors

Blades render as wedge expressions `e0∧e1`; coefficients attach
`coeff⋅label` with coefficient-`1` elided and `-1` → `-label`. **Join
rule**: sign-aware, as above (string-level, char-agnostic). **Zero rule**:
the empty multivector renders as `S::zero()`'s display (`*0` in nim-worlds,
`0` elsewhere). **Atomicity**: a rendering is atomic iff it contains no
spaces and no operator characters outside balanced parens; a single leading
`-` is a sign. Atomic coefficients attach bare; non-atomic ones get parens
(`(x + 1)⋅e0∧e1`).

### 12.3 Game forms

§10.2's structural display + multiset recognition chain (now including the
dyadic rung). Loopy values: §10.8 equation-system display.

### 12.4 Minimal marks — Indexes and binders

Canonical display marks Index values `#n` at every sort-neutral position
(binding RHS, statement position, argument frames, conditional branches,
lambda bodies) and leaves them bare exactly where the grammar forces Index
(pure-Index exponent slots after `↑`, stdlib I-slots) — the minimal-mark
rule, the sort-space analogue of minimal parens. **The mark is on the
literal, not the expression**: `x ↦ nleft(x)` displays unmarked — `nleft`
already says Index; `#(…)` wraps are for Index-sorted *literal* interiors,
not every Index-sorted term. One slot is sort-ambiguous rather than forced:
the exponent of base `ω` in the surreal family admits Scalar exponents
(§8.1), so Index marks stay visible there. `grundy@*2` displays `#2`; the
game `2` displays `2`.

**Binder marks follow the same law** (§6.1): the echo shows `#`/`?` on a
binder iff its occurrences do not force its sort.

### 12.5 Functions, Bools, sequences

Functions print `binders ↦ body` (minimal parens; single spaces around `↦`
and the word operators); inlining means composites display expanded (the
REPL is the tutor; deep chains blow up — accepted). Bools print
`true`/`false`. Sequences preserve the user's let-structure. Recursive
functions echo their equation form; mutual Element systems echo as adjacent
`=:` runs (§10.8).

## 13. Error taxonomy

`GrundyError { kind, span, message, hint }`. Errors are built through
centralized constructors; **guidance lives in the `hint` field, never the
message tail** (this is a checked build invariant — see
`implementation.md`), and focused tests assert hints. Kinds:

| kind | trigger | canonical hint example |
|---|---|---|
| `E_Parse` | token/grammar violation | site-specific teaching hints: STAR after a complete operand — "`*` is the nimber prefix; the product is `⋅` (sugar `.`)"; `IDENT(args) :=` — "functions are lambdas: `name := x ↦ …`"; `!=` — "not-equal is `not (a = b)`; `!` is fuzzy `∥`"; lone `‿`/`_` — "mover-result atoms come in pairs"; barless braces — "`[a, b]` is the list; braces are game forms"; relop-tier `\|` — "the braceform bar is structural; fuzzy is `∥` (sugar `!`)"; chained relations — "relations don't chain; parenthesize the Bool"; `?`/`:` at expression tier — "conditionals are words now: `if a then b else c`" |
| `E_Reserved` | `↑↑`, `O(` | "reserved for future precision syntax" |
| `E_ExpSort` | non-Index exponent | "`↑`/`^` is power; the wedge product is `∧`/`&`" |
| `E_IndexSort`, `E_BoolSort`, `E_FnSort` | sort discipline (§6, §8.6) — definition-time conflicts, frame mismatches against declared defaults, and skipped-operand checks | frame mismatch: "declare the binder: `(#i, #j) ↦ …`" |
| `E_FixpointSort` | Bool/Index `=:` with self-mention (§9.1) | "recursion is for Functions (unfolding) and game Elements (graphs)" |
| `E_Shadow` | binder shadows reserved/stdlib/generator; duplicate binders | poly worlds: "`t` is the indeterminate here; `5⋅t + 1` is already a function" |
| `E_SeqValue` | discarded intermediate value | |
| `E_BareInt` | bare integer at Element position in nim-worlds | "did you mean `*3`?" |
| `E_BareOrdinal` | bare `ω` in ordinal world | "values are starred here: `*ω`" |
| `E_WrongWorld` | literal/operator foreign to the session world; unknown world name | unknown `:world` lists the menu and near-matches |
| `E_CnfOrder` | star-literal exponents not descending | "CNF indices are structural: `*(ω + 1)`, not `*(1 + ω)`" |
| `E_KummerEscape` | ordinal mul/inv past the tower | "below ω^(ω^ω), primes ≤ 727 — see docs/OPEN.md" |
| `E_NotInvertible` | failed inverse/exact division | per-world math; remainder named |
| `E_DivisionByZero` | `/0`, `% 0`, ratfunc pole, zero-denominator fraction literal | |
| `E_BladeIndex` | `e‹i›`/`coef` with `i ≥ dim` | |
| `E_DimMismatch` | container length ≠ dim (Clifford) | |
| `E_GeneralMetric` | `rev`/`dual` with `a ≠ ∅` | "reverse is undefined for the Chevalley construction" |
| `E_Unbound` | unknown identifier | "did you mean `q := 5`?"; self-mention: "recursive definition? `=:`"; `omega`: "ω is `ω` (sugar `w`)"; `outcome`/`winner`/`who` as unknown calls: "outcomes are relations against 0: `g > 0` Left wins, `g < 0` Right, `g = 0` second player, `g ∥ 0` first player; draws: the `‿` doubles" |
| `E_Arity`, `E_UnknownFn` | call errors | `up()`/`dim()`/`drawn()`: "`up` is a literal now" / "`hasdraw`" |
| `E_Grade0` | grade > 0 where grade-0 required | |
| `E_Modulus` | `%` modulus outside the world's scope | "moduli here are monic ω-powers: `% ω↑2` truncates the CNF below it" |
| `E_Overflow` | payload past its carrier | |
| `E_Domain` | operand outside an operator's domain (option index out of range; non-dyadic fraction literal in the game world; non-constant polynomial container entry) | game fractions: "only dyadics are short games; `1/3` is not born on any finite day" |
| `E_Fuel` | μ-step budget exhausted (§9.2) — **steps only, never depth** | |
| `E_StackDepth` | the host frame guard (a resource, not fuel — the kinds never blur); message keeps the μ name, the frame limit, and the remaining fuel | |
| `E_Unfounded` | unguarded Element-`=:` (§10.7), naming the equation and name | |
| `E_Improper` | `⧺` left walk hits a non-list node | |
| `E_Loopy` | value-stratum operation beyond its loopy envelope (§10.7) | witness-carrying: names the alternating cycle |
| `E_GraphBudget` | materialized graph past the node budget — including finite→loopy embedding (§10.7) | distinct from `E_Loopy` — a resource, not a theory boundary |

## 14. REPL and files

`grundy/examples/repl.rs` drives the crate's `GrundySession`. Default world
`integer` (dim 0 — the shorthand is canonical, §7); the banner names the
version and world. Colon commands: `:world …`, `:fuel [n]`, `:graph [n]`,
`:env`, `:help [topic]`, `:quit`. A failed `:world` preserves the current
world, its bindings, and the worker.

**The REPL earns the tutor principle**: `:help` is a task-first screen — the
world menu (§7.1) plus one seed line per family (a nim product, a game form +
an outcome relation against 0, a `=:` function, a stream via `⧺`); `:help
‹topic›` (`game`, `nimber`, `functions`, `worlds`) goes one level deeper.
Comment-only lines are no-ops; EOF flushes a pending continuation; unknown
worlds list the menu.

`.og` files are piped sessions: the same statement syntax, `:world` directive
lines included — `cargo run -p grundy --example repl < file.og` is the runner.
One statement per line at depth 0; continuation per §3 (open delimiters or a
line ending in a token that cannot end a statement).

## 15. Host operator alignment (Rust + Python)

The host overloads speak the same dialect as the display. Highlights:

| op | Rust | Python |
|---|---|---|
| wedge | `impl BitAnd` (`a & b`) | `__and__`; `__xor__` raises with the `E_ExpSort` hint |
| power | scalars: `impl BitXor<u128>` (RHS is the meta-integer type — `Nimber ^ Nimber` does not compile, by design); multivectors: `CliffordAlgebra::pow` only | `**`; never `__xor__` |
| ordinal power | no operator; `nim_pow -> Option` | `pow()` raising honestly |
| remainder | no `Rem` impl (Rust `%` truncates; grundy's is Euclidean) — methods only | `__mod__` (Python `%` agrees) |
| evaluation | inherent `Poly::eval`/`compose` | `__matmul__` |
| relations | `Ord` on ordered scalars; `fuzzy()` on nim types; no `PartialOrd` on nim types, no `BitOr`-as-fuzzy | rich comparisons / `fuzzy()`; `Ordinal.__richcmp__` speaks CNF *address* order, the language speaks value order — documented, not unified |
| `↦ if/then/else and/or/not =: ⧺ ≡ {L\|R} # ‿`-doubles, dyadic game literals, binder marks | **none** — grundy spelling only | none |

Game-world exposure to Python remains a binding-scope-policy decision
(`src/py/AGENTS.md`), not part of 0.3.x.

## 16. The conformance suite

**Every observable semantic rule is pinned by the conformance suite** —
three parts, one obligation:

1. **Exact corpus vectors** — [`conformance.txt`](conformance.txt), UTF-8,
   line-based: syntax, canonical display, and errors, hand-blessed.

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

   Corpus files use `//` comments, on their own lines or trailing input.
   Blocks separated by blank lines. The harness is
   `tests/conformance.rs` (pure Rust); it also asserts hint fields on
   the vectors that pin them. Blessing remains an operator workflow: the
   engine can suggest values, the spec stays the oracle.

2. **Law tests** — properties no finite vector list exhausts: the two
   display laws (including loopy display → fresh session → `≡`, randomized
   over multi-SCC graphs, shared subgraphs, duplicate edges, ambient-name
   collisions, and rebinding histories); the retraction laws; the
   negation-rotation and operand-swap laws on fresh two-operand pairs; the
   nine-to-four projection against an independent relation oracle on
   randomized stopper pairs; `⧺` laziness and its total sort-checking.

3. **Differential oracles** — the engine-level independent checks the
   language relies on (the retrograde solver against strategy enumeration on
   seeded graphs; projected singles against graph-level outcome oracles).

**0.3.6 vector obligations** (beyond the standing per-section vectors): the
mutual-system family (definition, guardedness across the name-set, display
re-entry); the display-collision family (ambient `g1`, rebinding histories,
named roots referencing external cycles — the 0.3.5 defect probes, pinned);
`ones ⧺ true` / `ones ⧺ #2` / `ones ⧺ (x ↦ x)` as sort errors;
`g =: [g] ⧺ []` and `dead =: {true ? 0 : dead |}` as legal; `b =: not b` as
`E_FixpointSort`; the depth guard as `E_StackDepth`; shared-DAG operands
hitting `E_GraphBudget` (never hanging) and `≡` returning on shared DAGs;
binder-mark round-trips, conflicts, frame-mismatch hints; whitespace-signed
exponents; extended continuation; the `if`/`then`/`else` family (else-if
chains, branch laziness with total sort-checks, sort agreement, the `? :`
migration hints); dyadic literal/recognition/`E_Domain` family; polynomial container/`coef`/`E_Domain` family; v4 poly display
family; `birthday` teaching pair; `integral` per-world family; world
respelling + dim-0 shorthand + alias echoes; budget-precedence on the
singles' seam (`E_GraphBudget` with the stopper gate passed).

## 17. Version history

| version | date | delta |
|---|---|---|
| 0.1 | 2026-06-12 | core: worlds, scalar literals, Clifford operators, Display v2, conformance harness |
| 0.1.1 | 2026-06-12 | function-shaped poly/ratfunc worlds; `@` `%` exact-division; `deg`/`gcd` |
| 0.2.0 | 2026-06-12 | sorts (Bool, Function), lambdas by substitution, ternary + word operators, relations as values |
| 0.2.1 | 2026-06-12 | `;` sequences/programs; let-bodies; continuation lines |
| 0.3.0 | 2026-07-09 | `=:` + fuel; containers; the game world (forms, `⧺`, `≡`, `canon`, four-way relations); loopy Element-`=:`, streams, coinductive append; host guards |
| 0.3.5 | 2026-07-09/10 | the reflection release: unified spec; multiset `≡`/recognition (retraction laws true); `#` Index literals; `[…]` in both faces; nine-cell outcome relations + stopper-projected singles; total loopy `+`/`-`; `hasdraw`/`stopper`; runtime unification; tutor REPL |
| 0.3.6 | 2026-07-10 | **the second adversarial pass** (this contract): display law restored — self-contained equation-system display, mutual `=:` groups, collision-safe α-names; total sort-checking at non-strict positions; guardedness by the language's own reduction; budgeted finite→loopy embedding, DAG-safe `≡`; `if a then b else c` replaces `? :` (the Bool tier is all words; `:` freed for ordinal sum, `?` solely the binder mark); the binder mark triad (`#`/`?`/bare-is-Element); container totality (fixed/graded/free); dyadic game literals + recognition; `birthday`, `integral`, poly `coef`; world respelling (`fp2[t]`/`fp2(t)`) + dim-0 shorthand; Display v4 (poly joins the monomial family); strata corrections (multiform, outcome-as-observation, predicate refiling); `E_StackDepth`, `E_FixpointSort`; whitespace-agnostic exponents; extended continuation; the spec split (this document) |

The ladder (0.3.7 → 0.3.8 → 0.4.0 = release → 1.0.0 higher-order) lives in
[`docs/CONTINUATIONS.md`](../../docs/CONTINUATIONS.md). Provenance: the staging
corpora, [`docs/DONE.md`](../../docs/DONE.md), and the session records (the
`ogham-036-*` gaslamp threads and the 0.3.6 synthesis document).
