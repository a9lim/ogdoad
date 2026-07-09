# ogham — the ogdoad expression language

Status: **v1 + v1.1 + v2.0 + v2.1 implemented** (2026-06-12);
**v3.0 stubbed** (§19, same date — the stub is pre-contract). For the shipped
language this document is the implementation contract: every decision below
either cashes out as a vector in [`docs/ogham/conformance.txt`](conformance.txt)
or it is not really decided. Implementing agents work until the corpus is green;
judgment calls not covered here go back to the spec, not into the code.

ogham is a small calculator language over the ogdoad core: one world per
session, either a scalar backend + Clifford metric or a function-shaped
polynomial/rational-function world, bindings, closed first-order functions,
booleans, lazy ternary/boolean control, and pure let-sequenced programs. No
recursion, game forms, or floats yet. (§19 stages the remaining growth —
recursion and game forms — into a **lisp-for-games**; what never changes: no
floats, no juxtaposition, no coercions, errors as mathematical content.)
File extension `.og`. The name: og(doad) + the ancient stroke-script — fitting
a language whose operators are strokes and ticks (`*`, `↑`, `∧`, `⋅`, `/`).

---

## 1. Design principles

1. **Weird numbers first.** Scalar literals are the richest part of the
   grammar. `*` belongs to nimbers, not to multiplication.
2. **parse ∘ display = id.** Display (v2, §9) emits canonical ogham; the
   parser's input language is a superset of Display's output language.
3. **Two layers: canonical and sugar.** Canonical uses the unicode math glyphs
   where ASCII is contested (`ω ↑ ∧ ⋅`); ASCII stays canonical where it is
   uncontested (`* e + - / = := < > | [ ] ( )`). Sugar is input-only; the REPL echoes
   canonical (the REPL is the tutor).
4. **Unambiguous to the end.** No juxtaposition anywhere — not even as sugar.
   No inference of worlds from literals. No context-sensitive operators.
5. **One world per session** (core rule 5). Mixing is a parse/eval-time error,
   never a coercion.
6. **Errors are mathematical content.** Partiality (Kummer boundary, monomial
   inverses, non-fields) surfaces as typed errors with the math in the message.
7. **Pure Rust, zero deps, no pyo3 outside `src/py/`** (core rule 1). The
   parser/evaluator is a new `src/ogham/` area; the Python `eval` hook lives in
   `src/py/` behind the `python` feature.

## 2. Symbols and codepoints

| meaning | canonical | codepoint | ASCII sugar | notes |
|---|---|---|---|---|
| omega | `ω` | U+03C9 | `w` | atom; also inside star-literals |
| power | `↑` | U+2191 | `^` | right-assoc; Knuth's arrow |
| wedge | `∧` | U+2227 | `&` | exterior product |
| product | `⋅` | U+22C5 | `.` | the algebra's product; U+00B7 `·` also accepted on input |
| nimber prefix | `*` | — | — | value marker in nim-worlds (§6.3) |
| blade prefix | `e` | — | — | `e0`, `e1`, … basis 1-blades |
| neg / sub | `-` | — | — | unary and binary |
| recip / div | `/` | — | — | unary and binary (§7.4) |
| add | `+` | — | — | |
| remainder | `%` | — | — | Euclidean / CNF-truncation remainder (§7.6) |
| evaluate | `@` | — | — | substitution `t := v`, binds tightest (§7.6; v1.1 worlds) |
| factorial | `!` | — | — | prefix, Index operand (§7.6) |
| equality | `=` | — | `==` | Bool-valued relation (§7.7, §17) |
| less / greater | `<` `>` | — | — | Bool-valued strict order relations (§7.7, §17) |
| fuzzy | `\|` | — | — | incomparable, CGT ∥ (§7.7); structural separator inside future `{L\|R}` forms, like `+ ⋅ ↑` inside star-literals |
| binding | `:=` | — | — | `name := expr` |
| lambda | `↦` | U+21A6 | `~` | first-order Function value (§17) |
| ternary | `? :` | — | — | lazy condition, branches sort-homogeneous (§17) |
| bool words | `and or not` | — | — | lazy word operators; reserved as identifiers (§17) |
| vector | `[a,b,c]` | — | — | `Σ aᵢ⋅eᵢ`; length must equal world dim |
| comment | `#` | — | — | to end of line |

Reserved, must lex but reject with `E_Reserved`: `↑↑`, `{` `}` (game forms
`{L|R}`, contractions), and `O(` (precision tails). `;` is program syntax
since §18 and raises `E_SeqValue` only for a discarded intermediate value.
The name `t` is reserved
only inside poly/ratfunc worlds, where it is the indeterminate; outside them
it is an ordinary identifier whose unbound hint points back to those worlds.

**Unary-fill principle**: a unary form of a binary operator fills the left
operand with the operator's identity. `-a = 0 - a`, `/a = 1/a`. Only the two
inverse-taking operators have non-trivial unary forms; no other operator gets
one. (Prefix `!` is not an exception: it is a standalone prefix operator over
Index operands, §7.6, not a unary form of any binary operator.)

## 3. Lexical structure

- Tokens are self-delimiting; there are **zero juxtaposition / maximal-munch
  rules**. Whitespace separates tokens but is never semantic.
- `INT`: `[0-9]+`, value must fit `u128`. No sign (sign is unary `-`); the one
  exception is a tight signed exponent immediately after `↑` (§5).
- `IDENT`: `[a-z][a-z0-9_]*`, excluding reserved words. Reserved everywhere:
  `w`, `and`, `or`, `not`, and stdlib function names (§8); `true`/`false`
  lex as Bool literals. Reserved per-world: `x` in `f4…f27` worlds (the
  field generator), `t` in shipped poly/ratfunc worlds.
- `e` followed immediately by digits lexes as a BLADE token (`e0`, `e12`).
  `e` alone is an error (not an identifier).
- `*` followed by anything lexes as the STAR prefix token; `*` is never an
  infix operator.
- Sugar substitution happens in the lexer: `w→ω`, `^→↑`, `&→∧`, `.→⋅`, `·→⋅`,
  `==→=`, `~→↦` (into the reserved token, §2). After the lexer, only
  canonical tokens exist.

## 4. Grammar (EBNF)

Statements (one per line; blank lines and comment-only lines are no-ops):

```ebnf
statement   = binding | expression ;
binding     = IDENT ":=" additive ;           (* rebinding allowed; binds values, not verdicts *)

expression  = additive [ relop additive ] ;   (* relations not nestable *)
relop       = "=" | "<" | ">" | "|" ;
additive    = mulexpr { ("+" | "-") mulexpr } ;
mulexpr     = wedge   { ("⋅" | "/" | "%") wedge } ;
wedge       = unary   { "∧" unary } ;
unary       = { "-" | "/" } power ;
power       = appl [ "↑" exponent ] ;         (* right-assoc via recursion *)
appl        = atom { "@" atom } ;             (* evaluation, left-assoc; §7.6 *)
exponent    = [ "-" ] INT
            | "(" expression ")" ;            (* Index sort; Scalar iff base is ω in surreal-family worlds *)
atom        = INT | starlit | "ω" | BLADE | vector | call
            | factorial | IDENT | "(" expression ")" ;
factorial   = "!" ( INT | "(" expression ")" ) ;   (* operand is Index sort; §7.6 *)
vector      = "[" expression { "," expression } "]" ;
call        = IDENT "(" [ arglist ] ")" ;
arglist     = arg { "," arg } ;
arg         = expression ;                    (* sort checked per signature *)

starlit     = "*" ( INT | "ω" | "(" cnf ")" ) ;
cnf         = cnfterm { "+" cnfterm } ;       (* strictly descending exponents, else E_CnfOrder *)
cnfterm     = INT
            | "ω" [ "↑" cnfexp ] [ "⋅" INT ] ;
cnfexp      = INT | "ω" | "(" cnf ")" ;
```

Notes:

- **Star-literals are structural, not arithmetic.** Inside `*(…)` the symbols
  `+ ⋅ ↑` build a CNF ordinal *index* (the nimber's address in On₂), they do
  not evaluate. Exponents strictly descend or `E_CnfOrder`. Outside the star,
  all arithmetic is nim arithmetic. `*(ω + 1)` is the nimber at ordinal ω+1;
  `*ω + *1` is a nim-sum that happens to equal it.
- Unparenthesized star applies only to `INT` and bare `ω`: `*5`, `*ω`.
  Everything else takes parens: `*(ω↑2)`, `*(ω⋅3 + 5)`. So `(*ω)↑2` (nim
  square) and `*(ω↑2)` (index ω²) are visibly different, settling the binding
  question: **the star binds tighter than `↑`**, i.e. `*ω↑2 = (*ω)↑2`.
- The surreal-family worlds (`surreal`, `omnific`) allow CNF **at expression
  level, unstarred and live**: `3⋅ω↑2 - ω + 5` is ordinary arithmetic over
  monomials. `ω↑e` with non-integer `e` is the Hahn monomial constructor and
  requires base exactly `ω` (§7.3).

## 5. Precedence (tight → loose)

```text
atoms:  INT, *‹i›, ω, e‹i›, [a,b,c], f(...), !‹i›, (...)
@           evaluation, left-assoc; both operands atoms (f@7, f@(t + 1))
↑           power, right-assoc (2↑3↑2 = 2↑9); tight signed INT exponent ok (ω↑-1)
unary - /   neg, reciprocal
∧           wedge
⋅  /  %     product, right-division, remainder, left-assoc
+  -        add, subtract
=  <  >  |  relations (non-associative, top level only)
```

Wedge tighter than `⋅` follows Hestenes (outer binds tighter than geometric).
Check: `*3⋅e0∧e1` = `*3 ⋅ (e0∧e1)`. Display v2 relies on this: blade terms
print unparenthesized.

**Host-language caveat** (§13): Rust and Python cannot reproduce this table
for the overloaded operators (`&` binds looser than `+` in Python). The
precedence above is ogham's, full stop; host code uses parens.

## 6. Worlds

A session holds exactly one world plus environment. The Clifford-capable worlds
monomorphise a scalar backend into a `CliffordAlgebra<S>`. The function-shaped
v1.1 worlds are scalar polynomial/rational-function evaluators with no Clifford
metric. Worlds are declared by colon-command (REPL) or a leading directive line
(`.og` files use the same syntax without the colon prompt):

```text
:world ‹name› ‹dim› q=[s0,…,s(n-1)] [b=[(i,j):s, …]] [a=[(i,j):s, …]]
:world ‹name› ‹dim› grassmann
:world nimber gold(m,a)            # dim = m, metric = forms::trace_form::gold_form(m,a)
:world ‹name› 0                    # pure scalar work, no metric
:world ‹poly/ratfunc name›          # function-shaped v1.1 world
```

`q`/`b`/`a` mirror `Metric::diagonal` / `::new` / `::general`
(src/clifford/engine/metric.rs): `q` dense length-n, `b`/`a` sparse `i<j`
pairs. Values are scalar literals of the world. Declaring `a≠∅` prints a
warning that `rev`, `dual`, and everything built on reverse is unavailable
(the engine panics there; ogham refuses earlier with `E_GeneralMetric`).
`dim ≤ 128` (`MAX_BASIS_DIM`).

**Typing.** Two value sorts only. **Element**: every value in a world is a
`Multivector<S>`; pure scalars are grade-0 elements (in `dim 0` worlds,
everything is grade-0). **Index**: meta-integers (`i128`) used for exponents,
grades, blade indices, stdlib integer args; Index expressions allow
`+ - ⋅ ↑` and parens, nothing else. Position determines sort; there are no
coercions between sorts.

### 6.1 v1/v1.1 world menu (fixed dispatch table)

Const-generic backends require a compiled-in menu; v1 ships:

| world name(s) | backend | field? | notes |
|---|---|---|---|
| `nimber` | `Nimber` (u128) | yes | F_{2^128} |
| `ordinal` | `Ordinal` | partial | Kummer-checked (§7.5) |
| `surreal` | `Surreal` | partial | monomial inverses only |
| `omnific` | `Omnific` | no (units ±1) | |
| `integer` | `Integer` (i128) | no (units ±1) | |
| `fp2 fp3 fp5 fp7` | `Fp<2|3|5|7>` | yes | |
| `f4 f8 f16` | `Fpn<2,2|3|4>` | yes | char-2 extension fields |
| `f9 f27` | `Fpn<3,2|3>` | yes | |
| `f25` | `Fpn<5,2>` | yes | |
| `poly2 poly3 poly5 poly7` | `Poly<Fp<2|3|5|7>>` | no | `F_p[t]`, function-shaped, no metric |
| `polyint` | `Poly<Integer>` | no | `ℤ[t]`, monic division boundary |
| `ratfunc2 ratfunc3 ratfunc5 ratfunc7` | `RationalFunction<Fp<2|3|5|7>>` | yes | `F_p(t)`, function-shaped, no metric |

(The six `f*` names match the Python binding classes `F4…F27`,
src/py/scalars.rs. Extending the menu = adding one arm to the dispatch enum.)

Further out: precision worlds (`Qp/Qq/Laurent/Ramified/Gauss/Adele` —
`O(p^k)` literal design is its own iteration); games mode (`{L|R}`).

### 6.2 Integer literals per world (the `from_int` trap)

`Scalar::from_int` is the ℤ-ring map — in char-2 backends `from_int(3) = 1`.
Literal meaning is therefore defined per world and **never** via `from_int`
in nim-worlds:

| world | bare `INT` at Element position |
|---|---|
| `nimber`, `ordinal` | **error `E_BareInt`**, hint: `did you mean *3?` |
| `surreal`, `omnific`, `integer` | exact integer (`from_int`, overridden exactly there) |
| `fp*`, `f*` | residue (`from_u128`-style reduction; `f*` worlds: degree-0 constant) |
| `poly*`, `polyint` | constant polynomial over the coefficient world |
| `ratfunc*` | constant rational function over the coefficient world |

Bare `INT` at Index position is always a meta-integer, in every world.

### 6.3 Star-literals per world

- `nimber` world: `*n` with `n` a u128 — `Nimber(n)` (the representation
  constructor, src/scalar/finite_field/nimber/mod.rs). `*` alone is sugar for
  `*1` (CGT star); canonical prints `*1`.
- `ordinal` world: `*n`, `*ω`, `*(cnf)` — assembled from `Ordinal::from_u128`
  / `::monomial` / `::omega_pow` per the structural CNF. The star is the value
  marker; there are no unstarred Element literals in this world.
- All other worlds: `E_WrongWorld`, hint names the world that wanted it.

### 6.4–6.8 Other literal forms

- `ω` (atom): `surreal`/`omnific` worlds — `Surreal::omega()`. In `ordinal`
  world bare `ω` is `E_BareOrdinal` (hint: `*ω`); the glyph appears there only
  inside star-literals.
- Dyadic/rational values are spelled with division: `1/2`, `3/2` (the field
  operation *is* the literal syntax; in non-field worlds non-exact division
  errors honestly — `1/2` in ℤ names no integer, §7.6).
- `f*` worlds: the generator is the reserved identifier `x`
  (`Fpn::generator()`); elements are reached arithmetically (`x↑2 + x + 1`).
- `e‹digits›` blades: `alg.e(i)`, `E_BladeIndex` if `i ≥ dim`.
- `poly*`/`polyint`/`ratfunc*`: reserved `t` is the indeterminate. Fractions
  print as `(num)/(den)`; `[…]` remains vector syntax.

## 7. Semantics (desugaring to the engine)

All file:line references are to this checkout.

| ogham | engine call |
|---|---|
| `a + b` | `Multivector::add` (multivector.rs:85) |
| `a - b` | `Multivector::sub` (:109) — scalar `neg()` underneath, never literal −1 (core rule 3) |
| `-a` | `Multivector::neg` (:95) |
| `a ⋅ b` | `alg.mul(&a, &b)` (algebra.rs:141) |
| `a ∧ b` | `alg.wedge(&a, &b)` (algebra.rs:153) |
| `a / b` | `a ⋅ inv(b)` — **right division**; noncommutative worlds beware, documented not hidden. At grade 0 in non-field worlds, falls back to **exact division** — the unique `x` with `x ⋅ b = a` (§7.6): `6 / 3 = 2` in ℤ, `7 / 3` still `E_NotInvertible` |
| `/a` | grade-0: `Scalar::inv` else `alg.multivector_inverse(&a)` (inverse.rs:9); `None → E_NotInvertible` |
| `a % b` | per-world remainder — Euclidean in ℤ, CNF truncation in the surreal family, `divrem` in v1.1 poly worlds, rejected in fields (§7.6) |
| `f @ v` | substitution `t := v` in the function-shaped v1.1 worlds; `E_WrongWorld` in every v1 world (§7.6) |
| `!n` | factorial of an Index, landing as the bare integer literal `n!` would per §6.2 (§7.6) |
| `a ↑ k` (k ≥ 0) | iterated `alg.mul`, left fold; `a↑0 = 1` |
| `a ↑ -k` | `(/a) ↑ k` |
| `ω ↑ s` (surreal world, s an Element) | `Surreal::omega_pow(s)` — Hahn monomial constructor; any other base with Element exponent is `E_ExpSort` |
| `[a0,…,a(n-1)]` | `Σ alg.scalar_mul(&ai, &alg.e(i))`; length ≠ dim → `E_DimMismatch` |
| `a = b` | `PartialEq`, prints `true`/`false` (§7.7) |
| `a < b`, `a > b`, `a \| b` | the world's canonical partial order, grade-0 only (§7.7) |

Evaluation is strict, left-to-right; bindings live in a per-world environment
(cleared on `:world`). A bare expression statement evaluates and prints the
value's canonical display. If the *input* was not already canonical, the REPL
first echoes the canonical form of the parsed expression (the unparser, §10),
then the value.

### 7.5 Partiality (the honest edges)

| operation | behavior |
|---|---|
| `ordinal` mul/inv escaping the verified Kummer tower | `Ordinal::nim_mul`/`checked_inv` return `None` → `E_KummerEscape` ("beyond the source-verified tower below ω^(ω^ω)"). ogham never calls the panicking `Scalar::mul` path on Ordinal. |
| `surreal` inverse of a non-monomial | `Surreal::inv = None` → `E_NotInvertible` ("only CNF monomials invert exactly; 1/(ω+1) is an infinite Hahn series") |
| `integer`/`omnific` inverse of non-units | `E_NotInvertible` (unary `/a` fills with `1`, so `/3` = `1/3` still errors) |
| `integer` non-exact division | `E_NotInvertible`, the remainder named in the message (§7.6) |
| `/0` and `% 0` anywhere | `E_DivisionByZero` |
| grassmann/degenerate inverses | `multivector_inverse → None → E_NotInvertible` |

### 7.6 The operator grab bag (`%`, `@`, `!`)

Three operators over grade-0 elements; a grade > 0 operand is `E_Grade0`
anywhere in this section. None of them appears in any value's display, so
Display v2 (§9) is untouched.

**`a % b` — remainder.** The operator face of the place table's integrality
column (`scalar/integrality.rs`): reduce `a` modulo `b` against the world's
notion of integral cofactor, keeping the canonical representative.

| world | semantics |
|---|---|
| `integer` | Euclidean remainder, `0 ≤ r < \|b\|` (`rem_euclid`: `-7 % 3 = 2`); `b = 0` → `E_DivisionByZero` |
| `surreal`, `omnific` | `b` must be a **monic ω-power** `ω↑e` — a single CNF term with coefficient `1`, any exponent, so `1 = ω↑0` and `ω↑(1/2)` qualify — else `E_Modulus`. Result: the CNF tail strictly below `e`: `(3⋅ω↑2 - ω + 5) % ω↑2 = -ω + 5`; `x % ω` drops the ω-and-above part; `x % 1` is the infinitesimal part. This reduces mod `ω↑e ⋅ R` (`R` = the exponent-≥0 subring), the Hahn mirror of dropping high digits mod `10↑k`. Non-monic moduli are rejected *deliberately*: every nonzero constant is a unit of No, so `7 % 3` would honestly be `0` — a footgun beside the integer world's `1`. Hint: integer remainders live in the `integer` world. |
| `poly2`/`poly3`/`poly5`/`poly7`, `polyint` | polynomial remainder via `Poly::divrem` (poly.rs:222), `deg r < deg b`; `polyint` divisors must be monic (`divrem` inverts the leading coefficient); `b = 0` → `E_DivisionByZero` |
| `nimber`, `ordinal`, `fp*`, `f*`, `ratfunc*` — any field world | `E_WrongWorld` — a field divides exactly, so the remainder is identically zero; returning that `0` silently would mislead more than help |

**Exact division.** At grade 0 in non-field worlds, `a / b` means **exact
division** — the unique `x` with `x ⋅ b = a` — so `6 / 3 = 2` while `7 / 3`
is `E_NotInvertible`, with the remainder named in the message. Polynomial
worlds use the same exact-division rule through `divrem`; `polyint` keeps the
monic-divisor boundary. Wherever `inv(b)` exists this agrees with §7's
`a ⋅ inv(b)`, and it makes the Euclidean identity expressible:
`(a - a%b)/b ⋅ b + a%b = a`. Exact division does not loosen the
surreal/omnific monomial-inverse boundary — general CNF long division has no
termination story (`1/(ω+1)` all over again).

**`f @ v` — evaluation (substitution).** `f@v` substitutes `t := v` through
the substitution homomorphism: `(5⋅t + 1)@7 = 36` in `polyint`. The
argument is any in-world Element, so a non-constant argument is composition
— `(t↑2)@(t + 1) = (t + 1)↑2` — and substitution is associative, so the
left-assoc chain `f@g@x` is unambiguous. Engine calls: `Poly::eval`
(poly.rs:202, Horner) for constants, `Poly::compose` (the same Horner loop
over `Poly` arithmetic) for the general substitution. `ratfunc` evaluates
`num`/`den` separately; a vanishing denominator is `E_DivisionByZero` (the
pole is the honest error). `@` binds tightest of all operators
(`f@7↑2 = (f@7)↑2`) and both operands are atoms: `f@(x + 1)` takes parens,
and there is no tight signed form (`f@(-3)` — the `↑-1` exception exists
for Display, which never emits `@`). Non-function worlds reject `@` with
`E_WrongWorld` ("evaluation lives in the function-shaped worlds —
poly/ratfunc, v1.1"); the grammar is world-independent.

**`!n` — factorial.** Prefix, operand an **Index** (meta-integer): `!5`,
`!(2⋅3)`. One rule: `!n` computes the factorial at the Index level and
lands it in the world exactly as the bare integer literal `n!` would land
(§6.2). So:

| world | `!n` |
|---|---|
| `integer`, `omnific`, `surreal` | exact `n!`; `!33` is the i128 roof, `!34` → `E_Overflow` |
| `fp*`, `f*` | the residue of `n!`, computed by running product in-world (no overflow): Wilson's theorem is a one-liner — `!6 = -1` in `fp7` — and `!n` is `0` once `n ≥ p` |
| `nimber`, `ordinal` | `E_BareInt`, like any bare integer trying to enter a nim-world — the ℤ-map collapses `n!` to `*0`/`*1` |

A negative operand (`!(0-2)`) is `E_Domain`. The result is an Element and
the operand an Index, so `!` does not nest — `!(!3)` is `E_IndexSort` — and
factorial gets no host operator (§13).

### 7.7 Relations (`=`, `<`, `>`, `|`) and binding (`:=`)

A relation statement prints `true`/`false`; relations are verdicts, not
values — they appear only at top level (§4), and a binding binds a value
(`name := a = b` does not parse).

- **`a = b` — equality.** Every world, full multivectors: `PartialEq`. The
  one relation with no order content.
- **`a < b`, `a > b`, `a | b`** — the strict, strict-reversed, and
  *incomparable* cells of the world's canonical partial order; grade-0 only
  (`E_Grade0`). Together with `=`, exactly one of the four holds wherever a
  canonical order exists:

| world | order | consequence |
|---|---|---|
| `integer`, `surreal`, `omnific` | the ring's total order | `a \| b` is identically `false` |
| `nimber`, `ordinal` | the CGT game-value order restricted to nimbers — an antichain plus equality: for `m ≠ n`, `*m + *n = *(m⊕n)` is nonzero and fuzzy with `0` | `<`/`>` identically `false`; `a \| b ⟺ a ≠ b`. The `ordinal` world's CNF *address* order is not the value order and is not exposed here |
| `fp*`, `f*` | none — no order is compatible with a finite field, and no canonical game reading exists | `<` `>` `\|` are `E_WrongWorld` |

Binding is `name := expr` (rebinding allowed; per-world environment, cleared
on `:world`). An unbound bare identifier on the left of a top-level `=`
earns the `E_Unbound` hint `did you mean name := …?` (§11) — the
muscle-memory catch for the `=`/`:=` split, alongside the `==→=` sugar (§3).

## 8. Stdlib v1/v1.1

Eight functions, all thin wrappers; signatures are sorted (E = Element,
I = Index):

| call | engine | notes |
|---|---|---|
| `rev(E)` | `alg.reverse` (algebra.rs:173) | `E_GeneralMetric` if `a ≠ ∅` |
| `grade(E, I)` | `alg.grade_part` (:193) | |
| `even(E)` | `alg.even_part` (versor.rs:13) | |
| `dual(E)` | `alg.dual` (versor.rs:183) | `None → E_NotInvertible` (pseudoscalar) |
| `tr(E, I)` | `nim_trace(x, m)` (artin_schreier.rs:11) | nimber world, grade-0 arg; m a power of 2 ≤ 128; `f*` worlds: `FieldExtension::trace` (extension.rs:60), 1-arg form `tr(E)` |
| `frob(E)` | `FiniteField::frobenius` (finite_field/mod.rs:48) | finite-field worlds, grade-0 arg |
| `deg(E)` | `Poly::degree` | polynomial worlds only; returns an Index, so it does not reduce mod p; `deg(0)` → `E_Domain` |
| `gcd(E,E)` | `Poly::gcd` / primitive integer polynomial gcd | polynomial worlds only; finite-field results are monic, `polyint` returns the positive-leading primitive integer factor |

Everything else (versors, sandwiches, contractions, meet, spinor norms) is
deliberately out of v1/v1.1 — reach those from Rust/Python. The Gold chain
works day one: `tr(x ⋅ x↑(2↑a), m)`.

## 9. Display v2 (canonical form)

Every `Display` impl in language scope emits canonical ogham — one rendering
path each (the Multivector path is unified, multivector.rs:59-83).

| type | canonical display |
|---|---|
| `Nimber` | `*5` |
| `Ordinal` | star-wrapped: `*5`, `*ω`, `*(ω⋅3)`, `*(ω↑2)`, `*(ω + 1)`, `*(ω↑(ω))` |
| `Surreal` | `3⋅ω↑2 - ω + 5`, `ω↑-1`, `ω↑(1/2)`, `ω↑(ω)` — explicit `⋅`, `↑`; exponent bare iff (signed) integer, else parenthesized |
| `Omnific` | delegates to Surreal |
| `Integer`, `Fp` | plain int |
| `Fpn` | `3⋅x↑2 + 2⋅x + 1` (coefficients reduce mod p) |
| `Poly` | `1 + 2⋅t` — variable `t` (matches `F_q[t]`; `x` belongs to Fpn); coefficient parens only when the coefficient renders non-atomically |
| `RationalFunction` | `(num)/(den)` — `[…]` belongs to vectors |
| `Multivector` | blades `e0∧e1`; coefficients `c⋅e0∧e1` with the atomic-parens rule (`(x + 1)⋅e0∧e1`); coefficient `1` elided, `-1` → `-e0∧e1`; **join rule**: if a term's rendering starts with `-`, strip it and join with ` - ` instead of ` + ` (string-level, char-agnostic — no sign predicate on `Scalar` exists or is wanted); **zero rule**: the empty multivector renders as `S::zero()`'s display (`*0` in nim-worlds, `0` elsewhere — a bare `0` would not round-trip where bare integers are `E_BareInt`) |

**Atomicity (operational rule)** for the coefficient-parens decisions above: a
rendering is atomic iff it contains no spaces and no operator characters
(`⋅ ∧ ↑ /`, internal `+ -`) outside balanced parentheses; a single *leading*
`-` is a unary sign, not an operator — it attaches bare and is then lifted by
the join rule. So `42`, `-2`, `*5`, `*ω`, `x`, and `*(ω⋅7)` are atomic (the
star-literal is self-delimiting); `x + 1` and `ω↑-1` are not. Atomic coefficients attach bare (`*(ω⋅7)⋅e0∧e2` — never
double-wrapped); non-atomic ones get parens (`(x + 1)⋅e0∧e1`).

Out of scope: `CliffordInvariants` names (`M_2(R)` …), tropical display,
game displays, error-message strings.

## 10. The unparser

A canonical pretty-printer over the AST, used for (a) the REPL echo of
non-canonical input and (b) conformance `~` vectors. Rules: canonical glyphs;
minimal parens per §5 precedence (re-parsing the output must yield the same
AST); spacing exactly as Display v2 emits: single spaces around
`+ - = < > | :=` and after `,`; `⋅ / % @ ∧ ↑`, unary operators, and prefix
`!` tight (`3⋅ω↑2 - ω + 5`, `*ω⋅e0∧e1`, `7%3`, `f@7`, `!5`).

## 11. Error taxonomy

Every error is `OghamError { kind, span, message, hint: Option<String> }`.
Kinds and canonical hints (conformance `!` vectors match on kind + message
substring):

| kind | trigger | hint example |
|---|---|---|
| `E_Parse` | token/grammar violation | |
| `E_Reserved` | `↑↑ { } O( ↦ ? ; :` (bare) | "reserved for future games/precision/function syntax" |
| `E_ExpSort` | non-integer exponent, e.g. `e0^e1` | "`↑`/`^` is power; the wedge product is `∧`/`&`" |
| `E_IndexSort` | Element where Index expected, and vice versa | |
| `E_BareInt` | bare integer at Element position in nim-worlds | "did you mean `*3`?" |
| `E_BareOrdinal` | bare `ω` in ordinal world | "values are starred here: `*ω`" |
| `E_WrongWorld` | literal **or operator** form foreign to the session world (`*3` in surreal; `%` in a field world; `@` outside poly/ratfunc) | "`*3` is a nimber; this is the `surreal` world" |
| `E_CnfOrder` | star-literal exponents not strictly descending | "CNF indices are structural: write `*(ω + 1)`, not `*(1 + ω)`" |
| `E_KummerEscape` | ordinal mul/inv past the verified tower | "below ω^(ω^ω), primes ≤ 709 — see docs/OPEN.md" |
| `E_NotInvertible` | failed `inv`/`multivector_inverse`/`dual` | per-world math in message (§7.5) |
| `E_DivisionByZero` | `/0` | |
| `E_BladeIndex` | `e‹i›` with i ≥ dim | |
| `E_DimMismatch` | vector length ≠ dim; vector in dim-0 world | |
| `E_GeneralMetric` | `rev`/`dual` with `a ≠ ∅` | "reverse is undefined for the Chevalley construction" |
| `E_Unbound` | unknown identifier | bare LHS of a top-level `=`: "did you mean `q := 5`?" |
| `E_Arity`, `E_UnknownFn` | call errors | |
| `E_Grade0` | grade > 0 element where a grade-0 scalar is required (`tr`/`frob` args; `%` `@` `!` operands) | |
| `E_Modulus` | `%` modulus outside the world's scope (surreal/omnific non-ω-power) | "moduli here are monic ω-powers: `% ω↑2` truncates the CNF below it" |
| `E_Overflow` | integer payload past its carrier (`INT` beyond u128 at lex; `!34`; iterated integer products) | |
| `E_Domain` | operand outside an operator's mathematical domain (`!` of a negative Index) | |

## 12. REPL

`examples/ogham_repl.rs` (the binary driver; the library lives in
`src/ogham/`). The REPL layer owns a dispatch enum over the §6.1 menu — one
arm per monomorphised `CliffordAlgebra<S>` — which is exactly how rule 5 is
preserved. Colon-commands (REPL only, not in the grammar): `:world …` (§6),
`:env` (bindings + world summary), `:help`, `:quit`. Echo behavior per §7.
Invariant queries (`:arf` etc.) deferred — the colon-command namespace is
where they will land, not the function namespace.

## 13. Host operator alignment (Rust + Python)

The host-language overloads speak the same dialect as the display.

| op | Rust | Python |
|---|---|---|
| wedge | `impl BitAnd for Multivector` (`a & b`); no `BitXor`-as-wedge | `__and__`; `__xor__` raises `TypeError` with the §11 `E_ExpSort` hint during a deprecation window |
| power | scalars: `impl BitXor<u128>` for total-product backends (`x ^ 3`, square-and-multiply via `mul`); RHS is the meta-integer type, so no clash with any element-element op. **Multivectors get no power operator** — the geometric product needs the metric, so power is `CliffordAlgebra::pow(&self, v: &Multivector<S>, k: u128)` (ogham's `↑` desugars to it; negative exponents stay in the evaluator via `multivector_inverse`) | **`**` (`__pow__`)** — Python has a native power operator and the Py multivector classes are algebra-bound, so this works where the Rust operator can't; do not bend `__xor__` into power |
| ordinal power | **no operator.** `Ordinal` omits owned `*` because nim-mul is partial; an `^` that panics through iterated partial mul would contradict that deliberate omission. `Ordinal::nim_pow(&self, k: u128) -> Option<Ordinal>` sits beside `nim_mul` | same: `pow()` method returning/raising honestly |
| product | `*` stays `Mul` (Rust has no native power operator to displace it; `⋅` isn't typeable as an operator) | `*` stays |
| remainder | **no `Rem` impl.** Rust's native `%` truncates toward zero while ogham's is Euclidean (`-7 % 3 = 2`); an `impl Rem for Integer` disagreeing with `i128 %` on negatives is the `Nimber ^ Nimber` class of footgun. Methods only (`Integer` is transparent i128; `Poly::rem`) | **`__mod__`** on `Integer` and the v1.1 poly classes — Python's native `%` is already Euclidean for positive moduli (`-7 % 3 == 2`), so the dialects agree |
| evaluation | Rust has no `@` operator; inherent `Poly::eval`/`Poly::compose` | **`__matmul__`** — Python's `@` lands on the poly/ratfunc classes with exactly ogham's meaning; Python binds `@` at the multiplicative level, far looser than ogham's tightest-binding `@` (the flag below applies) |
| factorial | none — deliberately; `!` is ogham spelling only | none (`!` isn't overloadable; a `factorial` free function would be scope creep on a literal-level operator) |
| relations | `Ord`/`PartialOrd` on the totally ordered scalars (`Integer`, `Rational`, `Surreal`, `Omnific` — delegating to the inherent `cmp`s, the established shadow pattern); `fuzzy()` on `Nimber`/`Ordinal` (= `a ≠ b`, the game-value confusion). Deliberately **no** `PartialOrd` on the nim types — `partial_cmp = None` beside `Ordinal`'s total address `cmp` would be incoherent — and **no** `BitOr`-as-fuzzy: bitwise expectations are the `Nimber ^ Nimber` footgun class | rich comparisons on the ordered classes; `fuzzy()` on the nim classes. **Dialect note**: the shipped `Ordinal.__richcmp__` compares CNF *addresses* (the ordinal order); ogham's `ordinal` world compares *game values* (§7.7). Hosts speak address, the language speaks value — documented, not unified |

Two flags, decided here:

- **Nimber `^` danger**: Rust users may expect `Nimber ^ Nimber` = XOR =
  nim-*addition*. The power overload takes `u128` on the right, so
  `Nimber ^ Nimber` simply does not compile — the type system is the
  disambiguation. Never implement element-element `BitXor` on any backend.
- **Precedence mismatch is documented, not fixed**: Python's `&` binds looser
  than `+` (so `a + b & c` ≠ ogham's reading), Rust's `^` looser than `*`, and
  Python's `@` multiplicative-level. Host code parenthesizes;
  rustdoc/docstrings on the overloads say so.

## 14. Conformance corpus

`docs/ogham/conformance.txt`, UTF-8, line-based:

```text
@world ‹world-decl args, exactly as after ":world"›   # resets bindings
> ‹input line›            # statement, exactly as typed (may use sugar)
~ ‹canonical unparse›     # optional: expected canonical echo of the input
= ‹expected display›      # value line; or:
! ‹E_Kind›: ‹message substring›
```

Blocks separated by blank lines; `@world` persists until the next `@world`.
The harness is `tests/ogham_conformance.rs` (pure Rust, reads the file,
no Python). The Python `ogham_eval` hook is validated through `demo.py` and
focused smoke probes; a pytest mirror can reuse the same corpus later if the
Python package grows a dedicated test tree. The corpus ships with
hand-verified vectors (small nim arithmetic, char-2 wedges, dyadic surreals,
Conway's `(*ω)↑3 = *2`). Corpus expansion/blessing remains an operator
workflow: the engine can suggest values, but the spec stays the oracle for
syntax, sorts, and errors.

Pre-build staging: vectors for spec'd-but-unbuilt versions are blessed into
sibling staging files the harness does not read. The v2.0 and v2.1 slices of
[`conformance_v2.txt`](conformance_v2.txt) were merged into
[`conformance.txt`](conformance.txt) on 2026-06-12; the staging file is now
kept as provenance for those blessed vectors. The v3.0 staging corpus is
[`conformance_v3.txt`](conformance_v3.txt) (adds the `@fuel n` directive,
§19.2), awaiting the 3.0 build.

## 15. Work packages

WP1 (Display v2, §9), WP7 (host operators, §13), the backend helper
surface (§7.6/§7.7), WP2–WP6, the v2.0 abstraction layer (§17), and the v2.1
program layer (§18) are shipped.
The table below is the historical build decomposition and the maintenance map.
Acceptance for the language is the committed conformance corpus plus the normal
Rust/Python validation stack.

| WP | scope | model |
|---|---|---|
| **WP2 Lexer / parser / AST / unparser** | `src/ogham/{lex,ast,parse,unparse}.rs`, pure Rust, zero deps, world-independent (literal *forms* parse everywhere; world legality is WP3's). §3–§5, §10. The conformance corpus covers sugar, precedence, and unparse expectations through its `~` lines. | sonnet |
| **WP3 Worlds + evaluator** | `src/ogham/{eval,error}.rs`: the §6.1 dispatch enum, per-world literal mapping (§6.2–6.8), §7 desugaring (incl. §§7.6–7.7), §7.5 partiality, §8 stdlib, §11 errors. The judgment-heavy package. | opus |
| **WP4 REPL** | `examples/ogham_repl.rs` + colon commands (§12). | sonnet |
| **WP5 Conformance harness** | `tests/ogham_conformance.rs` + corpus format parser over the committed hand vectors (§14). | sonnet |
| **WP6 Python eval** | `ogham_eval(world: &str, src: &str)` pyfunction + the v1 operator alignment that keeps multivector `&` as wedge and makes `^` raise the Ogham `E_ExpSort` hint (§13). | sonnet |

## 16. v1.1 — the function-shaped worlds

**Implemented and tested.**

- **Worlds** (fixed dispatch, §6.1 discipline): `poly2 poly3 poly5 poly7` =
  `Poly<Fp<p>>` (F_p[t]); `polyint` = `Poly<Integer>` (ℤ[t]); `ratfunc2
  ratfunc3 ratfunc5 ratfunc7` = `RationalFunction<Fp<p>>` (F_p(t)).
- **The `t` atom**: the reserved `t` is the variable (the mirror of `x` in
  `f*` worlds); elements are reached arithmetically (`3⋅t↑2 + 1`); bare
  `INT` is the constant per the coefficient world's §6.2 row; `(num)/(den)`
  round-trips in ratfunc worlds through ordinary `/`.
- **Activations** (§7.6): `@` evaluates at constants and composes at
  non-constants; `%` and exact `/` use `divrem`; `polyint` divisors must be
  monic; ratfunc evaluation at a pole is `E_DivisionByZero`.
- **Relations** (§7.7): none of these worlds carries a canonical order —
  `< > |` stay `E_WrongWorld`; `=` is exact (ratfunc: cross-multiplied).
- **Stdlib additions** (§8): `deg(E) → I`, with `deg(0) → E_Domain`;
  `gcd(E,E) → E` in polynomial worlds. Finite-field polynomial gcds are
  monic; `polyint` returns the positive-leading primitive integer factor.
- **Python parity** (§13): `IntegerPoly` is bound alongside the existing
  `Fp*Poly`/`Fp*RationalFunction` rows; `%` maps to polynomial remainder and
  `@` maps to eval/compose on the v1.1 Python classes.
- **Still out**: precision worlds (`O(p^k)` literals are their own
  iteration); games mode (`{L|R}`); invariant colon-commands (§12).

## 17. v2.0 — abstraction

**Implemented and tested.** The
v2.0 conformance vectors are merged into
[`docs/ogham/conformance.txt`](conformance.txt), replacing the four superseded
v1.1 reserved-syntax vectors listed in the staging header. Judgment calls go
back to this section and the corpus, not into the code. The 2.x/3.0 staging
remains deliberate: each version is independently shippable and leaves a
language worth stopping at.

### 17.1 Sorts

Four sorts: **Element**, **Index**, **Function**, **Bool**. Position
determines sort; there are no coercions (unchanged from §6).

- **Function** = a binder-AST, closed over its own binders (§17.3). The
  entire first-order discipline is one rule: *a Function-sorted term may
  appear only as (a) the RHS of `:=`, (b) an operand of `@`, (c) a whole
  statement.* Everything else — nested lambdas, functions in vectors,
  arithmetic, exponents, stdlib arguments — is `E_FnSort`.
- **Bool** = the verdicts, promoted to values. Relations become
  Bool-*valued* expressions (§7.7's "verdicts, not values; top level only"
  is amended by this section); `true`/`false` become literals;
  `p := a < b` binds a Bool. Bool positions: ternary conditions,
  `and`/`or`/`not` operands, `:=` RHS, statement position, lambda bodies
  (predicates), arguments to Bool-sorted binders. Banned in vectors,
  arithmetic, and exponents: `E_BoolSort`.
- **Binder sorts are inferred per binder** from occurrence positions:
  Element by default, Index when occurrences sit at Index positions, Bool
  likewise; conflicting occurrences are `E_IndexSort`/`E_BoolSort` *at
  definition*. The flagship case is the Gold family —
  `gold := (a, u) ↦ tr(u ⋅ u↑(2↑a))` infers `a : Index`, `u : Element` —
  one definition for the whole parameterized family.
- Bindings bind any sort (`d := deg(f)` binds an Index; `p := a < b` a
  Bool); a bare statement of any sort evaluates and prints.

### 17.2 Grammar deltas

Replaces §4's `statement`/`binding`/`expression` and §5's loose end:

```ebnf
statement   = binding | expression | lambda ;
binding     = IDENT ":=" ( lambda | expression ) ;
lambda      = binders "↦" expression ;        (* ↦ grabs maximally rightward *)
binders     = IDENT | "(" IDENT { "," IDENT } ")" ;
expression  = orexpr [ "?" additive ":" additive ] ;
orexpr      = andexpr { "or" andexpr } ;
andexpr     = notexpr { "and" notexpr } ;
notexpr     = { "not" } relexpr ;
relexpr     = additive [ relop additive ] ;
appl        = atom { "@" applarg } ;
applarg     = atom
            | "(" expression { "," expression } ")" ;   (* a comma makes a tuple *)
atom        = …v1 atoms… | "true" | "false" | "(" lambda ")" ;
```

- `↦` (sugar `~`), `?`, and bare `:` leave the reserved set and become real;
  `and or not` join the reserved words (a breaking change in principle —
  they were legal identifiers in v1.1).
- Precedence, loose end of the table (tight → loose): relations, `not`,
  `and`, `or`, `? :`, `↦`. Relations stay non-chaining (`a < b < c` is
  `E_Parse`); a parenthesized relation is a Bool atom
  (`(a < b) and (c = d)` works, and so does the unparenthesized form, since
  the word operators bind looser than relops).
- **Multi-param application is a tuple**: `b@(u, v)`, arity checked
  (`E_Arity`). One-param keeps the v1.1 atom rule: `f@7`, `f@(u + 1)`. No
  currying, no partial application — partial application manufactures
  function-valued intermediates, which is higher-orderness through the side
  door.
- **Ternary**: condition is any Bool-sorted expression; branches are
  `additive`, must agree in sort (Element, Index, or Bool), and nest only
  via parens: `u < 0 ? -1 : (u = 0 ? 0 : 1)`.
- **Relations extend to Index operands**: `=`, `<`, `>` are sort-homogeneous
  over Element, Index, or Bool pairs (`<`/`>`: Element/Index only; `|`:
  Element only). Index relations are the meta-integer total order — in nim
  worlds Element `<` stays identically false while Index `<` is real;
  position disambiguates, as always. (Needed for Index-recursion base cases,
  §19.) `f = g` on Functions is `E_FnSort` — function equality is
  extensional and not ogham's to decide.
- **`t` is released**: an ordinary IDENT outside the poly/ratfunc worlds
  (the global reservation was a placeholder for exactly this section). The
  `E_Unbound` hint for the exact name `t` still mentions the poly worlds.
  Inside poly/ratfunc worlds `t` remains the indeterminate and cannot be a
  binder (`E_Shadow`, §17.4).

### 17.3 Semantics — capture by substitution

The load-bearing decision: **a Function value is a closed AST over its own
binders, produced by substitution at definition time.** No runtime
environments, ever.

- Captured Element/Index/Bool bindings substitute in as *values* at
  definition (`c := 5` then `f := u ↦ c⋅u` makes `f` literally `u ↦ 5⋅u`,
  and that is its display — capture-at-definition is visible, and rebinding
  `c` later observably cannot touch `f`). Captured Functions
  **beta-reduce** (inline) at definition, so a Function value never
  references another function. Binder occurrences are never substituted.
- Consequently `parse ∘ display = id` extends to the Function sort at
  statement level, and **definition-time checking is complete**: sorts,
  arities, shadowing, unbound names (self-reference included — the hint
  changes in §19), and world-legality of every operator (an ordered
  comparison in `fp5` fails *at definition* with `E_WrongWorld`). The only
  application-time failures are the §7.5 partiality table.
- Application substitutes argument values for binders (sort-checked against
  the inferred binder sorts), then evaluates strictly — except the **lazy
  trio**: ternary branches and the right operands of `and`/`or` evaluate
  only as needed. Both branches are still fully checked at definition. These
  are the language's only non-strict positions and the list is exhaustive.
  (§19's recursion is why the trio must be lazy from day one: the guard
  protects the recursive call.)
- **Composition**: `f@g` with `g` a Function — or, in poly/ratfunc worlds,
  an Element, the v1.1 coherence — yields a Function by inlining, when `f`
  is unary (`E_Arity` otherwise; an n-ary `g` gives an n-ary composite).
  `f@g@x = (f@g)@x = f@(g@x)`, associative exactly as in §7.6.
- **Four-way honesty**: `not (a < b)` in a partial order means "greater,
  equal, *or fuzzy*" — correct CGT, stated loudly. In nim-worlds `u < 0` is
  identically `false`, so `abs` is the identity there; not a bug.

### 17.4 Shadowing (the debt the old stub named)

Binders may not shadow reserved words, stdlib names, or the world's
generator (`t` in poly/ratfunc, `x` in `f*` worlds): `E_Shadow`, with the
poly-world hint being the good one — "`t` is the indeterminate here;
`5⋅t + 1` is already a function." Duplicate binders (`(u,u) ↦ …`) are
`E_Shadow`. Binders **may** shadow ordinary bindings — substitution only
touches free occurrences. (`w` is unreachable as a binder: it lexes to `ω`.)

### 17.5 Display

Functions print as `binders ↦ body` with the unparser's minimal-parens rule;
single spaces around `↦`, `?`, `:`, and the word operators; Bools print
`true`/`false`. Inlining means a function built from other functions
displays *expanded* — define a quadratic form, then its polar form, and the
echo shows you the polar form (the REPL is the tutor). The honest cost: deep
composition chains blow up the display; accepted.

### 17.6 Errors

New kinds: `E_FnSort`, `E_BoolSort`, `E_Shadow`; `E_SeqValue` is used by
§18 sequencing for dead intermediate values. Reused: `E_Arity` (tuple
arity), `E_IndexSort` (binder sort conflicts), `E_Unbound`
(definition-time, including self-reference), `E_WrongWorld` (world-illegal
operators inside bodies, caught at definition).

### 17.7 Host alignment

None. `↦`, `? :`, and `and/or/not` get **no host operators** — Python has
native lambdas, conditionals, and booleans; Rust likewise. Documented like
factorial (§13): ogham spelling only.

### 17.8 Examples (illustrative; the corpus is the oracle)

```text
@world integer 0
> p := 3 < 5
= true
> not p or 1 = 0
= false
> abs := u ~ (u < 0 ? -u : u)
~ abs := u ↦ u < 0 ? -u : u
> abs@(-5)
= 5
> c := 5
> f := u ~ c.u
> f
= u ↦ 5⋅u                  # capture made visible
> c := 7
> f@1
= 5

@world nimber 0
> pn := g ↦ (g | *0 ? *1 : *0)
> pn@(*3 + *2)               # *3 + *2 = *1, fuzzy with *0: an N-position
= *1

@world f4 0
> q1 := s ↦ tr(s⋅s)
> b := (u, v) ↦ q1@(u + v) + q1@u + q1@v
> b
= (u, v) ↦ tr((u + v)⋅(u + v)) + tr(u⋅u) + tr(v⋅v)
> gold := (a, u) ↦ tr(u ⋅ u↑(2↑a))    # a : Index — the Gold chain, one definition
> gold@(1, x)                          # Tr(x³) = Tr(1) = 0 over F₄/F₂
= 0

@world fp5 0
> h := u ↦ (u < 0 ? 0 : 1)
! E_WrongWorld: no order on fp5        # at definition, not application
```

## 18. v2.1 — programs

**Implemented and tested.** The
v2.1 conformance vectors, including the `>>` continuation-line format, are
merged into [`docs/ogham/conformance.txt`](conformance.txt); the original blessed
staging block remains in [`docs/ogham/conformance_v2.txt`](conformance_v2.txt) as
provenance. Totality, definition-time completeness, and the closed-AST
Function model all survive 2.1 untouched — sequences are definitional
structure, not new semantics.

- **`;` becomes real** (leaves the reserved set). A statement sequence is
  `{ binding ";" } statement`. Intermediate statements must be bindings:
  with no effects, a discarded value is necessarily dead code —
  `E_SeqValue`, the one new error kind.
- **Top level**: sequences are legal on a REPL/`.og` line; bindings persist
  into the session environment; only a final expression prints
  (`a := 5; a + 1` prints `6`, and `a` stays bound). The session is a
  program too — "a function body is any ogham program" reads both
  directions.
- **Bodies**: a parenthesized sequence is an expression form, usable
  anywhere `( expression )` is — `f := n ↦ (d := n⋅n; d + 1)`. There is no
  `let` keyword: `:=` *is* the let. Locals are lexically scoped, may shadow
  (§17.4 rules apply), are invisible outside, and the final statement of a
  body sequence must be an expression. Capture-substitution maps through
  sequences; display preserves the user's let-structure (sequences are not
  inlined away in the canonical form — closedness, not flatness, is the
  invariant).
- **Continuation**: the lexer consumes lines while `(`/`[` are unbalanced —
  the REPL shows a continuation prompt; `.og` files wrap freely;
  one-statement-per-line remains the rule at depth 0. Comments still run to
  end of line.

```text
@world integer 0
> a := 5; a + 1
= 6
> norm1 := (u, v) ↦ (
    s := u + v;
    d := u - v;
    s⋅s + d⋅d
  )
> norm1@(2, 1)
= 10
```

## 19. v3.0 — recursion + games (sketch)

**Sketch — the build contract for 3.0**, grown from the 2026-06 stub in the
2026-07-09 design session (a9 + fable). The staged corpus is
[`conformance_v3.txt`](conformance_v3.txt) (§14 staging discipline: the
harness does not read it until the build merges it into `conformance.txt`).
Judgment calls go back to this section and the corpus, not into the code.
The layering inside 3.0 is itself staged — §§19.1–19.2 are world-independent,
§§19.3–19.4 add the containers and the game world, §19.5 adds the loopy
layer — and each stage leaves a language worth stopping at (§19.5 may slip
to 3.1 if the loopy seam fights the build).

This is the one genuine semantic break: **totality is traded for
attributable partiality** — a program either terminates or errors honestly
(`E_Fuel`), never a silent hang — and, exactly where CGT's loopy theory
licenses it, non-termination itself becomes a *value* (§19.5).

**The thesis, sharpened.** A lisp's power is a recursive data constructor
plus recursion over it; an APL's power is a fixed-shape bulk container whose
operators act on the whole. ogham has both, one per pillar, and they were
already in the mathematics — the two containers are the pillars' native
shapes:

| | array (Clifford worlds) | list (game world) |
|---|---|---|
| constructor | `[a0,…,a(n-1)]` (grade-1) | `{h \| t}` cons, `{\|}` nil |
| shape | static — the world's `dim` | dynamic, even infinite (§19.5) |
| access | random: `coef(v, i)` | sequential: option descent |
| contains | the world's scalars | the world's Elements (games) |
| iteration | Index recursion, bounded | μ-recursion / coinduction |
| algebra | `+` is zip-with-add; `⋅` exists (ring) | `+` is game sum, **not** append; `⋅` is `E_WrongWorld` (group) |
| equality | `=` is structural *and* semantic | `=` semantic, `≡` structural (§19.4) |
| append | none — shape belongs to the world | `⧺` (§19.4) |

*APL over the Clifford worlds, Lisp over the game world, one grammar.* The
ring/group divide — the repo's founding scope boundary — reappears as
fixed-shape-with-algebra vs free-shape-with-recursion: the world with
multiplication has the rigid container, the world that is only a group has
the free one. Not a lisp with weird numbers: the lisp whose cons cell is the
Conway game, where mex and Grundy sit where car/cdr folds sit in Scheme.
(On ship, a compact form of this graduates to a §1 design principle.)

This split settles the stub's recorded sequence-sort question: the *data*
half was never missing — each pillar already carries its native container —
and only the *functions-as-values* half stays gated post-3.0, decided when
the Index-recursion pain has been measured (§19.6).

### 19.1 `=:` — the fixpoint binding

`name =: lambda` defines recursively: the name is in scope in its own body
as a symbolic self-reference (a μ-binder, honestly). The mirror notation
*is* the semantics — `:=` is assignment, the value flows in from the past
(capture); `=:` is an **equation the name satisfies**, the least fixed
point:

```text
@world integer 0
> fact =: n ↦ (n = 0 ? 1 : n⋅fact@(n-1))
> fact@5
= 120
```

- `=:` with no self-mention degenerates to `:=` exactly — any sort, any
  world (`c =: 5` is `c := 5`).
- `:=` with a self-mention stays `E_Unbound`; the hint becomes "recursive
  definition? `=:`".
- The recorded footgun: the rebind idiom `f := u ↦ f@u + 1` ("new f from
  old f", which eager substitution makes work) and the recursive
  `f =: u ↦ f@u + 1` differ by a character transposition. The loud
  direction is covered by the hint; the silent direction needs a
  previously bound name *and* a self-mention *and* the wrong operator —
  narrow, documented, accepted.
- Lexing: `=:` munches before `=` (the token sequence `=` `:` is never
  grammatical, so this is safe — the same class as `:=` vs bare `:`).
- A **top-level** Function value carries at most one free name — its own μ.
  Statement-level round-trip holds (`fact =: …` re-parses to the same
  function); the bare `> fact` echo prints the equation form. Everything
  non-recursive keeps full inlining: 2.x semantics are unchanged, not
  grandfathered.
- **Local `=:`** is allowed in body sequences, for both sorts; a local
  helper may recurse and may reference the enclosing μ-name and binders.
  This is what lets a single μ cover most mutual-recursion shapes. True
  mutual recursion (`=:` groups) is **deferred, owed**.
- `=:` with an Element-sorted RHS **and** a self-mention is §19.5's
  coinductive case, legal exactly in the game world. Everywhere else it is
  an error with the math in the message: `x =: x + 1` names nothing in ℤ —
  no fixpoint theory, no fixpoint syntax (`E_WrongWorld`). The equation
  reading is uniform — only the licensing theory differs.

### 19.2 Fuel — steps, not depth

The stub metered recursion *depth*; that does not deliver the honesty
claim. `fib =: n ↦ (n < 2 ? n : fib@(n-1) + fib@(n-2))` at `fib@100` has
depth ~100 — no depth budget trips — but performs ~φ¹⁰⁰ ≈ 10²⁰ unfoldings:
a silent hang with a clean conscience. Fuel therefore meters **total
μ-unfoldings**: every substitution of a μ-bound body into its call site
counts one, all μs (top-level, local, nested) draining one shared budget,
reset per top-level statement. Exceeding it is **`E_Fuel`**, naming the
μ that struck zero and the budget. (Non-recursive applications are not
metered: §17.3 inlining means they cannot loop. Engine-internal recursion —
canonicalization, spine walks, loopy fixpoints — is not metered: it
terminates on finite forms by construction.)

- Default budget: **2¹⁶ = 65536** unfoldings — interactive scale;
  substitution-based evaluation is not cheap, and the knob exists.
- `:fuel n` is the REPL knob (`:fuel` alone prints the current budget).
  The conformance format grows a matching `@fuel n` directive line
  (persists until the next `@fuel`/`@world`; `@world` resets to default).
- "Every vector terminates" stops being a theorem and becomes a budget.
  The stub's `E_Depth`/`:depth` are renamed with the semantics change —
  honesty in names.

### 19.3 The array container — `coef` and `dim`

The array half costs exactly two stdlib entries; the constructor (`[…]`,
§7) has existed since v1 and the language could never read a component back
out. Clifford worlds only (`E_WrongWorld` in game and function worlds — the
hint teaches the container table: *arrays are world-fixed length; the
free-shape container lives in the game world*).

| call | signature | semantics |
|---|---|---|
| `coef(E, I)` | Element × Index → Element | the coefficient of the basis 1-blade `e_i` in the multivector (grade-0 result; `0` if absent; total in the Element — `coef(e0∧e1, 0) = 0`). `i ≥ dim` → `E_BladeIndex`. Engine: `Multivector::terms()` at mask `1 << i` |
| `dim()` | → Index | the world's dimension (`0` in dim-0 worlds) |

With `coef` + `dim` + `=:`, array folds are Index recursion — bounded by
`n`, fuel-friendly. The array-side acceptance example, sibling to §19.4's
`grundy`:

```text
:world fp7 3 q=[1,1,1]
dot =: (u, v, i) ↦ i = dim() ? 0 : coef(u, i)⋅coef(v, i) + dot@(u, v, i + 1)
dot@([1, 2, 3], [4, 5, 6], 0)     # 32 ≡ 4 mod 7
```

Recorded extensions, gated on measured pain, not built now: a blade-bitmask
accessor for the full 2ⁿ coefficient array; `coef` on the poly worlds
(coefficient of `t↑i`, mirroring `deg`).

### 19.4 The game world — forms, lists, and the second equality

`:world game` — Elements are **game forms** over the games pillar
(`games/partizan.rs::Game`: ordered option vectors, `Arc`-shared,
canonicalization only on demand); the first non-scalar world (the dispatch
enum grows a non-Clifford arm, exactly as v1.1's function worlds did). No
metric, no blades. CGT is the recursive subject; this is where the language
and the repo's thesis converge.

**Two strata, stated up front.** The world carries *form-land* (the free
constructors: lists, option access, `≡`, `⧺`) and *value-land* (the CGT
quotient: `=`, `<`, `>`, `|`, `+`, `-`, outcomes). Form-level operations
are **not congruences for `=`** — `{-1 | 1} = 0` is `true` (simplicity
rule), yet `{-1 | 1}` is a cons cell and `0` is nil, so `≡` says `false`,
`isnil` differs, and `⧺` treats them differently. This is not a bug; it is
the form/value distinction CGT itself is careful about, and it is
load-bearing beyond lists: a future misère mode *needs* the form stratum
(misère play does not quotient by normal-play equality — `games/misere.rs`).

#### 19.4.1 Grammar and symbol deltas

```ebnf
relexpr     = catexpr [ relop catexpr ] ;
relop       = "=" | "≡" | "<" | ">" | "|" ;
catexpr     = additive [ "⧺" catexpr ] ;      (* right-assoc via recursion *)
atom        = …v2 atoms… | braceform ;
braceform   = "{" [ optlist ] "|" [ optlist ] "}"
            | "{" [ expression { "," expression } ] "}" ;   (* list sugar *)
optlist     = expression { "," expression } ;
```

| meaning | canonical | codepoint | ASCII sugar | notes |
|---|---|---|---|---|
| append | `⧺` | U+29FA | `++` | right-assoc, own tier looser than `+ -`, tighter than relations; game world only |
| structural equality | `≡` | U+2261 | `===` | relop tier, non-chaining; game world only |
| game form | `{L\|R}` | — | — | leaves the §2 reserved set; inside braces `\|` and `,` are structural separators |

- `{` `}` and their interiors parse in **every** world (the grammar stays
  world-independent, as with `@`); worlds other than `game` reject the
  form at evaluation with `E_WrongWorld`.
- `++` munches before `+` (safe: `+` has no unary form, §2 unary-fill, so
  `+ +` is never grammatical); `===` munches before `==`. Adjacency
  required, as for all multi-char tokens — `a + + b` stays `E_Parse`.
- `⧺` precedence, tight → loose, amending §5/§17.2: … `+ -`, **`⧺`**,
  relations, `not`, `and`, `or`, `? :`, `↦`. Right-assoc is both the shape
  of the spine it builds and the linear-cost association for chains
  (left-assoc re-copies the accumulated prefix: O(n²)). Ternary branches
  stay `additive` — an append inside a branch takes parens.
- New reserved stdlib names (§3 discipline; a breaking change in principle,
  as `and/or/not` were for v2): `coef dim canon nleft nright left right
  up down drawn`.
- §18 continuation extends to unbalanced `{` — multi-line game forms wrap
  like vectors and sequences.

#### 19.4.2 Literals and display

- Bare `INT` is the integer game — the canonical CGT embedding, the one
  world where `from_int` on bare literals is honest (`!n` lands likewise).
  `*n` is the nimber game in its standard form (options `*0 … *(n-1)` on
  both sides, in that order); bare `*` is `*1`. `ω`, blades, `[…]` vector
  literals: `E_WrongWorld` (the `[…]` hint: "lists are braces here:
  `{1, 2, 3}`").
- **Form display is structural and canonical**: `{` + left options joined
  `, ` + `|` + right options joined `, ` + `}`, single spaces separating
  the bar from each *nonempty* side: `{|}`, `{0 |}`, `{| 0}`, `{0 | 0}`,
  `{1, 2 | 0}`. One carve-out: a form that is **structurally** identical to
  what a literal builds displays as that literal — integer chains print
  `2`, `-3`; standard nimber forms print `*n`; `{|}` prints `0` (bare INT
  is honest here, and `*0` parses to the same form). Recognition is
  structural, never value-level: `{5 | 0}` and `{0 | 1}` display as
  themselves, and `1 + 1` — which materializes the *sum form* — displays
  `{1, 1 |}`, not `2`. Value identity is said with `=` or `canon`:
  `1 + 1 = 2` is `true`, `canon(1 + 1)` displays `2`. Display v2's scope
  note ("game displays out of scope") is amended by this clause.
- Operators: `+` disjunctive sum (form-level materialization), unary and
  binary `-` game negation. `⋅` is **`E_WrongWorld`** — games are a group,
  not a ring (the repo's founding scope boundary, now enforced by the
  evaluator rather than assumed by it). `∧`/`&`, `/`, `%`, Element-`@`:
  `E_WrongWorld` (the `∧` hint points at `⧺`).
- **Relations are the full CGT partial order** — the world `|` was born
  for; all four §7.7 cells are live. `=` is game-*value* equality
  (canonicalize-and-compare; engine `Game` comparison).
- The CGT glyph collision is recorded: ogham's `↑` is power, so up/down
  are the nullary stdlib calls `up()`, `down()` (names settled).

#### 19.4.3 The second equality and `canon`

- **`a ≡ b`** — structural (form) equality: same tree, options compared
  in order. On §19.5's cyclic values it is regular-tree equality (equality
  of infinite unfoldings; α-invariant, decidable by synchronized descent
  with a visited pair-set). Bool-valued, relop tier, non-chaining.
- **`canon(E) → E`** — the engine's canonical form (`Game::canonical`:
  options canonicalized, dominated options deleted, reversible options
  bypassed). Finite forms only at 3.0 (`E_Loopy` on loopy values —
  onside/offside canonicalization is owed post-3.0).
- The two equalities are related *in the language*:
  `a = b  ⟺  canon(a) ≡ canon(b)` — a conformance vector, not just prose.
- `≡` outside the game world is `E_WrongWorld`, not an alias for `=`: in
  every other world forms *are* values and a silently-coinciding second
  equality would mislead more than help (the `%`-in-fields precedent,
  §7.6). Hint: "`=` is already structural here."
- Cost inversion, noted: structural `≡` is the cheap linear walk; semantic
  `=` is the expensive one (canonicalization). The default glyph is the
  costly one because the math owns `=`.

#### 19.4.4 Option access

Form-level, all Index-sorted where shown (0-indexed; out of range →
`E_Domain`):

| call | signature |
|---|---|
| `nleft(E)` / `nright(E)` | Element → Index — option counts |
| `left(E, I)` / `right(E, I)` | Element × Index → Element — the i-th option |

Recursion over options is Index recursion; no sequence sort is needed
(§19.6 keeps the gate).

#### 19.4.5 Lists — the cons-cell discipline

The game form is ogham's cons cell, literally: **cons is `{h | t}`**
(sides are ordered — the bar distinguishes head from tail — and each side
is a singleton, so set-vs-sequence never arises), **nil is `{|} = 0`** —
the empty list is the zero game; list exhausted = ending position. A
**proper spine** is nil, or a cons whose tail is a proper spine. Everything
else is Lisp's dotted/improper case, legal as data. The accessors are
definable in-language — the list library is a prelude, not stdlib:

```text
:world game
hd := l ↦ left(l, 0)
tl := l ↦ right(l, 0)
isnil := l ↦ nleft(l) = 0 and nright(l) = 0     # structural — l = 0 is NOT a nil test ({-1|1} = 0)
```

- **List sugar**: barless braces are list literals — `{a, b, c}` desugars
  at parse to the right-nested spine `{a | {b | {c | {|}}}}`, `{}` to
  `{|}`; items are expressions; nesting gives trees (`{{1, 2}, 3}`).
  Input-only sugar (§1.3): canonical display stays the bar form, the echo
  teaches, and the switch-player who wrote `{5 | 0}` is never shown `{5}`.
- The **missing-bar footgun**, recorded (the §19.1 transposition's class):
  `{1, 2 |}` (left options only) and `{1, 2}` (spine) differ by one
  character; today the barless form is a loud parse error, post-sugar it is
  a silently different game. The echo makes it visible immediately —
  `{1 | {2 | 0}}` looks nothing like `{1, 2 |}`. Narrow, echo-visible,
  documented, accepted.
- **`l ⧺ g` — naive append.** Walks the left operand's spine and grafts
  the right operand at the nil terminal. The left operand must be a
  *finite proper spine*, else **`E_Improper`** (this includes §19.5's
  cyclic spines at 3.0 — see the owed decision there). The right operand
  is **unrestricted**: grafting a non-list gives an improper list, exactly
  Lisp's `(append '(1 2) 3) = (1 2 . 3)` last-argument freedom. Units:
  `{} ⧺ l = l` and `l ⧺ {} = l`. Form-level, hence not a `=`-congruence:
  `0 ⧺ l = l` while `{-1 | 1} ⧺ l` is `E_Improper`, despite
  `{-1 | 1} = 0`. `+` is **not** append and no operator concatenates
  arrays — the containers give construct/access/recurse, never a borrowed
  algebra.

The acceptance example — the cons-cell payoff (sorts check under §17.1
inference; `grundy` returns an Index; `has` captures the outer binder `g`
and the outer μ; the lazy trio guards both the index range and the
recursive calls; mex is "the first `n` not hit"):

```text
:world game
grundy =: g ↦ (
  has =: (n, i) ↦ not i = nleft(g) and
                  (grundy@(left(g, i)) = n or has@(n, i + 1));
  mexfrom =: n ↦ has@(n, 0) ? mexfrom@(n + 1) : n;
  mexfrom@0
)
grundy@(*2)        # = 2
```

Greedy = mex is Bridge O's seam (`games/lexicode.rs`) — with 3.0 the
language can finally *say* the games pillar.

### 19.5 Element-`=:` — loopy games are fixpoint equations

The μ-binder is not function-only. `=:` with an Element-sorted RHS is a
fixpoint equation on *values*, and CGT is the theory that licenses it: a
**guarded** self-reference defines a cyclic game graph, i.e. a loopy game,
whose outcome theory the games pillar already carries (`games/loopy/`):

```text
:world game
on   =: {on |}
off  =: {| off}
dud  =: {dud | dud}        # the deathless universal draw
over =: {0 | over}
ones =: {1 | ones}         # the constant stream — coinductive lists for free
```

The construct and the math object coincide: `=:` was designed for recursive
functions, and applied to game data it *is* coinductive definition —
Siegel's loopy values are fixpoint equations on game forms, told in the
language's own notation. Under the §19.4.5 list reading, guarded
Element-`=:` *is* the infinite/circular list: streams are loopy games.
(Folded into 3.0 at a9's call, 2026-06-12.)

- **Guardedness, checked after definition-time reduction.** The RHS is
  evaluated at definition with the μ-name symbolic: brace constructors may
  enclose symbolic occurrences; **`⧺` reduces structurally** — its
  recursion walks only its *left* operand and never inspects its right, so
  `s ⧺ X` with `s` a closed proper spine unfolds into nested constructors
  with `X` grafted at the terminal (`{a, b} ⧺ l` becomes `{a | {b | l}}`).
  Every other operator is strict in its operands' options and cannot
  reduce past a symbolic occurrence — applying one to a μ-containing
  operand is **`E_Unfounded`**. After reduction, every remaining μ-occurrence
  must sit strictly inside at least one brace constructor; a bare-root
  occurrence (`g =: g`) is `E_Unfounded`. **`⧺` is the one
  guardedness-transparent operator at 3.0**, transparent from the left
  only. The edges fall out with no extra code: `h =: {|} ⧺ h` unfolds to
  `h =: h` → `E_Unfounded` (nil is append's unit); `k =: k ⧺ {1 | 0}`
  cannot reduce → `E_Unfounded`; `m =: m + 1` → `E_Unfounded` (sums with
  loopy summands stay behind the stopper boundary, deferred as before).
- **The stream idioms.** Purely periodic: `l =: {1, 2} ⧺ l` — the period-2
  stream, a 2-cycle graph. Eventually periodic: local `=:` in a body —
  `p := (q =: {1, 2} ⧺ q; {9} ⧺ q)` is the stream 9,1,2,1,2,… The sugar
  always nil-terminates, so a self-*tail* needs `⧺` or the raw bar form;
  the sugared `l =: {1, l}` is legal but different — a self-*element* list,
  Lisp's circular `#1=(1 #1#)`.
- **The graph is materialized and classified at definition** (definition-
  time completeness, §17.3 spirit): the cyclic form becomes a
  `LoopyPartizanGraph`; outcomes with draws come from
  `classify`/`draw_set`. **Fuel is untouched**: Element-`=:` runs graph
  fixpoints, not descent — "didn't terminate" becomes a value exactly where
  the theory assigns one, and `E_Fuel` remains the verdict everywhere else
  (a μ-*function* recursing along an infinite spine — `len@ones` — is
  honestly `E_Fuel`).
- **The 3.0 envelope for loopy values** (conservative; loosening is owed,
  never breaking): allowed — binding, display, option access
  (`left`/`right`/`nleft`/`nright` walk graph nodes; `hd`/`tl` work on
  streams), `≡` (regular-tree), `drawn`, and the *right* operand of `⧺`
  (`{9} ⧺ ones` is a finite graft).
  Rejected with **`E_Loopy`** — relations (`= < > |`), `+`, `-` (unary
  negation is mathematically trivial — an L/R swap through the graph — but
  it manufactures an *anonymous* cycle, and the display rule below names
  cycles by their defining `=:`; negation joins the owed loosening),
  `canon`. Rejected with `E_Improper` — the *left* operand of `⧺`; the
  message records the coinductive candidate meaning (`l ⧺ g = l` when `l`
  never reaches nil — appending to an infinite list is the identity), and
  upgrading error → value is the recorded owed decision (a9's call).
- **`drawn(E) → Bool`** — true iff some mover faces a draw
  (`LoopyPartizanOutcome::has_draw`); identically `false` on finite forms;
  `E_WrongWorld` outside the game world. `drawn(dud)` is `true`;
  `drawn(on)`, `drawn(over)`, and `drawn(ones)` are `false` (alternation:
  the opponent's forced returns still hand the mover a win). The richer
  per-mover 3×3 readout wants either an outcome sort or a relation
  extension — **owed post-3.0**; Bool stays two-valued, and Index-coding
  outcomes is rejected. For finite forms nothing is lost: relations
  against `0` already read out all four outcome cells.
- **Display.** A loopy *root* echoes as its equation, μ carve-out as
  §19.1: `> on` prints `on =: {on |}`. An interior node re-roots the
  equation at itself, reusing the cycle's defining name α-bound —
  `tl@l` for the period-2 `l` prints `l =: {2 | {1 | l}}` (the name is a
  bound variable of the equation, not an environment reference; statement-
  level round-trip holds). A *composite* value containing cycles it does
  not root displays as a §18 body — one local `=:` per distinct cycle in
  first-reach order, final expression the structural form:
  `(q =: {1 | {2 | q}}; {9 | q})`. Round-trips by construction (it is a
  program computing the value); verbose-canonical accepted, prettification
  owed post-3.0.
- Staging: ships **with 3.0** by default — refusing it would take *extra*
  code, an occurs-check built solely to reject meaning the math already
  assigns. Slipping to 3.1 is recorded as acceptable if the loopy-engine
  seam fights the build.

### 19.6 Errors, host alignment, build staging, non-goals

**New error kinds**: `E_Fuel` (§19.2 — renames the stub's `E_Depth` with
the step semantics), `E_Unfounded`, `E_Improper`, `E_Loopy`. Reused:
`E_WrongWorld` (game forms / `⧺` / `≡` / `coef` / `dim` / `drawn` outside
their worlds; Element-`=:` with self-mention outside the game world),
`E_Domain` (option index out of range), `E_BladeIndex` (`coef` past `dim`),
`E_Unbound` (hint gains "recursive definition? `=:`"), `E_Parse`,
`E_Shadow`, `E_Arity`, `E_IndexSort`, `E_BoolSort` (all as in v2).

**Host alignment: none.** `⧺`, `≡`, `{L|R}`, `=:`, and fuel get no host
operators (the §13 factorial clause); game-world exposure to Python is a
binding-scope-policy decision (`src/py/AGENTS.md`), not part of 3.0.

**Build staging** (each stage independently shippable, conformance-gated):

| stage | scope |
|---|---|
| **A** | lexer/parser/AST/unparser deltas: `=:`, `⧺`/`++`, `≡`/`===`, braceforms + list sugar, precedence row, `~`-vector coverage (world-independent) |
| **B** | evaluator: `=:` capture/μ semantics + fuel + `E_Fuel` + hints, `coef`/`dim`, all existing worlds |
| **C** | the game world: dispatch arm over `games::Game`, literals + structural-recognition display, relations, `canon`/`≡`, option stdlib, `⧺`, `up`/`down` |
| **D** | Element-`=:`: definition-time reduction + guardedness, graph tie to `games/loopy/`, `drawn`, loopy display carve-outs, the `E_Loopy` envelope |
| **E** | REPL `:fuel`, harness `@fuel`, corpus merge into `conformance.txt` |

**Non-goals, recorded.** **Quote/macros: never.** Code-as-data would blur
the structural-vs-arithmetic line (star-literals, `{L|R}` interiors) that
the grammar fights hardest to keep crisp; recursion, sequencing, let-bodies,
booleans, and the two containers all compose with ogham's honesty axioms —
quote does not. Mutation, I/O, strings: out — rebinding is the only state,
the REPL the only effect. Higher-order functions (map/fold as values):
still gated post-3.0, now *only* on functions-as-values — the container
question is settled by §19.3/§19.4.5. Transfinite/ω-length games: out —
the game world is the finite-graph pillar. Owed post-3.0, collected:
mutual-recursion groups (function and loopy), the loopy comparison/sum
envelope and onside/offside `canon`, coinductive append (error → value),
loopy negation (anonymous-cycle display naming), the per-mover outcome
readout, composite-display prettification, blade-bitmask and poly-world
`coef`.
