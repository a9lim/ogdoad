# grundy design stance

This note is non-normative; [`spec.md`](spec.md) is the contract.

## Rulesets are the object

A combinatorial game is a state space with moves. grundy makes that the
primitive: a ruleset is a coalgebra `S → List(List(S)) × List(List(S))`.
Positions are data, and an option is a disjunctive sum of components. Brace
forms and guarded equations are the special case where the states are syntax.

The coalgebraic account of loopy games (Honsell–Lenisa, *LMCS* 2011) is the
standard foundation. A finite graph presents exactly the eventually periodic
behaviors; exploring a ruleset over finitely many reachable states yields one.
Multiplicity matters at the presentation level, so options are lists, not
sets.

## Answers carry their scope

The project's claim discipline distinguishes cited, tested, proved, and open.
grundy brings that distinction into the type of an answer:

- a computation on a finite object is **exact** and returns a plain value;
- a statement about a family, or one whose evidence should travel, is a
  **Claim**. It is sealed only by an independent checker, and it displays as
  `verify(<witness>)`, so the text re-checks wherever it goes;
- an answer computed on a finite sample of an infinite universe is
  **Bounded**. It has a different type from its payload, so sampled agreement
  cannot silently become equivalence; `sampled(b)` is the visible projection.

The asymmetry this exposes is mathematical, not an implementation accident:

- a misère separating context is one finite witness that two positions differ
  in the whole universe;
- equivalence over an infinite universe needs a theorem.

## Values and presentations are two types

`Game` is a short game value in sealed canonical form, so every operation on
it respects `=`. `Form` is a presentation: as built, possibly cyclic, compared
structurally by `≡` and by value only where the stopper theory licenses it.
The type system enforces the split; it is not a convention of prose.

## Budgeted general recursion, not totality

grundy is not total in Turner's sense, where a programming discipline excludes
non-termination. It is general recursion with attributable failure:

- fuel meters every call and every produced element;
- the call depth and the node count have their own guards;
- a budget's exhaustion is an error, never a value, never "draw" and never
  "equal".

Loopy games are different. Their cycles are mathematical data represented by
finite graphs, and infinite play is a draw because CGT says so, not because a
computation failed to finish.

## Worlds are types

Nimbers, ordinals, surreals, finite fields, polynomial rings, rational-function
fields, and Clifford algebras are types that coexist in one program. Typed
bridges cross them where a theorem licenses the crossing:

- `game(x)` embeds an integer, a nimber, or a dyadic;
- `nimber(g)` reads a nimber-valued game, and fails elsewhere;
- `sg(R, p)` is the Sprague–Grundy number of a terminating impartial ruleset.

Literal types default through `Int, Game, Nimber, Surreal, Form` by one
static rule. Nimbers and ordinals have no integer literals — `from_int` would
collapse `3` to `1` in characteristic two — so `*3` is their literal.

## References

- F. Honsell and M. Lenisa, “Conway Games, Algebraically and
  Coalgebraically,” *Logical Methods in Computer Science* 7(3), 2011.
- A. Van Gelder, K. Ross, and J. Schlipf, “The Well-Founded Semantics for
  General Logic Programs,” *JACM* 38(3), 1991. Win, loss, and draw on a finite
  game graph are the well-founded semantics of the win–move program.
- T. Plambeck and A. N. Siegel, “Misère Quotients for Impartial Games,”
  *J. Combin. Theory Ser. A* 115(4), 2008.
- A. N. Siegel, *Combinatorial Game Theory*, GSM 146, AMS 2013.
- R. M. McConnell, K. Mehlhorn, S. Näher, and P. Schweitzer, “Certifying
  Algorithms,” *Computer Science Review* 5(2), 2011.
- L. Damas and R. Milner, “Principal Type-Schemes for Functional Programs,”
  *POPL* 1982.
- D. A. Turner, “Total Functional Programming,” *Journal of Universal
  Computer Science* 10(7), 2004.
