# grundy — the stance

Status: **non-normative** (drafted 2026-07-19, a9 + fable, out of a design
conversation — prompted by a9's observation that the language had grown
Haskell-shaped). [`spec.md`](spec.md) remains the only contract. This note
names the design tradition the shipped semantics already occupies, so that
future rungs steer by it deliberately rather than by drift. Claim level:
re-description of implemented v0.3.6 semantics, except where marked.

## The claim

grundy is a **total, observation-driven language, lazy exactly where the
objects are coinductive** — a member of the lazy-functional family through
the *total* line (Turner's total functional programming; the data/codata
discipline of Agda and Idris), not through Haskell's own semantics. The
kinship with Haskell is real and worn openly: the name is a person-name in
the Haskell tradition ([`spec.md`](spec.md), header note), the `=:` system
is a letrec, the branches are non-strict. One refusal separates the two
lines, and it is the language's most distinctive commitment:

**⊥ is not a value.** Haskell's laziness comes bundled with partiality —
every type contains divergence, every equation holds only up to ⊥, and
equational reasoning happens in a domain. grundy took the other fork:
divergence is an *error, priced and named* — `E_Fuel` for μ-steps (§9.2),
`E_GraphBudget` for materialization (§10.7), `E_StackDepth` for the host
frame (§13) — never an inhabitant of a sort. The spec's own slogan is the
stance: "total" always means *mathematically total, operationally budgeted*
(§10.7). The conformance corpus depends on this — its equations are
set-level facts, not domain-level approximations. So "aligning with
Haskell" means mining the good parts — non-strictness, codata, the
equational culture — while keeping the refusal of ⊥ as the thing that
makes grundy grundy.

## The shipped constructs, under their tradition names

Nothing here is new semantics; it is the v0.3.6 surface, re-described.

| construct | spec | tradition name |
|---|---|---|
| Function `=:` — substitution you can see, fuel-metered | §9.1, §9.2 | μ-recursion by visible unfolding (the data side) |
| Element `=:` with self-mention, guard required | §9.1, §10.7 | guarded coinductive definition, presented as a finite cyclic graph (the codata side) |
| Bool/Index `=:` self-mention → `E_FixpointSort` | §9.1 | the data/codata stratification, *enforced*: recursion is for Functions (unfolding) and game Elements (graphs), nowhere else |
| `if/then/else`, `and`/`or` lazy branches under total sort-checking | §4, §8.6 | non-strictness without ⊥ ("non-strictness is not an exemption") |
| `⧺`, coinductively total on the left | §10.4 | corecursion on codata |
| outcome as observation; `≡` with branch-local cycle assumptions | §10.1, §10.5 | copatterns; bisimulation up-to |
| fuel / node / frame budgets | §9.2, §10.7, §13 | the operational fence that replaces ⊥ |

The loopy game world is the final-coalgebra account of Conway games —
standard math, worked out in Honsell–Lenisa 2011 (loopy games as a final
coalgebra, sum by corecursion) — and that is the theory citation the 0.3.8
loopy-envelope rung carries.

## The two infinities (laziness and the transfinite)

Coinductive machinery comes in two strengths; grundy currently ships
exactly one.

- **Cyclic**: finite graphs — the Element-`=:` systems — present exactly
  the *eventually-periodic* infinite behaviors (`on`, `over`, `dud`,
  `ones`). This is 0.3.8's territory, with Honsell–Lenisa as its theory.
- **Productive**: streams whose next option is *computed*, not looked up.
  `ω = {0, 1, 2, … |}` genetically — Conway's construction view, as
  opposed to the CNF normal-form view the ordinal worlds already give —
  has an increasing, non-periodic left-option stream: **no finite cyclic
  presentation exists**. A generator is a function. So lazy transfinites
  are not a change of tack; they are the 1.0.0 higher-order rung's
  content, arriving with its motivation attached. (Claim level: design
  synthesis. Implementation sketch: call-by-need thunks with blackholing —
  which doubles as principled vicious-circle detection for non-productive
  systems; host stays Rust.)

**`birthday` is the litmus** separating the strata, and it inverts across
them: a symbolic value (CNF ordinal, Hahn surreal) *knows* its birthday —
total, read off the representation. A stream-presented game only *reveals*
it: forcing n levels yields "birthday ≥ n"; the exact answer requires
recognizing the stream as a symbolic value (proving your generator is ω),
and comparison on naive non-wellfounded presentations is only
semi-decidable in general. This is why the symbolic core stays load-bearing
under any amount of laziness: **the lazy layer presents; the symbolic layer
computes.** Budgeted embeddings are already the fence between them.

## Ladder impact

(The ladder lives in [`docs/CONTINUATIONS.md`](../../docs/CONTINUATIONS.md).)

- **0.3.7** — untouched.
- **0.3.8** — gains its theory citation (Honsell–Lenisa), and one
  release-dress decision: whether §1 states the coalgebraic identity out
  loud. Note that §1's "non-strictness exactly where the mathematics never
  looks" becomes false the day a stream *is* the mathematical object — the
  sentence is priced for revision at 1.0.0, not before.
- **0.4.0** — freezes the public story; the stance had to be decided by
  then. (It is: this note.)
- **1.0.0** — productive streams as the codata face of higher-order; and a
  star to steer by (claim level: speculation): the Escardó–Oliva selection
  monad — selection functions compute optimal plays in sequential games,
  and their infinite products run total searches over infinite spaces. If
  the Function sort ever wants a strategy shape, that is the prior art.
  (The reflexive cousin: game semantics interprets programming languages
  *in* games — Hyland–Ong, Abramsky — so a language for games whose
  functions are strategies would eat its own tail in the good way.)

## References

- D. A. Turner, *Total Functional Programming*, J.UCS 10(7), 2004 — the
  stance itself: strong normalization plus codata, ⊥ refused.
- F. Honsell, M. Lenisa, *Conway Games, Algebraically and Coalgebraically*,
  Log. Methods Comput. Sci. 7(3), 2011 — loopy Conway games as a final
  coalgebra; the 0.3.8 theory.
- A. Abel, B. Pientka, D. Thibodeau, A. Setzer, *Copatterns: Programming
  Infinite Structures by Observations*, POPL 2013 — outcome-as-observation
  as a typing discipline.
- M. Escardó, P. Oliva, *Selection Functions, Bar Recursion and Backward
  Induction*, Math. Struct. Comput. Sci. 20(2), 2010; and *What Sequential
  Games, the Tychonoff Theorem and the Double-Negation Shift Have in
  Common*, MSFP 2010 — the 1.0.0 temptation.

Reading order for the incoming: Turner, then Honsell–Lenisa, then
Escardó–Oliva.
