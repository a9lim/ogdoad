# grundy design stance

This note is non-normative; [`spec.md`](spec.md) is the contract.

Grundy is a total, observation-driven language that is lazy exactly where its
objects are coinductive. It belongs to the total-functional and data/codata
tradition rather than to a semantics in which divergence inhabits every type.

**Bottom is not a value.** Recursive unfolding, graph materialization, and host
stack use are priced by `E_Fuel`, `E_GraphBudget`, and `E_StackDepth`. A program
returns a value or an attributable error; divergence is never silently coerced
into a language value. Loopy games are different: their cycles and draw
outcomes are mathematical data represented by finite graphs.

## Current correspondences

| construct | interpretation |
| --- | --- |
| Function `=:` | visible, fuel-metered inductive unfolding |
| Element `=:` | guarded coinductive definition as a finite cyclic graph |
| Bool/Index self-reference rejection | recursion is restricted to the data/codata sorts that support it |
| lazy conditionals and Boolean words | non-strict evaluation with total sort checking |
| lazy-left append | corecursion on a game spine |
| outcome relations and structural equivalence | observation and bisimulation-up-to |
| explicit budgets | the operational replacement for bottom |

Finite cyclic graphs represent eventually periodic behavior. Productive
nonperiodic streams, such as the genetic option sequence for `omega`, require a
higher-order generator and are not part of the current language. The symbolic
ordinal and surreal worlds remain essential: a stream presents observations,
while a symbolic normal form supports exact arithmetic and birthdays.

Future language work is listed in [`docs/ROADMAP.md`](../../docs/ROADMAP.md).

## References

- D. A. Turner, “Total Functional Programming,” *Journal of Universal
  Computer Science* 10(7), 2004.
- F. Honsell and M. Lenisa, “Conway Games, Algebraically and
  Coalgebraically,” *Logical Methods in Computer Science* 7(3), 2011.
- A. Abel, B. Pientka, D. Thibodeau, and A. Setzer, “Copatterns: Programming
  Infinite Structures by Observations,” *POPL*, 2013.
- M. Escardo and P. Oliva, “Selection Functions, Bar Recursion and Backward
  Induction,” *Mathematical Structures in Computer Science* 20(2), 2010.
