# CONSISTENCY.md (the aesthetic ledger)

The aesthetic ledger: a structural/stylistic read of the core, valued like
[`COMPLETENESS.md`](COMPLETENESS.md) — a game value `g` on a pillar blade `e_B` (`e_s` scalar,
`e_c` clifford, `e_f` forms, `e_i` integral, `e_g` games, `e_o` ogham, `e_y` py). Claim
level **interpretation**: one reviewer's eye, but every item is checked against
the actual source, not vibes. Numbers ≈ focused days; `±n` flags an a9 scope
call (API-churn, mostly); `↑` is worth less than any number but strictly
positive; `*n` is real, on-thesis, unscheduled. Its soundness sibling — claims that
are machine-verified vs source-pinned vs merely asserted, not taste — is
[`CORRECTNESS.md`](CORRECTNESS.md).

---

Currently empty. The 2026-06-20 Rust-core taste audit was played the same day and
recorded as [`DONE.md`](DONE.md) → `consistency-sweep`; the audit prose that stood here
(the pre-sweep-tree findings) is preserved in git history.

One `↑`-grade nit was consciously **deferred rather than played** — `precision-K`, the
`Qp<…, K: u128>` vs `Laurent<…, K: usize>` precision-width disagreement, whose unification
cascades across the whole p-adic const-generic surface (`Qp::Int = Zp<P,K>`, the
`impl_scalar_ops!` macro, `Valued`/`PrecisionScalar`/`HasRingOfIntegers`, `springer_decompose_qp`,
the `small/analytic` impls). Disproportionate to a cosmetic nit; reopen as a focused
standalone pass if it ever bothers more than this sentence does (per the `consistency-sweep`
boundary note).

The next taste-style audit lands its findings here: `src/ogham/` and `src/py/` were both
out of scope for the 2026-06-20 Rust-core pass and are the standing candidates — see
[`CONTINUATIONS.md`](CONTINUATIONS.md) → `ogham-reflect` for the ogham consolidation (its
part (3) is a CONSISTENCY-style audit of `src/ogham/` after three builds of growth).
