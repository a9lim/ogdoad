# AGENTS.md — pleroma

Working notes for agents editing this repo. Global rules still apply.

## What this is

Clifford algebras (with nilpotents) over the field-like subclasses of Conway's
combinatorial games. Games under disjunctive sum are an abelian group, **not a
ring** — Conway multiplication is only a congruence on the numbers. A Clifford
algebra needs a commutative scalar ring, so this only lives on the three
field-like cores of game-world, and each is a backend:

- **nimbers** `On₂` — algebraically closed, characteristic **2**. The only
  backend where Clifford gets a genuinely new flavour (alternating polar form,
  `q ≠ b`).
- **surreals** `No` — real-closed, char 0. Cl(p,q) exactly as over ℝ, but metric
  entries may be infinite/infinitesimal.
- **surcomplex** `No[i]` — algebraically closed, char 0.

A pure Rust math core, generic over a `Scalar` trait, with PyO3 per-backend
bindings on top. "With nilpotents" = the quadratic form may be degenerate
(`q[i]=0` ⇒ `eᵢ²=0`); all-zero `q` is the exterior/Grassmann algebra.

## Layout

```
src/
  scalar.rs     # Scalar trait (add/neg/mul/zero/one/is_zero) + an exact
                # Rational used ONLY to validate the engine in char 0, plus an
                # exact Integer (ℤ) used as the coefficient ring for the game
                # exterior algebra (partizan.rs).
  nimber.rs     # On₂ in u64 (= F_{2^64}): nim_add = XOR; nim_mul via Fermat-
                # power recursion, memoised on 2^i ⊗ 2^j. Also nim_square /
                # nim_sqrt (Frobenius & its inverse), nim_trace, and the
                # Artin–Schreier solver (y²+y=c, solvable ⇔ Tr(c)=0).
  clifford.rs   # Metric { q, b, a } + CliffordAlgebra<S> + Multivector<S>.
                # The whole engine, generic over Scalar. geom_product_blades is
                # the core (general-bilinear Chevalley product; reduce_word is a
                # #[cfg(test)] oracle it is cross-validated against). The
                # versor/GA layer: versor_inverse, sandwich, twisted_sandwich
                # (Pin action), reflect, left/right_contract, dual,
                # grade_involution, norm2. Plus even_part / even_subalgebra and
                # direct_sum / graded_tensor.
  surreal.rs    # Conway normal form: Vec<(exponent: Surreal, coeff: Rational)>
                # with recursive exponents. Hahn arithmetic: ω^a·ω^b = ω^{a+b}.
  surcomplex.rs # Surcomplex<S> = adjoin i over any backend.
  classify.rs   # the char-0 Clifford classifier (companion to arf.rs): Cl(p,q)
                # → matrix algebra over ℝ/ℂ/ℍ via the 8-fold table (real-closed
                # surreal/rational) and the 2-fold table (surcomplex). Diagonal
                # metrics; signature read off the surreal/rational signs.
  arf.rs        # Arf invariant (the char-2 Clifford classifier): arf_f2 (F₂,
                # bitmask) + arf_nimber (any nim-field, via symplectic reduction
                # + the field trace). arf_invariant routes to arf_nimber. Also
                # the Dickson invariant: dickson_matrix (rank(g−I) mod 2, the
                # char-2 determinant; ker = SO) + dickson_of_versor.
  witt.rs       # WittClass: the Witt group W_q(F) ≅ ℤ/2 of a finite nim-field,
                # Arf-classified. Makes A⊕A ≅ H⊕H a one-line group identity.
  games.rs      # nim_mul_mex: nim-multiplication as Conway's Turning-Corners
                # mex recurrence (the GAME definition); == algebraic nim_mul.
                # Also general 1-D coin-turning games (grundy_1d) and the 2-D
                # Tartan product (tartan_grundy), with the Tartan/Product theorem
                # (tartan == nim-product of component Grundy values) verified.
  misere.rs     # misère-play outcomes (misere_is_n/_is_p) for any finite
                # impartial game; misère Nim vs Bouton's theorem. The instrument
                # for the non-linear (misère) route to the open question.
  partizan.rs   # short partizan games (sum/neg/order/birthday/is_number) + the
                # exterior algebra of the GAME group: Λ over ℤ on game
                # generators (Clifford-adjacent structure living on all of
                # game-world, including non-numbers ⋆/↑). NB: distinct from
                # games.rs — that is coin-turning; this is partizan + exterior.
  py.rs         # PyO3 per-backend classes (feature = "python"). The backend!
                # macro stamps out <World>Algebra + <World>MV (now incl. the
                # Integer backend). Plus classify/witt/dickson/nim-field/Game
                # bindings.
  lib.rs
examples/tour.rs   # cargo run --example tour   (Rust-only demo)
demo.py            # the same tour from Python
experiments/       # research probes ON TOP of the shipped lib: Arf of Gold
                   # forms, the game-built synthesis, the Arf win-bias,
                   # artin_arf (the trace ↔ Arf unification),
                   # open_question_probe (the polar-form obstruction), and
                   # tartan_bilinear (B realized by Turning-Corners). See NOTES.md.
```

The math thread (Arf↔Clifford, the games bridge, the char-0/char-2 classifier
symmetry, the Artin–Schreier ↔ Arf unification, the open play-semantics
question) is written up in `NOTES.md` — read it before touching `arf.rs`,
`classify.rs`, `games.rs`, `witt.rs`, or `experiments/`.

## Commands

```sh
cargo test                                    # the math core (pure Rust, no Python)
cargo run --example tour                      # Rust demo
python3 -m venv .venv && .venv/bin/pip install maturin
VIRTUAL_ENV=.venv .venv/bin/maturin develop   # build + install the abi3 extension
.venv/bin/python demo.py
```

`maturin develop` needs `VIRTUAL_ENV` set (or a `.venv` in cwd) and `cargo` on
PATH (`. "$HOME/.cargo/env"`).

## Hard rules

1. **The math core is generic over `Scalar` and pure Rust.** PyO3 lives behind
   the `python` feature (`pyo3` is an optional dep; `extension-module` only
   enabled there). This is what keeps `cargo test` from linking libpython.
   Never `use pyo3` outside `py.rs`; never make it non-optional.

2. **The metric carries `q` and `b` independently — do not collapse them.**
   `q[i] = eᵢ²` (quadratic form); `b[(i,j)] = {eᵢ,eⱼ}` (polar/anticommutator,
   i<j). In char ≠ 2 they're linked; in char 2 they are NOT — `b` is alternating
   (`b(i,i)=0`) yet `q[i]` can be nonzero. Collapsing to one symmetric bilinear
   form silently makes every char-2 algebra commutative and throws away the
   entire point of the nimber backend. There is now a THIRD, *optional* field
   `a[(i,j)]` (i<j): the in-order / asymmetric contraction that lifts the engine
   to a general (non-symmetric) bilinear form `B` — `e_i e_j = e_i∧e_j + a_{ij}`
   for i<j; `b` stays the (symmetric) anticommutator regardless. `a` empty ⇒ the
   ordinary Clifford algebra. Build metrics with `Metric::new(q, b)` (a empty),
   `Metric::diagonal`, `Metric::grassmann`, or `Metric::general(q, b, a)` rather
   than the bare struct literal, so the `a` field is handled for you (`a` is keyed
   i<j only).

3. **Signs go through the scalar's own `neg()`, never a literal `-1` or a
   `characteristic()` branch.** The product (`geom_product_blades`, and the
   `#[cfg(test)]` oracle `reduce_word`) emits `S::one().neg()` from the wedge
   antisymmetry. For nimbers `neg` is identity, so `-1 = 1` and char-2
   sign-vanishing falls out for free. Hardcoding signs breaks char 2.

4. **Surreal arithmetic recurses only on exponents.** Every op (add/mul/cmp) on
   a `Surreal` recurses into its *exponents*, which are strictly simpler (lower
   depth) than the number itself. That is the entire termination argument. Never
   write a recursion that calls back on the number.

5. **Per-backend, no mixing.** Each Python backend monomorphises the generic
   engine to one concrete scalar type. Mixing scalar worlds in one algebra is
   impossible by construction (raises `TypeError`) and that's intended — do not
   add a runtime-tagged "any scalar" path.

6. **Verify, don't claim.** Engine + every backend have `cargo test` checks. The
   `associativity_*` tests (incl. `associativity_general_bilinear_form`) are the
   ones that actually catch product bugs, and `general_product_reproduces_reduce_word_when_a_empty`
   pins the general engine to the independent oracle — add a test before trusting
   a new operation. The char-0 classifier is checked against the known low-dim
   table + a dimension-consistency sweep; Dickson against known O(Q) elements;
   the Artin–Schreier solver against the trace obstruction exhaustively on F₁₆.

## Style

- Rust 2021, `cargo fmt` clean, no warnings. License: see `LICENSE`.
- Display is deliberate and should stay readable: blades render `e0e1`;
  coefficients `1`/`-1` are elided; nimbers print `*n`; surreals print CNF
  (`3ω^2 - ω + 5`, `ω^(ω)`, `ω^-1`). Keep `display()` / `Debug` matching this.
- Python operators: `*` geometric, `^` wedge, `<<`/`>>` left/right contraction,
  `~` reverse, `/` divide (scalar or versor), `**` power, `+`/`-`, `==`.

## Testing

`cargo test` is the source of truth and needs no Python. The Python layer is
smoke-tested via `demo.py`. After touching `clifford.rs` or `surreal.rs`, run
`cargo test` **and** rebuild + run `demo.py` — display changes don't surface in
`cargo test`.

## Things that look like bugs but are not

- **Char-2 Clifford over an orthogonal basis is commutative.** `e0*e1 == e1*e0`
  when `b` is empty and the scalar is a nimber. Correct: `{e0,e1}=2B=0` and
  `-1=1`. Set an off-diagonal `b[(i,j)]` to get non-commutativity.
- **Surcomplex over nimbers is degenerate.** `i²=1`, `(1+i)²=0`, not a field.
  That's the theorem — On₂ is already algebraically closed, so `i` adjoins
  nothing. Surcomplex is only meaningful over the surreals.
- **Surreal coefficients are ℚ, not ℝ** — the honest finite truncation of true
  CNF. Exponents *are* fully recursive surreals. Don't "fix" this expecting
  irrational coefficients.
- **`Surreal::inv` returns `None` for any non-monomial.** `1/(ω+1)` is an
  infinite Hahn series; finite-support can't hold it. So `versor_inverse`
  succeeds iff the spinor norm `v ṽ` is a scalar *and* a monomial. Intended.
- **`scalar * multivector` works via the scalar's `__mul__` returning
  `NotImplemented`** so Python falls back to the MV's `__rmul__`. Don't make the
  scalar ops raise on a non-scalar operand — that breaks `omega() * e0`.
- **`nim_mul`'s `1u64 << (1u64 << n)` looks overflow-prone.** It isn't for valid
  u64 inputs: bit positions are < 64, so Fermat indices `n ≤ 5` and the shift is
  ≤ 32.
- **`nim_mul_mex` is the slow *game* definition (the mex recurrence), for
  validation and small arguments only.** It's exponential in the argument size —
  fine up to ~48, infeasible over a whole field like F_{2^16}. For real
  computation use the algebraic product (`nim_mul` / `Nimber.__mul__`), which it
  is proven equal to. Experiments use the fast product and only `nim_mul_mex` on
  tiny fields.
- **Pyright flags `import pleroma` as unresolved.** It's installed in `.venv`;
  the editor's interpreter is the system Python. `.venv/bin/python` runs fine.
- **The `neg_one` branch in `Multivector::display` never fires for nimbers.**
  `neg(one)=one` in char 2, so the `coeff==one` branch catches it first.
  Harmless.

## Math facts worth not re-deriving

- nim-field: `F_{2^{2^k}}` = nimbers `< 2^{2^k}`. `F_n ⊗ F_n = (3/2)F_n` for a
  Fermat 2-power `F_n = 2^{2^n}`; distinct Fermat powers multiply ordinarily.
- A real-closed field gives the full Cl(p,q) classification (8-fold periodicity);
  that's why the surreal backend reproduces ℝ-Clifford with exotic scalars.
- Surreal CNF is the Hahn series field ℝ((ω^No)); the ω-map is the monomial map
  and `ω^a·ω^b = ω^{a+b}` is a group homomorphism (No,+) → (No>0,×).
