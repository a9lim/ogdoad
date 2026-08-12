# Lean formalization

This standalone Lean 4 project tests how much of the current proof threads
can be moved from checked prose and exhaustive computation into a proof kernel.
It pins Lean and mathlib independently of the Rust workspace.

```sh
cd formal
lake update       # only when intentionally refreshing the pinned manifest
lake build
```

The sources contain no `sorry`, `admit`, or custom `axiom` declarations.

## Gold diagonal source

[`Ogdoad/GoldDiagonal.lean`](Ogdoad/GoldDiagonal.lean) kernel-checks the
load-bearing algebra of the all-exponent Gold diagonal theorem:

- the two relative-trace coordinate identities in a characteristic-two
  quadratic tower with `sigma(u) = u + 1`;
- reconstruction of the upstairs trace-dual from the two downstairs duals;
- vanishing of the absolute trace of a base-field element in a quadratic
  extension; and
- the full finite-field exact sequence
  `im(w ↦ w²+w) = ker(absolute trace)`, proved by rank--nullity and trace
  surjectivity, plus the additive and tower-lifting identities.

The concrete canonical nim-field recursion and its basis identifications are
implemented and exhaustively tested in `src/forms/trace_form.rs`. Lean proves
the abstract identities and the finite-field existence theorem from the stated
hypotheses; it does not encode the `u128` nim multiplication implementation.

## Brown game semantics

[`Ogdoad/BrownGame.lean`](Ogdoad/BrownGame.lean) kernel-checks the algebraic
resolution of the independent `over` invariant question:

- every Brown refinement on an exponent-two additive group splits canonically
  as `q = lift(ell) + 2Q`, with `ell = q mod 2` additive and `Q` an ordinary
  characteristic-two quadratic form;
- the corrected polar is `B_Q = b + ell tensor ell`, and Lean proves it is
  alternating, symmetric, and biadditive;
- the converse construction and pointwise round trip show that no Brown value
  is lost in the split;
- on a two-divisible source, every exponent-four Brown-compatible quadratic
  value is zero, and every additive exponent-two quotient is trivial; and
- the explicit abelian extension `Z/4 -> Z/8 -> Z/2` realizes the odd Brown
  line only after a section is chosen, proving that a bare central extension
  does not determine the phase; and
- the single partizan selector `{A_(Q+ell) | A_Q}` has outcomes `N,R,P,L`
  for residues `0,1,2,3`, with a kernel-checked fixed decoder back to `q`.

The external instantiation remains source-pinned: Moews proves the additive
short-game group is a direct sum of copies of `Z[1/2]` and `Z[1/2]/Z`, hence
is two-divisible.  The Lean file proves the full implication from that abstract
divisibility hypothesis but does not encode short games or Moews's theorem.
The Lean selector layer abstracts each shipped ordinary quadratic arena by its
proved `P iff bit = 0` contract; it checks the partizan root semantics and
four-class decoder rather than re-encoding the full weighted-source arena.

## Game-exterior divisibility obstruction

[`Ogdoad/GameExterior.lean`](Ogdoad/GameExterior.lean) formalizes the algebraic
core of the resolved `tisn` problem:

- an additive grade-one realization in an arbitrary associative ring;
- explicit `n`-th roots of a torsion game and of an arbitrary second input;
- the resulting square-zero and polar-anticommutator-zero identities; and
- coefficient-valued `Q(t)=0` and `B(t,x)=0` corollaries when the coefficient
  map into the Clifford algebra is injective;
- polarization forced by the Clifford relations, symmetry of the polar value,
  and `Q(x+t)=Q(x)`, the torsion-coset invariance behind quotient factorization.

The external game theorem remains source-pinned rather than axiomatized here:
Moews proves that the short-game group is a countable direct sum of
`Z[1/2]` and `Z[1/2]/Z`, hence power-of-two division is available, and that all
finite-order short games have power-of-two order.  The Lean file proves the
entire ring-theoretic implication from explicit roots, without encoding the
short-game group itself.

## `off`

[`Ogdoad/Off.lean`](Ogdoad/Off.lean) formalizes the load-bearing algebra of the
resolved full-`On₂` classification through a set-sized algebraically closed
characteristic-two field:

- Frobenius and Artin–Schreier surjectivity;
- an explicit change of every normalized symplectic pair to a hyperbolic pair,
  preserving its plane span;
- simultaneous conversion of a supplied symplectic family; and
- the polar-radical normal form `Q = ℓ²`, with either `ℓ = 0` or a
  codimension-one zero kernel after normalizing a vector with `ℓ(e) = 1`.

The set-sized field is a proxy, not an encoding of Conway's proper class.  The
mathematical reduction is that any finite form and its finitely many algebraic
roots lie in a set-sized algebraically closed subfield.  The standard
symplectic decomposition theorem for a finite-dimensional alternating form is
used as the interface to `hyperbolic_family_of_symplectic_family`; this project
does not yet re-formalize that general linear-algebra theorem.

## Lenstra excess

[`Ogdoad/Excess.lean`](Ogdoad/Excess.lean) formalizes theorem-level algebraic
ingredients used by the Lenstra-excess reductions, including the exceptional
`2·3^k` column:

- the first-non-`p`-th-power definition of finite excess;
- the group-theoretic lower bound: a shared order class coprime to `p` makes
  the `0,1,2,3` translates `p`-th powers, hence `m_p ≥ 4`;
- the corrected norm
  `(kappa+a)(kappa+a+1) = kappa²+kappa+(a²+a)`, specializing to
  `kappa²+kappa+omega`;
- the exact cyclic-group and finite-field Euler-quotient criteria for being a
  `p`-th power, including the prime-order shortcut used at Fermat-prime levels
  and the equivalence between maximal order and simultaneous non-`p`-power at
  every prime divisor of the ambient cyclic-group order;
- the Conway-unit Euler-symbol identity
  `c^((q-1)h)=w^h` from `c^q=c*w`, which is the finite-field core of the
  paper's exact cyclotomic lift of the selected Fermat residue symbol;
- the abstract semiprimitive Gauss-table core: the nontrivial additive
  character sum on field units, multiplicative change of variables, the
  one-exceptional-line evaluation, denominator-cleared large and small period
  values, and invariance of every symmetric labelled sum under moving the
  exceptional label.  The quadratic finite-field trace-line decomposition and
  identification of that label with the selected Fermat symbol remain
  paper-level;
- the abstract one-phase Conway-basis core: multiplying an entire upper block
  by one fixed element gives one common character value, every basis monomial
  remembers only its upper-block weight, and inverse squaring detects the
  identity on an odd-order target.  It also checks the finite counting core
  obtained by deleting the uniquely trivial base line from a uniformly
  labelled projective set, and the characteristic-two norm collapse used in
  the labelled first-upper-block factorization.  It now also checks the
  trace-one universal-translation collapse and the identity making the marked
  constant term exactly the one-phase defect.  The literal nim multiplication
  `e_(m+i)=c_n*e_i`, triviality on the lower finite-field block, and the
  projective-line/cyclotomic-product specialization identifying
  `H=C^(-2)` and `B_1(0)=S_d(a)` remain paper-level;
- the denominator-cleared ordinary affine-orbit identity reducing
  `(Y+1)^Q+lambda*(Y+1)` to `Y^Q+lambda*Y+(1+lambda)`.  The additive
  polynomial product over `F_Q`, rescaling invariance of the complete
  translate set, and the marked-scalar Kummer interpretation remain
  paper-level;
- the first exact dependency composition in the selected `p=359` chain and
  invariance of marked power status under a ring equivalence.  The maintained
  stdlib certificate constructs the complete sparse degree-3,504,820
  full-conductor polynomial and checks its term counts and coefficient hash.
  The finite-field dependency and root-to-factor deductions remain
  paper-level.  A checked-in 438,103-byte Hilbert-root artifact and maintained
  python-flint verifier now instantiate the compact certificate: full mode
  verifies `y^179=A`, recomputes `theta=Norm(1+y)`, and checks its
  nontrivial 359-phase, proving `m_359=1` by exact finite computation.
  None of this finite-field computation is kernel-checked in Lean. Historical
  git blobs also contain two complete external exact-run traces with the same
  1,743,227-term nonidentity endpoint; the stdlib provenance checker verifies
  their hashes and endpoints, so they are source-pinned corroboration rather
  than the local proof;
- the first row beyond the vendored table, `p=719`, has a paper-level nested
  reduction to one degree-179
  factor of `(T^359+1)^179+(kappa_89+1)` over `F_(2^7029220)` and one
  selected Euler test on its value at one.  A crossed-tower reformulation
  reduces a replayable certificate to two 438,103-byte payloads over
  `F_(2^179)` and a final Euler test in `F_(2^64261)`.  Lean checks the
  generic scaled-product and conditional nested-exponent cores; the
  field/Kummer/norm and numerical-exponent specializations remain paper-level.
  All four crossed payloads are now checked in.  The maintained python-flint
  verifier reconstructs them together with the `p=359` artifact, checks
  `a^359=(1+x)/c`, verifies `f_a(a)=0` in authoritative full mode,
  recomputes `W=v^19580*f_a(v^(-1))`, and obtains a nontrivial 719-torsion
  Euler phase.  This proves `m_719=1` by exact finite computation plus the
  paper-level crossed-tower deduction, not by Lean.  The two cheaper norm
  shadows and their `mu_719` phase-blindness are also paper-level;
- the locally certified `p=727` row: Lean checks that 727 is prime, the exact
  order arithmetic `ord_727(2)=121`, and the selected degree
  `20*121=2420`.  The maintained stdlib certificate constructs and proves
  irreducible the literal polynomial `P_alpha_11(X^121)` and evaluates its two
  Euler classes, obtaining `m_727=1`; that binary finite-field computation is
  not kernel-checked in Lean.  This is the deliberate finite-row cutoff; the
  remaining ordinary target is the uniform theorem;
- the characteristic-free canonical-lift reparametrization
  `A=W/(W+1)^2`, `A*C=-W/(W+1)^3`, `W=A*C^(-2)`, its denominator-free
  discriminant recursion, and the odd-Kummer square-class equivalence used in
  the paper's global-reciprocity torsor no-go; the number-field ramification
  and Hilbert-symbol deductions themselves remain paper-level;
- the denominator-free quadratic-tail Kummer transport
  `2*[c_j]=i([a_(j-1)])` and `2*[a_j]=3*i([a_(j-1)])`, which underlies the
  paper's exact `3/2` propagation of a Fermat-prime obstruction through every
  later Conway level, together with the norm/Frobenius identity cubing the
  corresponding selected Euler symbol; the finite-field quotient
  identifications and Capelli factorization corollary remain paper-level;
- the weighted-selector algebra: inverse-pair and decomposition-coset first
  moments vanish for unmixed cyclotomic divisors, while the odd geometric sum
  at `W^(F_n/ell)` vanishes exactly when the desired selected residue is
  nontrivial; the global ray-class and local Hilbert-symbol interpretation
  remains paper-level;
- the abstract coprime-torsion separation: two classes of coprime exponents
  cannot cancel in one multiplicative reciprocity product.  The paper applies
  this only after proving, at number-field level, that the actual C and D
  Kummer extensions remain linearly disjoint over their common cyclotomic
  base;
- the affine mixed-selector algebra: a nonzero affine coefficient isolates one
  cyclotomic coordinate, its relative quadratic norm is `A + R + R^2`, the two
  orientations carry reciprocal Conway-unit values, and relative norm two is
  equivalent to a shifted-discriminant square.  Abstract orbit lemmas check
  that a transitive invariant valuation vector is constant and that a unique
  support point is fixed by every stabilizer; these are the abstract constancy
  and support-fixing ingredients in the paper's lower-field non-descent and
  degree bound.  It also checks that every
  nonsymmetric element can be rescaled by an involution-fixed scalar into the
  affine anti-trace normalization, and that the local oriented residue has a
  rational `ell`-power parametrization.  Finally, an abstract anti-invariant
  character kills every norm divisor while its oriented quotient retains the
  square of the selected value, and the abstract Jacobi-collapse lemma shows
  that a residual symbol inverse to the distinguished one makes the oriented
  half-resultant exactly its square.  The cyclotomic prime decomposition,
  norm-valuation covariance, stabilizer-index/Galois-degree passage,
  valuation-one selector and its field-degree interpretation, simultaneous
  approximation, elimination of every `ell`-adic pairing, preservation
  of the oriented ray character under fractional rescaling, and the resulting
  global reciprocity and Jacobi-symbol identities remain paper-level;
- the finite additive translation identity behind the paper's exact saturation
  theorem: translating a finite fibre through a finite additive group covers
  every point with constant multiplicity.  Its specialization to the selected
  trace-one polynomial and the distinctness of the fibotomic translates remain
  paper-level;
- the abstract mixed-ray character no-go: weight-one equivariance permits
  both zero and nonzero distinguished values, while every fixed source class
  is annihilated.  An invariant homomorphism evaluates every finite integral
  group-ring product through its augmentation alone, and every abelian
  quotient of an odd dihedral group kills its translation subgroup; the
  anti-invariant coboundary is `-2*x` and vanishes exactly with `x` in odd
  characteristic.  The reflection-symmetrization identity also constructs a
  fixed norm witness `((y*s(y))^r)/a` when `2*r=ell+1`, the algebraic core of
  the paper's descent to the non-Galois reflection field, and packages the
  resulting ordinary-witness/fixed-witness equivalence under equivariance of
  the norm. The Artin map, finite-etale base-change interpretation, cyclic
  Hasse theorem and resulting Hasse norm principle for the reflection field,
  Brauer projection/corestriction, and class-field interpretation remain
  paper-level;
- the global split-ray algebraic core: Lean checks descent of an `ell`-th
  root through a degree-`(ell-1)` norm equation, propagation of one marked
  zero through a rank-one orbit, the three exact integer inequalities used with
  the Amoroso--Dvornicich height bound, the rank--nullity lower bound after
  imposing local splitting conditions, and separation of marked-vector and
  selected-functional nonvanishing on a one-dimensional eigenspace.  For the
  cubic arm it additionally checks the direct circular-unit numerical height
  gap and propagation
  of a weight-one character across a transitive prime orbit.  The
  cyclotomic heights, unit-representation multiplicities, unramified-base
  hypotheses and local conductor
  calculation, Kummer extensions, ray class characters, and Artin reciprocity
  specializations remain paper-level;
- the complete cubic multikummer rank core: Lean checks that a bounded
  power-relation kernel gives the advertised lower bound on the realized
  conjugate lattice, that a split-ray surjection transfers this dimension,
  and the combined rank inequality.  The circular-unit lattice and index
  theorem, its character decomposition, local conductors, and the selected
  Artin-reciprocity specialization remain paper-level;
- the marked decomposition-character core: Lean checks iteration of the
  Frobenius covariance relation, vanishing forced by a conflicting
  complex-conjugation eigenvalue, and the necessity of matching the unique
  eigenvalue seen by a nonzero marked coordinate.  The cyclotomic projector,
  unit-representation multiplicity, and reflected Kummer character remain
  paper-level;
- the two denominator-free conductor-five identities and their quotient form
  `d + d^-1 = 2 + 5/(x^2+x-1)`, the algebraic coefficient in the paper's
  exceptional-arm reflection field.  The cyclotomic number-field extension,
  local Hilbert-symbol inventory, and Hasse/weak-approximation consequences
  remain paper-level;
- the two realification identities
  `(1+x)(1+x^-1)=2+x+x^-1` and
  `rho*j(rho)=(z/a)*rho^2` underlying the cubic and ordinary
  reflection normal forms; the corresponding number fields, local norm
  equivalences, and global selectivity boundary remain paper-level;
- the reciprocal cubic relation for `beta_k=gamma_k^-1`, the immediate
  trace-Gram and Moore-determinant polynomial identities proving scaled
  self-duality, the generic Hilbert--90 Frobenius-twist conjugacy and
  norm-one order-three identity, the abstract
  cumulative/exact cubic Frobenius projectors and their successive-value
  identity, and the characteristic-two derivative induction preserving
  `X*P'=P+1` under `P -> P^3+P^2+1`.  The irreducible
  cyclotomic-block decomposition, exact orbit ranks, Scheerhorn
  completely-normal conclusion, absolute Moore diagonalization, resultant,
  and finite-field Hilbert--90 instantiation remain paper-level;
- the cubic ancestral-Jacobian core: Lean checks the derivative of the cubic
  edge, the full iterated factorization through the canonical product of
  translated iterates, its lower-tail line factorization, lower-coefficient
  linear combinations on that line, and the canonical-root square ratio in a
  field.  Its identification with the full iterated derivative, the selected
  tower specialization, and the current-prime homogeneous Kummer-weight
  interpretation remain paper-level;
- the mixed ancestral-coordinate core: Lean checks the translated cubic
  relation, recursive quadratic reduction, uniqueness of a quadratic normal
  form at relative degree three, the explicit mixed vanishing witness, and
  recovery of the top selected coordinate.  The multivariable kernel-ideal
  equality, selected finite-field specialization, and Euler interpretation
  remain paper-level;
- the translated selected Singer cubic for
  `epsilon_k=eta_k+1`, its symmetric-coefficient Moore identity, the exact
  constant-off-diagonal trace-Gram determinant, and preservation of element
  order by a coprime power.  Lean also checks the three-term characteristic-two
  square-root bridge from `epsilon_k` to `beta_k` and its Singer exponent
  identity.  The paper proves the universal determinant-one half-circulant
  inverse in the group algebra.  From the cyclotomic Frobenius projectors it
  also proves that `epsilon_k` is absolutely normal and that `eta_k` spans
  the trace-zero hyperplane; it does not claim complete normality for
  `epsilon_k`.  A separate exact degree-81 bit-polynomial certificate uses
  kernel `decide` to check the Singer, normalized-beta, half-circulant,
  current-failure, full Kummer-kernel, Rabin-residue, and selected-ancestry
  break identities at the actual current prime `2593`.  The standard
  Moore-determinant interpretation of the maintained script remains
  paper-level linear algebra;
- the denominator-free first-Witt recurrence for the lifted Conway unit,
  including its selected terminal numerator and the next-discriminant relative
  norm; identifying these expressions with a local Fermat quotient requires
  the paper's unramified/étale hypothesis;
- the homogeneous leading-unit recurrence after a last simple ramified Conway
  step, its Cayley-coordinate initial term, the exact branch-sensitive
  nonvanishing factors, and a two-coordinate toy model satisfying both
  nonzero equivariance on a local line and vanishing on the distinguished
  prime-above-two orbit; the valuation-theoretic interpretation and the claim
  that the resulting unit is not a local `ell`-th power remain paper-level;
- the single-quadratic factorization underlying the paper's universal
  Dickson--Conway resultant; root enumeration, the full resultant identity,
  and the compatible parallel-ray torsor remain paper-level;
- the exact quotient-order factorization used by relative-order products, with
  maximality of the individual quotient factors deliberately left as an input;
- the finite-level Popovych primitive-product equivalence: the selected
  product is primitive exactly when every positive relative Fermat divisor is
  the full Fermat number, leaving those universal relative equalities visible;
- the full-primary quotient lemma behind the norm-blindness obstruction, and
  the simple-zero theorem showing that the cubic norm discards the current
  Kummer coordinate while its first transverse derivative survives;
- the cubic arm's square-zero exceptional-residue calculation modulo `3n`,
  including the distinguished lift `an - 1`;
- the denominator-free square-zero cross-product identity behind the
  exceptional arm's canonical four-Jacobi detector;
- the denominator-free alternating-determinant identity behind its quadratic-
  relative Eisenstein reduction;
- the exact coboundary-to-fibotomic projection, normalized
  Artin--Schreier quadratic, and symmetric cubic norm-coherence identity behind
  the Conway C-to-D selector bridge;
- naturality of an Artin--Schreier equation together with a chosen
  `ell`-th root under every ring map.  The exact degree-18 finite-field
  countermodel showing that primitivity plus the literal C-to-D rational
  selector does not transfer the current factor is certified by
  `experiments/cyclotomic_3k_family.py`; Lean checks only this naturality core,
  not the bit certificate, its exhaustive degree-nine fibre census, or its
  deliberately missing selected lower norm;
- the selected cubic's three auxiliary symmetric coordinates: Lean checks
  that `g=x^2+x+1` has relative trace one, middle coefficient `a+1`, and
  norm `a^2+a+1`.  The exact `k=4` countermodel in
  `experiments/cyclotomic_3k_family.py` retains primitivity, the literal
  rational selector, and the selected trace and norm while changing only the
  middle coefficient and making the Artin--Schreier root a `163`rd power;
  the stronger fixed witness in the same script retains primitive lower and
  upper coordinates and the literal selected cubic equation, hence all three
  symmetric coordinates, while still failing at `163`.  Lean additionally
  checks the two-point fibre of `x^2+x+1` and that the three selected
  symmetric coordinates expand to one rigid cubic.  It does not check either
  finite-field witness, its irreducibility, primitivity, or power tests;
- the alternating `F_4` translate of the selected exceptional cubic, including
  its twisted recursion, Artin--Schreier coefficient, symmetric-product norm,
  invariance of power membership after multiplication by a known power, and
  the uniqueness step forcing a norm-coherent chain of lower power roots.
  The finite-field tower, irreducibility after constant extension, current
  order calculation, and Kummer interpretation remain paper-level;
- the alternating twisted-fibre algebra: root-of-unity scaling preserves an
  `ell`-th power, the scaled cubic Frobenius orbit preserves its constant
  product, the characteristic-two cubic coefficient expansion is exact, and
  the universal Jacobian numerator specializes to the selected lower
  `gamma`.  Fibre degree, etaleness, rational-point counts, Capelli
  factorization, and the invariant-ring specialization remain paper-level;
- the characteristic-two Mobius trace identity
  `M + M^(-1) = (w^2+w)^(-1)` behind the exceptional arm's selected
  one-variable Dickson critical value;
- the denominator-free cyclotomic Artin--Schreier identity used by the paper's
  trace-one, norm-coherent alternative coefficient; the finite-field trace,
  degree, norm, and primary-power consequences remain paper-level deductions;
- the general uniqueness lemma that transports compatible power roots through
  a multiplicative map when powering is injective, plus the symmetric
  pair-product coefficients (D, C*E, E^2) behind the iterated cubic Dickson
  fibre;
- the choice-free Conway--Fermat root elimination: if `b^ell=a`,
  `ell*d=q+1`, and `b^q=b`, then `b^2=a^d`, and for `q=2Q` the selected root
  is explicitly `b=(a^d)^Q`;
- the characteristic-two Fibonacci doubling laws and trailing-zero
  compression
  `S_(2^t*h+1)=S_(h+1)^(2^t)+T_t(a)*S_h^(2^t)`, including its exact ratio
  form and the complementary-index nondivisibility used in the
  Conway--Fermat continued-fraction reduction; and the formal-derivative
  identities `S'_(2r)=0`, `S'_(2r+1)=S_r^2`, which show that an odd selected
  zero is simple whenever its half-index value is nonzero;
- the hypothetical-failure Fibonacci block core: after `S_d(a)=0`, all blocks
  satisfy `S_(kd+r)(a)=S_(d+1)(a)^k*S_r(a)`; Cassini gives
  `S_(d+1)(a)^2=a^d`, and `ell*d=2^m+1` forces
  `S_(d+1)(a)^ell=a`.  The selected-field and quotient-polynomial
  interpretations remain paper-level;
- the complementary factor/cofactor core: the power-of-two-plus-one Fibonacci
  derivative is one, while product zero plus the differentiated Bézout value
  one forces exactly one factor to vanish and makes the corresponding
  `ZMod 2` resultants sum to one.  Fibonacci divisibility, the selected
  finite-field specialization, and the resultant/norm identification remain
  paper-level;
- the selected CRT-projector core: the differentiated factorization gives two
  complementary idempotents, their branch orientation is exact over a field,
  every Bézout support certificate gives the same pair, quadratic trace kills
  either scalar bit in characteristic two, and quadratic norm preserves an
  idempotent.  The polynomial CRT specialization, selected-resultant
  orientation, and characteristic-polynomial interpretation remain
  paper-level;
- the twisted-fibre weighted core: the cubic pseudonorm of a Kummer root is a
  lower power root independent of the root choice, its normalized defect
  raises to the original Euler class, and a pure eigenweight acquires exactly
  the corresponding power of that monodromy.  The mixed core checks that all
  three complementary Fourier products equal the same pseudonorm, every
  exponent divisible by `ell` collapses through `v^ell=u`, and a scalar in
  a power basis has no nonzero-weight coordinates.  The monic
  Kummer-algebra grading, finite-field Fourier identification, invariant-ring
  statement, and split-factor orientation boundary remain paper-level;
- the cubic selected-phase trace core: in characteristic two, norm one
  together with trace and inverse trace one forces the phase to be one, since
  its orbit cubic is `X^3+X^2+X+1=(X+1)^3`.  The strengthened phase-orbit
  core checks the characteristic-two half-discriminant/root-difference
  factorization and collision criterion, distinguished-root membership from
  equal norm-one trace and inverse trace, and the forward periodicity of every
  shifted power sum once the powered roots are one.  The polynomial
  discriminant identity, finite-field Frobenius specialization,
  orbit-separation specialization, irreducibility statement, converse
  periodicity implication, and identification with the selected phase remain
  paper-level; the selected nonvanishing assertion remains open;
- the exceptional phase-identification core: norm/Euler exponent transport,
  removal of an Euler-trivial ancestry factor, the square carried by an
  antiunit quotient, and formal inversion of an assumed inverse-phase
  identity.  The
  finite-field norm, residue-index, Jacobi, weighted-fibre, and selected
  sextic identifications, including the selected inverse orientation, remain
  paper-level, as does the still-open
  nonvanishing of their common phase;
- the marked Hilbert--sextic bridge core: Lean checks transport of a Kummer
  quotient equality to Euler phases, the adjacent-Hilbert exponent identity,
  and the primitive-sixth-root coefficient and inverse-factor formulas. The
  selected finite-field Hilbert, sextic, Jacobi, and Euler identifications
  remain paper-level;
- the current-primary support core: Lean checks the primitive-sixth-root
  arithmetic and that phases of coprime primary orders cannot cancel. The
  cyclic-torus realization of every nonempty support profile, its finite-field
  degree and norm calculations, Dickson cubic shape, and selected
  interpretation remain paper-level;
- the exceptional four-block core: Lean checks the alternating base-`q`
  decomposition of the Euler exponent and its cross-multiplied
  commutative-group quotient identity.  The binary-complement calculation,
  finite-field Frobenius specialization, and identification with the inverse
  conductor-five residue phase remain paper-level;
- the exceptional adjacent-quartic core: the four-point `F_4` coset product
  is `x^4+x+1`, the two oriented corrected norms multiply to that same
  quartic, its three selected conjugates have cubic
  `T^3+T^2+T+Phi_5(a)`, and its downward norm is exactly `Phi_5(a)`.
  The finite-field Kummer-quotient injection, use of the full `F_16` orbit
  table, Capelli specialization, and the still-open nonpower assertion for
  the selected adjacent value remain paper-level;
- the adjacent Hilbert-pair core: Lean checks the characteristic-two
  Möbius add-one and recovery identities, inverse-unit Frobenius ratio,
  ratio-plus-norm rigidity, selected quartic orientation, and the
  maximal-Fermat count identity. The finite-field bijection, power-subgroup
  criterion, rational-point count, and selected Kummer interpretation remain
  paper-level;
- the selected reciprocal trace-fibre core: the universal Jacobian numerator
  at `(a,a+1)` is `a^2+a+1`, the characteristic-two discriminant of
  `X^3+C*X^2+D*X+1` is `(C*D+1)^2`, and injective lower
  `ell`-powering forces the norm of a reciprocal power root to be one.  The
  actual edgewise finite-etale fibres and their rational-point counts remain
  paper-level;
- the recursive trace-flag core: a compatible full lower flag has the same
  fibre as its immediate coordinate, every weighting formed only from that
  flag factors through the immediate coordinate, and a sum of linear Fourier
  functionals composed with one top trace is the corresponding summed
  downstairs functional.  Finite-field trace transitivity, the selected
  Singer fibre, and the character/Wendt identifications remain paper-level;
- the cubic affine-line core: translating the top cubic coordinate by a
  lower-field scalar preserves its lower affine line, and the selected line is
  contained in the trace-annihilator once the trace kills the top coordinate
  and its square.  Trace-pairing dimension, projective character sums, Gauss
  magnitude, and the finite-field self-polar equality remain paper-level;
- the projective incidence core: from the projective-plane intersection
  matrix Lean proves `I^2=q Id+J`, its restriction `I^2=q` on zero-sum
  vectors, and the two-step phase-swap identity. Projective-plane incidence
  counts and finite-field character/Gauss specializations remain paper-level;
- the norm-coherent Euler-tail core: Lean proves abstractly that a sequence
  whose relative norms and Euler exponents factor compatibly has one constant
  phase along its whole tail, including the same statement for an affine
  family. The ordinary Kummer and cubic finite-field specializations remain
  paper-level;
- the fixed-prime cubic-tail core: Lean checks relative-norm Euler transport,
  the additive--multiplicative selector identity, affine-translate phase
  descent, restriction of Euler phases, the birth-edge inverse-square
  relation, and equality of odd-torsion phases with the same square. The
  finite-field exponent specializations and literal Conway tower remain
  paper-level;
- the cubic birth-secant core: Lean checks the exact two-secant factorization,
  transport of two Frobenius weights to one selected phase both exactly and
  modulo the current torsion order, finite-product aggregation, and
  coprime-primary noncancellation. The cyclotomic weight parametrization,
  shell cancellation, and selected finite-field specialization remain
  paper-level;
- the selected cubic coupled-root core: one chosen `ell`-th root of `eta_k`
  transports explicitly to compatible roots of `epsilon_k` and `beta_k`, with
  their exact diagonal weights.  Every Frobenius monomial in the chosen root
  reduces to one residue weight in the same Kummer algebra.  The finite-field
  Kummer-class, common-compositum, lower-root uniqueness, and invariant-ring
  interpretations remain paper-level;
- the current cubic weight core: Lean checks the factorization
  `q^3=1+ell*(q-1)*u`, the resulting monodromy of a chosen root of
  `V^ell=tau_k`, and the corresponding monodromy of every pure nonzero
  weight.  The finite-field fixed-point criterion, Kummer/Euler equivalence,
  separable resultant product, and invariant-ring interpretation remain
  paper-level;
- partial Frobenius-trace additivity, Frobenius commutation, index splitting,
  and the exact conjugate descent
  `Tr(1+T_s(a))=T_s(A)` when `a^(2^d)=a+A`, which underlies the paper's
  full-ancestry trace no-go;
- the literal-top-bit multiplication identity and exact powers of its
  Fibonacci companion, including the equivalence between scalar return and
  `S_r(a)=0`; this identifies the hidden projective/Singer order with the
  original Conway--Fermat first-zero target rather than proving maximality;
- the characteristic-two cubic Horner reduction modulo
  `Y^3 + X*Y + X^2` and the determinant of its explicit multiplication
  matrix; these are the algebraic core of the exact selected-resultant screen,
  while the complete integer-bit polynomial loop and its finite outputs remain
  script-level checks;
- the algebraic parametrization identities underlying the paper's rational
  normalization of the Conway resultant correspondence by
  `alpha(c)=c^2+c` and `beta(c)=c^3+c^2`, including translation of the two
  child values and their exact product `beta(c)*beta(c+1)=alpha(c)^3`;
- the cubic map on the norm-one fibotomic coordinate
  `Phi(x^3)=Phi(x)^3/(1+Phi(x))^2`, its cube-class form, and the explicit
  cube forced by the preceding Conway driver; these show that old maximal
  cube-subgroup order is automatic ancestry data, not a new nonresidue;
- the denominator-free quadratic-remainder norm
  `(U+xV)(U+x'V) = U^2 + YUV + Y^3V^2` used by the paper's one-branch
  Conway--Fermat descent;
- the monic quotient/remainder independence core: every prescribed quotient
  and degree-bounded remainder occurs uniquely, while an additive coordinate
  equivalence reflects zero, realizes every coordinate pattern uniquely, and
  remains independent of a freely prescribed quotient.  The actual Conway
  tree coordinate equivalence and Euclidean/subresultant interpretation remain
  paper-level;
- the abstract Fibonacci quotient-defect core: from formal symbols satisfying
  the differentiated quotient relation, Lean checks that the two defects
  reduce to `drho` and `rho + X*drho`, reconstruct `rho`, and are divisible by
  the selected factor under exact divisibility.  Their specialization to
  polynomial derivatives, odd/even coefficient blocks, and the first
  `A`-adic digit remains paper-level;
- the Fermat quotient-window core: multiplication of a local parameter by an
  explicit unit preserves divisibility by every ideal power, equality of
  dividends in a truncated coefficient ring forces equality of quotient
  windows, every positive Fibonacci value has constant term one, and the
  trailing-zero formula becomes independent of its positive cofactor when the
  variable is nilpotent.  Lean also checks that a first surviving boundary
  monomial fixed by the common unit factor is transported unchanged to the
  quotient.  The Euler--Lucas endpoint windows, Fermat-factor valuation,
  reciprocal boundary calculation, completed-local-ring coordinate, and
  selected specialization remain paper-level;
- the fixed-`A` Hasse-jet ring core: Lean checks the second-digit
  rearrangement, the exact first-escape identity and quotient specialization,
  the order-`2R` normal form, the odd-branch quotient-ring collision, and the
  linear equivalence of its two arithmetic forms.  The Hasse block bookkeeping,
  canonical-digit recursion, selected polynomial specialization, finite-field
  order calculation, and proof that the displayed partial-trace prefactors are
  nonzero remain paper-level;
- the odd fixed-jet recovery core: Lean checks the strengthened short-factor
  window, the opposite-end size exclusion, the odd-index divisibility
  contradiction, the relevant Lucas parity and Hasse-composition coefficient,
  and nonvanishing of the recovered product.  The selected Fibonacci/Hasse
  specialization remains paper-level;
- the Fermat lower-semiconjugacy core: Lean checks the
  denominator-cleared cubic semiconjugacy, cyclic product reindexing,
  exact odd half-power cancellation in characteristic two, the selected
  quadratic-edge norm formula, and the final degree-divisibility
  exclusion. The Binet specialization, identification of the
  `Frob^s` orbit with `E_(n-1)/E_(v_2(s)-1)`, and iterated-resultant
  degree bookkeeping remain paper-level;
- the pointwise Fermat-saturation core: Lean checks the universal Fibonacci
  factorization and its exact two-branch zero criterion, the normalized
  Frobenius coboundary and its nontriviality, extraction of the selected
  monomial from equal Frobenius powers, and the abstract order formula. The
  minimal-counterexample Conway specialization and gcd/LTE arithmetic remain
  paper-level;
- the first additive-edge core: Lean checks the Fibonacci coordinates of every
  power across one Conway quadratic, the resulting additive trace, transport
  of the exact monomial equality together with its conjugate, and the
  arithmetic exclusion `Q+1 ∤ K`. The minimal-failure specialization,
  derivation of the conjugate equality by finite-field Frobenius, and lower
  Fibonacci zero-period interpretation remain paper-level;
- the cross-level additive-edge arithmetic: Lean checks the exact equality
  between the common divisors of Q+1 with ell-1 and d-2, and transport of
  that gcd through the selected exponent relation. The lower
  fibotomic-stratum interpretation remains paper-level;
- the additive-edge size obstruction: Lean checks that the exact common
  two-adic offset lies below Q, the divisibility `R | t+e`, the strict product
  bound `R*t < e^2`, and the consequence `R < 2e`. The Fermat-divisor
  congruences excluding the smallest proper lower stratum remain paper-level;
- the exact square and odd fast-doubling updates for a linear remainder
  `U+xV` under the Conway relation `x^2=A*x+A^3`, which underlie the
  paper's ancestry-filtration degeneration; the Gröbner-basis statement
  itself remains paper-level;
- the denominator-free normalization of the selected Singer cubic to
  `tau^3 + d^2*tau^2 + 1 = 0`, together with the coefficient-ancestry identity
  `s_k^3 = s_(k-1)*tau_(k-1)^2`;
- the characteristic-two semiconjugacy transporting the cubic arm's
  cyclotomic critical factor back to the actual Conway cubic;
- the denominator-free cyclic-resolvent Artin--Schreier equation and
  orientation trace-shift identity behind the exceptional arm's explicit
  terminal cubic;
- the characteristic-two Berlekamp-numerator factorization and its literal
  vanishing on the selected reciprocal cubic;
- the denominator-free characteristic-two identity that depresses every
  trace--constant Dickson cubic to an Artin--Schreier cubic;
- the four-axis reciprocal-root factorization behind the theorem that a
  trace--constant cubic with anisotropic quadratic lift lies on the smaller
  (Q^2-Q+1) Dickson torus;
- the characteristic-two algebra behind the singleton-even relative-trace
  collision: Artin--Schreier additivity, the centered ratio identity, and the
  exact fixed-field versus norm-one Mobius alternatives; and
- the open target `DPrimeTarget M`, namely `Psi_k | orderOf (M k)` for every
  level.

Lean also reduces the complete `k=2,...,6` factor products and every recorded
`ord_p(2)=2·3^k` residue screen.  Primality is proved locally through `k=4`;
the larger factors retain the paper's explicit source-assisted boundary.
These are arithmetic input checks, not a proof that the distinguished circle
element `M_k` has the required order.  The universal `D'_k` assertion remains
open, as do the finite `M_k` computations beyond the separately maintained
Python certificate.

## FIFO linking

[`Ogdoad/Fifo.lean`](Ogdoad/Fifo.lean) gives an authoritative transition system
for the reduced odd-close parity game from `experiments/linking_game.py`:

- OPEN, FIFO CLOSE, forced PASS, ko delay, mover, and the `ZMod 2` score;
- score-translation equivariance for every transition, its exact
  even/odd strategy-sheet equivalences, and the singleton-wall reconvergence
  of `C_f; O_z; O_w` with `O_z; C_f; O_w` after the next real OPEN;
- the abstract fixed-front closure recursion, including kernel-checked
  exclusion of every affine sheet-one separator at a defender root and the
  sharp sheet-zero policy showing why a designated immediate-close leaf
  cannot generally be retained;
- strict rank descent, absence of nonterminal stuck states, and preservation of
  the queue/untouched invariant;
- an explicit existential/universal finite strategy tree;
- its explicit odd-forcing dual, kernel-checked finite determinacy and
  incompatibility (`EvenWins` iff no `OddWins` counterstrategy);
- explicit membership in one fixed `OddWins` strategy tree and a
  strategy-relative minimum theorem: every zero-sheet odd counterstrategy
  contains a selected charge-one CLOSE whose translated child has a fully
  score-neutral continuation tree; more generally, an explicit score-one
  subtree translates directly to a neutral tree.  Opponent-controlled
  moves have score-neutral child trees (`TreeNeutralWins.answer_child`), and
  singleton closes in such tails have charge zero, so any complete family of
  punctured singleton tails forces the induced untouched graph to be
  Eulerian.  The writeup's scalar dual-minimum argument supplies that family
  in case `(B)`;
- an absolute-target `CloseFirstWins` strategy tree, whole-queue drain
  identities, and the dummy-free `ConditionedCloseFirstTheorem`: from every
  coherent ko-clear defender checkpoint with nonempty queue, a close-first
  attacker cannot force the score to change;
- the isolated-dummy hypothesis and exact general theorem statement;
- the queue-cut potential, including CLOSE and PASS conservation and the fact
  that no flip is possible once the untouched set is empty; and
- the exact singleton-untouched queue scan used by the terminal repair
  corridor, together with a formal winning strategy for every queue satisfying
  that scan; and
- a complete strategy proof for the edgeless base class.

`FifoLinkingTheorem` is a proposition, not an axiom or claimed theorem.  The
general isolated-dummy result remains open: the missing mathematical step is
the global causal affine-contraction/factor-extension lemma identified in
`writeups/linking_affine.tex`.  In particular, the conditioned close-first
theorem controls final parity but not score-one STOPs at intermediate attacker
checkpoints; that stronger prefix-safe normalization is false locally and its
root-level sibling coupling is still open.  The Lean development therefore
hardens the semantics and the proved reduction spine without laundering the
finite census through `k = 8` into a proof for all finite graphs.

[`Ogdoad/FifoNormalization.lean`](Ogdoad/FifoNormalization.lean) checks the
current normalization frontier rather than assuming it:

- a universal live-star vector and its graph-evaluation map, with a telescoped
  trace theorem saying that OPEN adds the current live star while CLOSE and PASS
  preserve the scalar queue-cut potential;
- list-faithful live-degree handshaking and the complete pair-response
  identities: `sum_queueCut_after_two_opens` proves that the full second-OPEN
  fan sums to `|U|` copies of the post-first-OPEN cut, its even-cardinality
  corollary is zero, and the odd-cardinality theorem adjoins the translated
  old-front CLOSE representative to obtain an odd zero aggregate;
- exclusion of a CLOSE-first terminal-score-one strategy from the
  isolated-dummy initial root for either attacker seat;
- a proof-indexed dichotomy saying that every explicit odd strategy is either
  CLOSE-first at all clear attacker nodes or contains a genuine clear-node
  deviation, and hence that every hypothetical initial odd strategy contains
  such a deviation; and
- the handshaking and balanced-front part of the least-root odd corridor:
  same-degree mates form an odd set, balance the twice-punctured front, and
  force the selected move of any odd strategy to be an OPEN while the smaller
  isolated-dummy root is even-winning; and
- the exact unpruned minimum-hot normal form.  `Hot` means that one physical
  player can force either absolute score, while `ColdAtOwnScore` means that
  both physical players can preserve the score already accumulated.  Below a
  rank-minimal hot state Lean proves every state cold at its own score and
  every legal edge score-neutral; `minHotState_is_singletonWall` then forces
  the minimum hot state to have one untouched vertex `z`, a clear front `f`,
  adjacency bit `fz = 1`, and a queue tail wholly nonadjacent to `z`.

These theorems deliberately stop before the unresolved step.  If the selected
OPEN touches the dummy at the initial empty root, the remaining real reply fan
has even cardinality and ko blocks the CLOSE term which completes every
ordinary odd-cardinality fan; neither the same-degree induction nor the local
balanced-front lemmas provide an even-winning child.  Likewise, the minimum-hot theorem
classifies primitive flexible walls but does not show that a fixed root
counterstrategy can reach one on the required sheet: its unpruned global
minimum is not the same object as the minimum dual bit in one pruned strategy
tree.  The required same-eta
corridor and global `(A)/(B')` ancestry contraction remain mathematical
obligations.

[`Ogdoad/FifoMatching.lean`](Ogdoad/FifoMatching.lean) closes the exact
subclass needed by the resolved Gold construction:

- `IsMatchingGraph` says every vertex has at most one neighbour, hence the
  board is a matching plus isolates;
- `evenWins_of_matching` gives a rank-inductive strategy from every score-zero
  state at the designated seat's turn, or at a safe opponent front;
- `evenWins_initial_of_matching` proves that either seat forces zero flip
  parity from the empty-queue root, without a dummy; and
- `evenWins_initial_of_every_submatching` formalizes the same public-branching
  induction for every edge-deleted submatching. Its move branches inspect only
  the public matching, although `EvenWins` does not expose a first-class policy,
  so the literal `exists policy, forall submatching` and per-close trace
  statements remain paper-level observations; and
- the abstract hyperbolic-plus-radical graph and induced-subgraph lemmas provide
  the matching target; the paper supplies the concrete Witt-frame and loaded-
  support instantiation.

This does **not** prove the arbitrary-graph isolated-dummy conjecture.  It
shows instead that the conjecture is an unnecessary strengthening for Gold.

## Gold normal-play semantics

[`Ogdoad/GoldMatchingAlgebra.lean`](Ogdoad/GoldMatchingAlgebra.lean)
kernel-checks the quadratic expansion in a supplied adapted basis: selected
basis diagonals plus the parity of hyperbolic pairs whose two coordinates are
active. It includes the exact split in which each adapted diagonal is a public
polar correction plus a transported original-frame linear source.
The standard existence of a symplectic-plus-radical basis for a finite
alternating form remains an ordinary linear-algebra input; the file proves the
identity once such a basis and the split-diagonal hypotheses are supplied. It
does not define the original-frame change-of-basis matrix or prove that its
concrete public correction is `P_B(f_i)`; that elementary polarization step
remains in the paper.

[`Ogdoad/GoldSemantics.lean`](Ogdoad/GoldSemantics.lean) proves the semantic
compiler independently of the FIFO mechanism:

- a recursive winning-status compiler models retaining every move and adding
  one terminal claim exactly when the current seat is designated by the charge;
- mutual backward induction proves winner equivalence at every subtree and phase, so
  stance one has a P-root exactly when the forced charge is zero;
- the Boolean complement identity behind the need for a mover/phase bit;
- outcome-dominance pruning makes mixed-successor criticality impossible in
  every two-class game; and
- the local Boolean swap identity for a two-action fork.

[`Ogdoad/GoldNoEvaluator.lean`](Ogdoad/GoldNoEvaluator.lean) proves the sharp
observation boundary. Coordinate-free, transcript stability and exactness
force the input into the span of the observed vectors. In the Boolean
coordinate frame it proves

```text
weight(x) <= number of observations * maximum observation weight
```

and rules out uniform exactness under a bounded total certificate. The paper's
weighted-source rule uses exactly the active singleton directions and attains
this support bound.

[`Ogdoad/GoldForkPadding.lean`](Ogdoad/GoldForkPadding.lean) proves generic
Bool-parameter fork padding. It replaces every terminal P-node of an arbitrary
finite normal-play tree by an outcome-equivalent forced wrapper leading to an
always-N swapping fork, and `win_padTerminals` proves the root outcome is
unchanged. The paper instantiates the Bool as a chosen refinement bit and
draws the fork-screen corollary.

These files kernel-check independent ingredients of the synthesis in
`writeups/goldarf.tex`; there is no single end-to-end Lean theorem constructing
the weighted-source arena and connecting every layer. In particular they do
not encode finite-field nim arithmetic, construct the standard Witt basis,
instantiate its concrete matrix coefficients, or build the compiled arena as a
second explicit move-graph datatype. `TranscriptStable`, `twist`, and `observe`
are abstract assumptions in Lean; their weighted-arena instantiation is also
part of the paper's synthesis.
