# C2 — Conway–Fermat relations, cyclotomic reduction, and a stronger order bound

Tags: **[S]** standard or supplied source theorem; **[D]** derived here with
proof; **[N]** named small symbolic check; **[H]** heuristic. All statements
under a tagged proposition or paragraph inherit its tag.

**[D] Main result.** The two independent functions supplied by the order-four
automorphism of the supersingular realization give

\[
 \boxed{\delta_n\ge \left\lceil\frac{2^{2n+1}}5\right\rceil
 \qquad(n\ge1).}
\]

Combining this with the Euler–Lucas congruence gives the slightly sharper
integer bound

\[
 \boxed{\delta_n\ge B_n:=
 1+2^{n+2}\left\lceil\frac{2^{n-1}}5\right\rceil
 \qquad(n\ge2).}
\]

This improves the supplied universal bound `delta_n >= 2^(n+2)+1` for
`n >= 4`. The proof is in §4. It does not prove full order.

**[D] Other conclusions.** The explicit multiplicative shadow of the
Artin–Schreier tower has only one Kummer coordinate at each Fermat prime.
A real cyclotomic-unit lift has exactly the same vanishing test as that
coordinate. In the semisimple case its reduction is a sum over relevant
characters, with explicit Euler factors and a selected prime above two.
There is always a relevant character with full prime support, so Euler
annihilation does not force failure in this family. For `n >= 2` there are
at least four relevant characters, not the single line of the arm-C
Theorem C. The exact remaining question is selected Kummer splitting,
including possible cancellation between character contributions.

**[N] Verification scope.** Read the specified overnight brief, digest,
B1 §1, B3 meta-obstruction, the live torus and Wiedemann sections, and the
supersingular/divisor and saturation propositions needed below. No web
search, sweep, or finite-field row run was performed. The small symbolic
check `ZF-divisor-symbolic` verified curve preservation by the automorphism,
its square, the divisor permutation, and determinant five. The arguments
below are paper proofs; they were not checked in Lean.

## 1. The exact relation web

**[S] Setup.** Write

\[
 a_{-1}=1,\quad a_j=\prod_{i=0}^j c_i,\quad
 c_j^2+c_j=a_{j-1},\quad
 E_j=\mathbb F_{2^{2^{j+1}}},\quad
 q_j=2^{2^j},\quad F_j=q_j+1,
 \qquad u_j=(c_j+1)/c_j.
\]

The supplied Conway tower theorem says that `c_j` has degree `2^(j+1)`,
that `c_j^q_j=c_j+1`, and that compatible root choices form one Frobenius
orbit. In particular `1 < delta_j := ord(u_j) | F_j`. The Fermat numbers
are pairwise coprime.

**Proposition 1.1 [D].** All of the following are exact identities:

\[
 \begin{aligned}
 c_j+1&=u_jc_j,& c_j&=(1+u_j)^{-1},\\
 a_{j-1}&=u_jc_j^2=\frac{u_j}{(1+u_j)^2},&
 a_j&=\frac{u_j}{(1+u_j)^3},\\
 u_j+u_j^{-1}&=a_{j-1}^{-1},&
 c_j^{F_j}&=a_{j-1},\\
 \operatorname{Tr}_{E_j/E_{j-1}}a_j&=a_{j-1},&
 N_{E_j/E_{j-1}}a_j&=a_{j-1}^3.
 \end{aligned}
\]

Consequently, for `j >= 1`,

\[
 \frac{u_j}{(1+u_j)^2}
 =\frac{u_{j-1}}{(1+u_{j-1})^3},
 \qquad
 c_{j+1}^2+c_{j+1}=c_j^3+c_j^2.
\]

*Proof.* The first line is the definition of `u_j` and its solution for
`c_j`. Substitution into `c_j(c_j+1)=a_(j-1)` gives the second line.
Adding `u_j` and its inverse gives `1/(c_j(c_j+1))`. The relative norm is
`c_j^(q_j+1)=c_j(c_j+1)=a_(j-1)`. Since `a_j=a_(j-1)c_j` and the parent
belongs to the base field, trace and norm give `a_(j-1)` and
`a_(j-1)^2 a_(j-1)`. Substituting the expression for `a_(j-1)` from the
preceding level proves the parent law. Finally
`a_j=c_j a_(j-1)=c_j(c_j^2+c_j)`. ∎

**Proposition 1.2 [D]: multiplicative parametrization.** Interpret division
by powers of two in exponents using the unique square-root automorphism of
an odd-order finite multiplicative group. Then

\[
 a_j=\prod_{i=0}^j u_i^{-3^{j-i}/2^{j-i+1}},
\]

and

\[
 c_j=u_j^{-1/2}
      \prod_{i<j}u_i^{-3^{j-1-i}/2^{j-i+1}}.
\]

*Proof.* Proposition 1.1 gives
`c_j=a_(j-1)^(1/2) u_j^(-1/2)` and hence
`a_j=a_(j-1)^(3/2) u_j^(-1/2)`. Iterate the second equality from
`a_(-1)=1`, and insert it in the first. ∎

**Proposition 1.3 [D]: precise Kummer shadow.** Fix an odd prime
`ell | F_n`, and embed a finite prefix through level `m >= n` in `E_m`.
Let `Phi` be an additive `ell`-Kummer character of `E_m^*`, and set
`s=Phi(u_n)`. Then

\[
 \Phi(u_j)=0\quad(j\ne n),\qquad
 \Phi(a_j)=
 \begin{cases}
 0,&j<n,\\
 -\dfrac{3^{j-n}}{2^{j-n+1}}s,&j\ge n,
 \end{cases}
\]

and

\[
 \Phi(c_j)=
 \begin{cases}
 0,&j<n,\\
 -s/2,&j=n,\\
 -\dfrac{3^{j-n-1}}{2^{j-n+1}}s,&j>n.
 \end{cases}
 \qquad
 \Phi(c_j+1)=\Phi(c_j)+\mathbf1_{j=n}s.
\]

*Proof.* For `j != n`, `u_j` has order dividing `F_j`, which is prime to
`ell`, so its Kummer character is zero. Apply `Phi` to Proposition 1.2.
The formula for `c_j+1` follows from `c_j+1=u_j c_j`. ∎

**[D] Scope of this conclusion.** Every multiplicative word in the displayed
coordinates and their Frobenius conjugates has Kummer value `lambda*s`.
All the displayed norm, product, and trace-to-product identities therefore
have a homogeneous one-coordinate shadow. For example,

\[
 2\Phi(c_n)+\Phi(u_n)=0,
 \qquad
 \Phi(c_n+1)=-\Phi(c_n)
\]

is also exactly the Frobenius constraint `q_n = -1 mod ell`.
These equations admit the zero phase; they do not force success.
This is a statement about these identities and their multiplicative
consequences, not a no-go theorem for every consequence of the additive
recurrence. The recurrence specifies the selected point, and another
argument using it can still constrain its order. Section 4 does so.

**Proposition 1.4 [D]: conductor bookkeeping.** With the notation of this
brief,

\[
 \operatorname{ord}(c_0)=3,\qquad
 \operatorname{ord}(c_1)=15,\qquad
 \operatorname{ord}(a_1)=5,
\]

and, for `n >= 2`,

\[
 \boxed{\operatorname{ord}(c_n)=\operatorname{ord}(a_n)
       =\prod_{j=1}^n\delta_j.}
\]

In particular the assertion `ord(c_n) | F_1 ... F_n` starts at `n=2`
with these indices; `c_1` is an exception.

*Proof.* The decomposition of `E_n^*` into its coprime factors of orders
`q_n-1` and `q_n+1` shows that `c_n` has top order `delta_n` and lower order
`ord(a_(n-1))`: its `F_n`th power is `a_(n-1)`, and raising to `F_n` is an
automorphism on the lower factor. Thus

\[
 \operatorname{ord}(c_n)=\delta_n\operatorname{ord}(a_{n-1}).
\]

Also `a_n=c_n^(F_n+1)`, and
`gcd(q_n^2-1,q_n+2)` divides three. The base `c_0` has order three;
`delta_1=5` because it is a nontrivial divisor of five. Hence `c_1` has
order fifteen and `a_1=c_1^6` has order five. All `F_j`, `j>=1`, are prime
to three. Induction now shows that raising `c_n` to `F_n+1` loses no order
for `n>=2`, proving the formula. ∎

## 2. A real cyclotomic lift and the selected prime

**[D] Construction.** Fix `n >= 1` and put `N=ord(c_n)`,
`M=Q(zeta_N)`, `K=M^+`. Choose a prime `P | 2` and residue identification
with `red_P(zeta_N)=c_n`. Put `Pplus=P cap K`. Existence follows because
the prime-to-two roots of unity of order `N` reduce to the primitive
`N`th roots in characteristic two. Set

\[
 \varepsilon=1+\zeta_N^{-1},\qquad
 \eta=\zeta_N^{1/2}+\zeta_N^{-1/2}\in O_K^\times,
\]

where half-exponents are taken modulo odd `N`. Then
`epsilon=zeta_N^(-1/2) eta`, and `eta` is a real cyclotomic unit:
`1+zeta_N=(1-zeta_N^2)/(1-zeta_N)` is a unit for odd `N>1`, and the
root-of-unity normalization is real. For the unit assertion, the ratio
is an algebraic integer, and numerator and denominator are Galois
conjugate, so its absolute norm is one.

**Proposition 2.1 [D]: the real lift has the correct phase, even when
`ell | N`.** For every `ell | F_n`,

\[
 \overline\eta^{\,4}=a_{n-1}u_n^3,
 \qquad
 \boxed{4\Phi_\ell(\overline\eta)=3\Phi_\ell(u_n).}
\]

Consequently `u_n` has full `ell`-primary order iff `eta mod Pplus` is not
an `ell`th power. No hypothesis `ell ∤ N` is required.

*Proof.* Since `bar(eta)^2=c_n u_n^2`, one has
`bar(eta)^4=c_n^2 u_n^4=a_(n-1)u_n^3`. The ancestor has order dividing
`q_n-1`, prime to `ell`. Apply the Kummer character. For `n>=1`,
`ell>=5`, so both three and four are invertible modulo `ell`. In a cyclic
group whose order has `ell`-valuation `e`, an element is an `ell`th power
iff its order has `ell`-valuation below `e`. The `ell`-part of `E_n^*`
is exactly the `ell`-part of `F_n`. ∎

**Proposition 2.2 [D]: there is no half-field CM forcing here.** For
`n>=1`, complex conjugation is not in `D=<2 mod N>`. Thus `2` splits in
`M/K` at the selected prime and `Pplus` has residue degree

\[
 h=2^{n+1}.
\]

For `n>=2`, the number of primes of `K` above two is

\[
 r=[\operatorname{Gal}(K/\mathbb Q):D]
   =\frac{\varphi(N)}{2h}\ge4.
\]

*Proof.* For `n=1`, `N=15`. The congruence `2^t=-1 mod 3` requires `t`
odd, whereas `2^t=-1 mod 5` requires `t=2 mod 4`.
For `n>=2`, Proposition 1.4 gives `5 | N` and a prime `s | delta_n`.
The latter has `ord_s(2)=h`, so `2^t=-1 mod s` requires
`t=h/2 mod h`; these `t` are divisible by four. Modulo five the same
congruence requires `t=2 mod 4`. Thus `-1` is not in `D`.

The order of two modulo `N` is `h`, because `c_n` has degree `h`.
Quotienting the cyclotomic Galois group by conjugation therefore does not
shrink the decomposition group at two, proving the residue degree and
prime count. Finally the Euler–Lucas argument gives `s=1 mod 2h`:
`s=1 mod 8` makes two a square modulo `s`, so `h | (s-1)/2`.
As `5s | N`, `phi(N)>=4(s-1)>=8h`, whence `r>=4`. ∎

**Proposition 2.3 [D]: exact selected splitting test, without
semisimplicity assumptions.** Let `L=K(mu_ell)` and choose a prime `Q`
of `L` above `Pplus`. Then

\[
 \boxed{
 v_\ell(\delta_n)<v_\ell(F_n)
 \iff Q\text{ splits completely in }
 L(\eta^{1/\ell})/L.}
\]

This includes the case of a trivial Kummer extension.

*Proof.* Since `ell | 2^h-1`, the residue field at `Pplus` contains
`mu_ell`, so `L/K` splits locally at `Pplus`. Its residue field remains
`F_(2^h)`. At residue characteristic two, adjoining an `ell`th root of a
unit is unramified, and the prime splits completely iff the residue unit
is an `ell`th power. This is the usual unramified local Kummer criterion
[S], or follows directly from Hensel lifting the `ell` distinct roots of
`X^ell-eta` when one residue root exists. Apply Proposition 2.1. ∎

**[D] The selection has not disappeared.** For a fixed `zeta_N`, the
Frobenius orbit of the selected `c_n` chooses a coset in
`(Z/N)^*/<2>`, equivalently a prime of `M` above two. Passing to `K`
forgets the inverse pair of cosets. The full tower, not only `N`, selects
this prime. One necessary non-liftable condition is

\[
 \zeta_N^{q_n}-\zeta_N-1\in P.
\]

This algebraic integer is nonzero: if `zeta^q=1+zeta` in characteristic
zero, absolute values force `Re(zeta)=-1/2`, so `zeta` has order three;
then `1+zeta` has order six and cannot be a power of an odd-order root.
Thus the Artin–Schreier condition supplies a selected prime divisor of a
nonzero algebraic integer, not a characteristic-zero unit identity.
Proposition 2.3 is an exact unit-splitting problem at that prime. Calling
it “Wieferich-type” describes the remaining selected local arithmetic;
it is not the ordinary congruence `2^(ell-1)=1 mod ell^2`.

**[D] Conductor caution.** For `n>=2`, Proposition 1.4 says
`N=delta_1 ... delta_n`, not the known upper bound `F_1 ... F_n` unless
the earlier full-order assertions hold. Substituting that upper bound
as the primitive conductor would assume part of the target. One can
instead work in the larger known cyclotomic field with a possibly
nonprimitive power of its root, but then its unknown exponent carries
the same selection problem.

## 3. Exact character and Euler-factor formulation

**[S] Standard inputs used in this section.** Dirichlet's unit theorem
gives one copy of each nontrivial even character in the cyclotomic unit
representation. Circular units have finite index in the real units.
Their generators are the normalized ratios of `1-zeta_d^a` and
`1-zeta_d`, together with the usual composite-conductor generators,
for divisors `d | N`. The distribution identity is

\[
 N_{\mathbb Q(\zeta_N)/\mathbb Q(\zeta_f)}(1-\zeta_N)
 =\prod_{s\mid N,\ s\nmid f}(1-\sigma_s^{-1})(1-\zeta_f),
\]

in additive notation for multiplicative groups tensored with the
coefficient field. The product is over rational primes. These are the
circular-unit inputs of Washington, *Introduction to Cyclotomic Fields*,
§§8.1–8.2, also used in B1. No analytic estimate is used below.

**[D] Hypotheses and notation.** Assume for this section that
`ell ∤ |G|`, where `G=Gal(K/Q)`; this is the actual semisimplicity
hypothesis. In particular it must be checked, not inferred from
`ell | F_n`. Take an unramified extension `R/Z_ell` containing all the
character values, with residue field `k`. Let

\[
 U=O_K^\times/\{\pm1\},\quad
 \rho=\Phi_\ell\circ\operatorname{red}_{P^+},\quad
 \Gamma=\{\psi\in\widehat G:\overline{\psi(\sigma_2)}=2\in k\}.
\]

Characters in `Gamma` are even characters modulo `N`. Their value at two
has exact order `h`, and is the Teichmüller lift of `2 mod ell`.
Merely having order `h` is not enough: the displayed reduction condition
selects the matching eigenvalue.

**Proposition 3.1 [D]: the exact character formula.** With `e_psi` the
integral idempotents,

\[
 \boxed{\frac34\Phi_\ell(u_n)
 =\rho(\eta)=\sum_{\psi\in\Gamma}\rho(e_\psi\eta).}
\]

There are exactly `r=phi(N)/(2h)` characters in `Gamma`.
For a character of conductor `f`, put

\[
 E_\psi(N)=\prod_{s\mid N,\ s\nmid f}(1-\psi(s)^{-1}),
 \qquad d_f=[\mathbb Q(\zeta_N):\mathbb Q(\zeta_f)].
\]

In additive unit notation, modulo torsion,

\[
 \boxed{
 e_\psi\eta_N
 =\frac{\psi(2)-1}{d_f}\,E_\psi(N)\,
       e_\psi(1-\zeta_f)
 =\frac{E_\psi(N)}{d_f}\,e_\psi\eta_f.}
\]

The first expression can be read in the multiplicative group of the
field tensored with the fraction field of `R`; its nontrivial component
is a unit component. The second expression is integral at `ell`.

*Proof.* Reduction satisfies `rho(sigma_2 v)=2 rho(v)`. On the
`psi`-component this gives
`(bar(psi(2))-2)rho(e_psi v)=0`; all other components vanish. Proposition
2.1 gives the factor `3/4`. Restriction of characters to the cyclic
subgroup `D`, of order `h`, has exactly `|G|/h` extensions for any one
character of `D`, proving the count.

Modulo roots of unity,
`[eta_N]=(sigma_2-1)[1-zeta_N]`. Project the distribution identity to
`psi`. Norm on the inflated `psi`-line multiplies by `d_f`, whereas the
Euler operators act by the scalars `1-psi(s)^(-1)`. This proves the first
formula. Apply the same `(sigma_2-1)` identity at conductor `f` to get
the second. Since `d_f | |G|`, its denominator is an `ell`-adic unit.
Also `psi(2)-1` is a unit, reducing to one. ∎

**[D] Normalization matters.** The factor `1/d_f` comes from normalized
idempotents. It does not change whether an individual component is
Euler-killed, but it cannot be discarded in a sum whose terms may cancel.

In this semisimple setting, an Euler factor is either exactly zero or
an `ell`-adic unit: character values have order prime to `ell`, and their
reduction is injective on those roots of unity. Thus a nontrivial value
of `psi(s)` cannot reduce to one.

**Proposition 3.2 [D]: unit-index form of the criterion.** Let `C` denote
the real circular-unit lattice. For `psi in Gamma`, the line `C_psi` is
generated over `R` by `e_psi eta_f`. Choose an `R`-basis `b_psi` of
`U_psi`, and write

\[
 e_\psi\eta_f=I_\psi b_\psi,\qquad
 R_\psi=\rho(b_\psi)\in k.
\]

Then

\[
 \boxed{
 \frac34\Phi_\ell(u_n)=
 \sum_{\psi\in\Gamma}
 \overline{d_f^{-1}E_\psi(N)I_\psi}\ R_\psi.}
\]

Here `I_psi` is the characterwise circular-unit index coefficient:
`U_psi/C_psi = R/(I_psi)`. Its divisibility by `ell` is independent of
the chosen basis. The factors `R_psi` are selected reduction values.

*Proof.* The unit theorem gives a free rank-one `R`-lattice in each
nontrivial character, and all characters in `Gamma` are nontrivial.
For the circular-unit assertion, a generator of conductor `d` contributes
only if `f | d`. In that case the distribution identity expresses its
projection as an integral multiple of `e_psi(1-zeta_f)`; all relative
degree denominators are units. Normalized ratios insert factors
`psi(a)-1`. Because `psi(2)-1` is a unit, their span is generated by
`e_psi eta_f`, which is itself a circular unit embedded from `K_f`.
Thus the stated generator and index description hold. Substitute this
description into Proposition 3.1. ∎

**[D] Why this is not arm C's two-alternative theorem.** When `D=G`, only
one character survives, and a product of a unit-index coefficient with a
reduction value is zero exactly when one of those factors is zero. Here
`n>=2` gives at least four characters. Individual terms may vanish by
Euler factors, unit-index divisibility, or reduction; distinct nonzero
terms may also cancel at the selected prime. Even proving every relevant
unit index prime to `ell` does not turn failure into complete splitting
of the extension generated by all units.

More explicitly, at conjugate primes the selected sum takes the form

\[
 \rho(\sigma_a\eta)
  =\sum_{\psi\in\Gamma}\overline{\psi(a)}
       \overline{d_f^{-1}E_\psi(N)I_\psi}\ R_\psi.
\]

These are the character evaluations on the cosets `G/D`; a factor from
`D` multiplies the whole value by a nonzero power of two. Thus vanishing
is well-defined on a prime coset. It is an individual Fourier evaluation,
not the simultaneous vanishing of all its Fourier coefficients.

**Proposition 3.3 [D]: a full-support relevant character always exists.**
For every actual Conway conductor `N=ord(c_n)`, `n>=1`, there is an even
character `psi` with `psi(2)` of order `h=2^(n+1)` whose conductor is
divisible by every prime dividing `N`. In the semisimple setting it can
be chosen in `Gamma`. Therefore at least one relevant Euler factor
`E_psi(N)` is the empty product one.

*Proof.* For `n=1`, `N=15`; use the odd nontrivial character modulo three
and an odd quartic character modulo five. Their product is even and
takes a primitive fourth-root value at two.

For `n>=2`, choose a prime `s | delta_n`. On the factor modulo five
choose an odd quartic character, taking a value `i` at two. Prescribe
the desired primitive `h`th root `omega` as the total value at two.
On the factor modulo `s`, choose a character taking `omega/i` at two;
this exists because the character of the subgroup generated by two
extends to the cyclic group `(Z/s)^*`. Since `h>=8`, `omega/i` still has
order `h`. This character is odd, because `-1=2^(h/2) mod s`.

Every other prime `t | N` lies in some `F_j`, `j>=2`. Use its nontrivial
quadratic character. It is even and takes the value one at two, since
`t=1 mod 8`. Inflate all these local characters to the prime powers in
`N` and take their product. Exactly two chosen local characters are odd;
the result is even, has value `omega` at two, and is nontrivial on every
local factor. Its conductor therefore contains every prime dividing
`N`. In the semisimple case choose `omega` to be the Teichmüller lift
of `2 mod ell`. ∎

**[D] Consequence and limitation.** Thus the uniform Euler-killing
mechanism from B1 cannot prove failure for the Conway–Fermat conductors.
It also does not prove success: the surviving character may have an
index or local reduction obstruction, and several surviving characters
can cancel. If `ell | |G|`, integral idempotents are unavailable and
Propositions 3.1–3.2 must not be used; Proposition 2.3 remains valid.
No infinite family with `delta_n=F_n` follows from these arguments.
If `F_n` is prime, full order follows immediately from `delta_n>1`;
this does not establish an infinite family of such indices.

## 4. A quadratic-in-degree lower bound from two elliptic units

**Theorem 4.1 [D].** For every `n>=1`,

\[
 \delta_n\ge\left\lceil\frac{2^{2n+1}}5\right\rceil.
\]

*Proof.* Work on the curve

\[
 \mathcal E:\ y^2+y=x^3+x^2
\]

and put

\[
 P=(c_{n-1},c_n),\qquad
 d=[\mathbb F_2(P):\mathbb F_2]=2^{n+1},
 \qquad g=(y+1)/y.
\]

Proposition 1.1 puts `P` on the curve. The degree follows from the degree
of `c_n` and the containment of `c_(n-1)` in `E_n`.

Define

\[
 \iota(x,y)=(x+1,y+x+1),\qquad v=g\circ\iota.
\]

Direct substitution preserves the curve, and
`iota^2(x,y)=(x,y+1)=-P`. Let `Q=2^(2^(n-1))` and let `tau` raise
coordinates to their `Q`th powers. It sends `x=c_(n-1)` to `x+1`.
Since

\[
 (x+1)^3+(x+1)^2=(x^3+x^2)+(x^2+x),
\]

the two possibilities for `tau(y)` are `y+x` and `y+x+1`.
Therefore `tau(P)` is either `iota(P)` or `-iota(P)`. As
`g(-R)=g(R)^(-1)`,

\[
 g(P)=u_n,\qquad v(P)=u_n^{Q}\ \text{or}\ u_n^{-Q}.
\]

Both values belong to the cyclic group generated by `u_n`.

Now label the rational points

\[
 A=(0,0),\quad B=(0,1),\quad C=(1,0),\quad D=(1,1).
\]

The horizontal-line intersections give

\[
 \operatorname{div}(y)=2[A]+[C]-3[O],\qquad
 \operatorname{div}(y+1)=2[B]+[D]-3[O].
\]

For example, along `y=0`, the right-hand side is `x^2(x+1)`, giving
intersection multiplicities two and one; the pole order is three.
The automorphism permutes the four points as
`A -> D -> B -> C -> A`. Thus

\[
 \operatorname{div}(g)=-2[A]+2[B]-[C]+[D],
 \qquad
 \operatorname{div}(v)=[A]-[B]-2[C]+2[D].
\]

For integers `a,b`, the divisor of `g^a v^b` has coefficients

\[
 (-2a+b,\ 2a-b,\ -a-2b,\ a+2b).
\]

Consequently its pole degree is exactly

\[
 H(a,b)=|2a-b|+|a+2b|.
\]

The coefficient matrix has determinant five, so every nonzero `(a,b)`
gives a nonconstant function. Define the relation lattice

\[
 \Lambda=\{(a,b)\in\mathbb Z^2:g(P)^a v(P)^b=1\}.
\]

Its index in `Z^2` is `delta_n`: the map has image exactly `<u_n>`,
since its first generator maps to `u_n` and its second lies in that group.

For a nonzero `(a,b) in Lambda`, the nonzero rational function
`g^a v^b-1`, defined over `F_2`, vanishes at the degree-`d` closed point
`P`. Its pole degree is `H(a,b)`. Equality of zero and pole degrees
therefore gives

\[
 H(a,b)\ge d \qquad (0\ne(a,b)\in\Lambda).                 \tag{*}
\]

The real convex body `H(a,b)<R` has area `2R^2/5`: under the matrix
`(a,b) -> (2a-b,a+2b)`, of determinant five, it becomes the diamond
`|s|+|t|<R`, of area `2R^2`.

By the two-dimensional Minkowski convex-body theorem [S], a symmetric
convex body of area greater than four times the covolume of `Lambda`
contains a nonzero lattice point. If `delta_n<d^2/10`, choose `R<d`
sufficiently close to `d` that `2R^2/5>4 delta_n`. Minkowski produces a
nonzero lattice point with `H<R<d`, contradicting `(*)`. Hence

\[
 \delta_n\ge d^2/10=2^{2n+1}/5.
\]

Taking the ceiling proves the theorem. ∎

**Corollary 4.2 [D]: integer and defect bounds.** For `n>=2`,

\[
 \delta_n\ge B_n=
 1+2^{n+2}\left\lceil\frac{2^{n-1}}5\right\rceil.
\]

If a prime `ell | F_n` is missing at full valuation, then

\[
 \boxed{\ell\le\left\lfloor\frac{F_n}{B_n}\right\rfloor.}
\]

*Proof.* Every prime dividing `F_n` is `1 mod 2^(n+2)`, by the
Euler–Lucas argument in Proposition 2.2. Hence `delta_n=1+k 2^(n+2)`.
Theorem 4.1 gives
`k >= 2^(n-1)/5 - 2^(-n-2)`. Because the nonzero fractional part of
`2^(n-1)/5` is at least `1/5`, rounding gives
`k >= ceil(2^(n-1)/5)`. If `ell` is missing at full valuation, it divides
the integer `F_n/delta_n`, so `ell <= F_n/delta_n <= F_n/B_n`. ∎

**[D] Why the earlier saturation boundary permits this improvement.**
The functions `g` and `v` are multiplicatively independent as functions
but have values in one cyclic group at the selected point. Their
Kummer classes at that point remain scalar multiples of one phase.
The lower bound uses the cost, in pole degree, of an exact multiplicative
relation, not an independent Kummer detector. Thus it is consistent with
the fixed-five-torsion rank-one proposition in the live paper.

**[D] Even multipliers do not give an unbounded new family by themselves.**
On this curve `pi=iota-[1]`, `iota^2=[-1]`, and
`[2]=iota pi^2`. Since the maps and functions are defined over `F_2`,

\[
 g\circ[2^t k]=(g\circ\iota^t\circ[k])^{4^t}.
\]

Also `g circ iota^2=g^(-1)` and `g circ iota^3=v^(-1)`.
Thus the powers-of-two multiples of a fixed odd multiplier supply only
the two function directions `g circ[k]` and `v circ[k]`, up to powers
and inversion. For `k=1` these are precisely the two directions exploited
above. The formula follows by iterating `[2]=iota pi^2`, commuting the
endomorphisms, and using `f circ pi^(2t)=f^(4^t)` for an `F_2`-rational
function `f`.

**[H] Remaining route.** To get substantially beyond a fixed quadratic
power of the degree using this packing method, one needs a growing
collection of independent low-degree functions whose selected values
are provably in `<u_n>`, or a stronger ancestry-sensitive separation
argument. The two-direction construction does not establish that such
a collection is impossible. Full order would still require control of
each selected `ell`-Kummer value, which none of §§1–4 evaluates.

