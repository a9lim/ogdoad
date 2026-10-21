# B4 — Moore flags, their duality, and the limit of a span-only obstruction

[D] Author: the Codex seat, in a one-hop research consult. This note uses
`CONTEXT.md`, `DIGEST.md`, and `B3-armC.md`, read in full, and the live
half-angle discussion in `writeups/excess.tex`, lines 2338–2440. Tags:
[S] standard; [D] derived here with proof; [N] exact named computation;
[H] interpretation or an unproved proposal. No universal arm-C conclusion is
claimed, and no Lean formalization is supplied.

## 1. Findings

- **[D] The actual cubic fixtures are structured.** With `n=3^k`,
  `s=3^(k-1)`, and `r=2s`, the orbit span has dimension `r`,
  `Delta_r=1`, and `Delta_d=0` for `d>r`. More strongly,
  
  ```text
  Delta_(r-d) = Delta_d^(2^(r-2d))       (0 <= d <= s).
  ```
  Here `Delta_0=1`. This is a complementary-minor identity, proved below
  from an exact symplectic trace-pairing calculation.
- **[D, N] At `k=2`, this explains every determinant ratio.** The ratios
  at `(m,l)=(27,73)`, for `d=1,...,6`, are
  `1,40,62,14,16,0`. The first three have explicit cyclotomic formulas;
  the last three follow from duality and the full-space product. At `k=1`,
  they are `1,0` at `(m,l)=(9,7)`.
- **[D, N] A genuinely characteristic-two relation is present.** Let `A_d`
  be the product of the natural characteristic-zero lifts of all nonzero
  binary linear forms on the first `d` conjugates at conductor 27. Then
  `red(A_4)=red(A_2)^4`, but
  `Norm(A_2)=1` and `Norm(A_4)=3^10*109`. Thus that equality does not hold
  for these lifts in characteristic zero. Its Kummer equation is still
  homogeneous and does not force `L(gamma)` to be nonzero.
- **[D] The suggested all-linear-forms no-go is too broad.** The nonzero
  elements of the orbit span generate the entire multiplicative group.
  Consequently some binary linear form has nonzero Kummer value for every
  nontrivial Kummer character. Factoring a determinant into linear forms
  does not show that those forms have liftable cyclotomic-unit evaluations.
- **[D] A narrower no-go is available.** Whole-span invariants, the full
  subspace polynomial, and Frobenius-stable unweighted products erase the
  marking. At `n=81,l=2593`, the same trace-zero space contains both
  `l`-th powers and non-`l`-th powers, all with the same Frobenius span and
  minimal additive polynomial. This is proved by a difference-set count;
  no selected row at `k=4` was evaluated.
- **[H] Verdict.** The requested small tests do not close the general partial
  flag route. They expose substantial duality, and they close these particular
  small flags as independent nonvanishing certificates. For `k>=3`, the
  determinants `Delta_4,...,Delta_s` are not evaluated by the arguments here.
  A new arithmetic input would still be needed to obtain nonvanishing from
  them. Arm C remains open.

## 2. Computation and complete ratio tables

[D] Write

```text
m odd, 2 primitive modulo m, n=phi(m)/2, q=2^n,
zeta = X in F_2[X]/Phi_m(X), gamma=zeta+zeta^(-1),
Delta_d=det(gamma^(2^(i+j)))_(0<=i,j<d).
```

[D] For a prime `l` with `ord_l(2)=n`, put `e=(q-1)/l`. If
`b=gamma^e != 1`, the ratio `R_d=L(Delta_d)/L(gamma)` is the unique exponent
modulo `l` satisfying `Delta_d^e=b^R_d`. This avoids choosing a global
primitive generator or a normalization of `L`. A zero determinant has no
Kummer logarithm; it must not be reported as ratio zero. A ratio zero in the
table means a **nonzero** determinant with trivial Kummer class.

[N] `/tmp/ogdoad_b4_moore.py` evaluates exactly the eleven requested fixtures
below, using binary polynomial arithmetic and baby-step/giant-step only in
the order-`l` subgroup. It checks the selected root's order, the subfield
membership of `gamma`, Gaussian-elimination determinants through size 6,
independent subspace products when the rank is at most 10, the determinant
recurrence of Section 3, the prime and cubic dualities of Section 4, and the
`Delta_2` formulas of Section 5. The output is
`/tmp/ogdoad_b4_moore.json`. The scripts and an output snapshot are embedded
below so that the note remains reproducible without the temporary files.
The original fixture run took 0.066 seconds; the expanded assertion run also
completed in under a second. No row census or counterexample sweep was run.

[N] The lists below give **all** `R_1,...,R_r`, where `r` is the rank of the
Frobenius span. In every fixture `Delta_r=1`, and `Delta_(r+1)=0`. All listed
primitive Kummer denominators `L(gamma)` were nonzero. There is no prime with
`ord_l(2)=6`, so conductor 13 has no requested Kummer ratio.

| `m` | `n` | `r` | `l` | `R_1,...,R_r` |
|---:|---:|---:|---:|---|
| 5 | 2 | 2 | 3 | `1,0` |
| 9 | 3 | 2 | 7 | `1,0` |
| 11 | 5 | 5 | 31 | `1,23,15,8,0` |
| 13 | 6 | 6 | — | no primitive prime divisor |
| 19 | 9 | 9 | 73 | `1,48,43,27,54,52,3,55,0` |
| 25 | 10 | 8 | 11 | `1,7,6,4,6,0,9,0` |
| 27 | 9 | 6 | 73 | `1,40,62,14,16,0` |
| 29 | 14 | 14 | 43 | `1,41,31,3,5,36,23,15,37,20,24,16,11,0` |
| 37 | 18 | 18 | 19 | `1,8,13,10,4,9,1,18,7,15,16,6,17,18,10,10,5,0` |
| 53 | 26 | 26 | 2731 | `1,1361,1351,453,2251,1483,343,1798,2439,1156,1212,2593,1509,2179,275,247,1716,458,1194,2496,1109,1890,1856,2304,683,0` |
| 59 | 29 | 29 | 233 | `1,196,55,16,26,38,190,145,143,39,69,86,226,222,211,177,189,211,163,216,6,160,128,56,102,121,187,175,0` |
| 59 | 29 | 29 | 1103 | `1,178,249,1017,169,311,342,1002,417,219,344,1050,161,898,693,185,510,1015,725,294,961,176,924,682,870,159,149,276,0` |
| 59 | 29 | 29 | 2089 | `1,946,698,1259,939,1862,1920,1306,1148,860,1149,764,427,738,1476,1327,1469,842,1630,979,983,147,283,158,111,729,1887,1567,0` |

[H] These data do not support describing the ratios simply as random: every
prime-conductor list has the duality below, and every `R_2` has a cyclotomic
formula. Some interior ratios vary with conductor and prime. A handful of
residues cannot establish randomness or rule out an exact formula. Moreover,
being a power of two is a weak test when `<2>` is large; modulo 19, every
nonzero residue is a power of two.

## 3. What a Moore determinant measures

### 3.1 Product identity and the additive recurrence

[D] For independent `x_0,...,x_(d-1)` over `F_2`, let `V` be their span. Then

```text
det(x_j^(2^i))_(i,j<d) = product_(0 != v in V) v.
```

[D] Proof. Regard both sides as polynomials in indeterminates `x_j` over
`F_2`. The determinant vanishes on each nonzero binary linear hyperplane,
because its columns become dependent there. Every such linear form therefore
divides it. There are `2^d-1` forms, their product has the determinant's
homogeneous degree, and comparison of the monomial
`x_0*x_1^2*...*x_(d-1)^(2^(d-1))` gives constant factor 1. Specialization
proves the identity, including vanishing for dependent tuples.

[D] Let `P_V(T)=product_(v in V)(T+v)`. Its coefficient of `T` is the
product above. If `a` extends `V`, the two cosets give

```text
P_(V+<a>)(T) = P_V(T)^2 + P_V(a)*P_V(T).
```

[D] This proves the linearized-polynomial recurrence used in the script.
It does **not** evaluate the individual factors `P_V(a)` in the Kummer
quotient. The product identity concerns the `2^d-1` points of the particular
subspace `V`; it is not automatically one of B3 Theorem 3.4's products over
an entire multiplicative coset satisfying an absolute trace condition.

### 3.2 Consecutive-flag recurrence

[D] For any `x` in a field of characteristic two, set
`Delta_d(x)=det(x^(2^(i+j)))`, `Delta_0(x)=1`. Then

```text
Delta_(d+1) * Delta_(d-1)^4 = Delta_d^4 * (Delta_d+1).       (3.1)
```

[D] Proof. Apply the Desnanot–Jacobi determinant identity to the
`(d+1)`-square Hankel matrix. The central minor is `Delta_(d-1)^4`; the two
principal `d`-minors are `Delta_d` and `Delta_d^4`; the two off-diagonal
minors are both `Delta_d^2`. In characteristic two their difference is a
sum, giving (3.1). This is a polynomial identity, so no nonsingularity
hypothesis is necessary.

[D] Whenever all terms to which a logarithm is applied are nonzero, its
Kummer form is

```text
L(Delta_(d+1)) + 4 L(Delta_(d-1))
    = 4 L(Delta_d) + L(Delta_d+1).
```

[D] Thus it introduces the new additive translate `Delta_d+1`. Treating
this translate's logarithm as known would silently supply the missing
arithmetic input.

## 4. Exact rank and complementary-minor duality

### 4.1 Cubic orbit span

[D] Put `n=3^k`, `s=3^(k-1)`, `Q=2^s`, `E=F_(Q^3)`, and
`W=ker Tr_(E/F_Q)`. Let `F` denote the squaring operator. Then

```text
span_F2{gamma,F gamma,...} = W,
dim_F2 W = r=2s,
P_W(T)=T^(Q^2)+T^Q+T,
Delta_r=1,       Delta_d=0 for d>r.                         (4.1)
```

[D] Proof. B3's cubic relative-trace identity places `gamma` in `W` and
annihilates it by `F^(2s)+F^s+1=Phi_(3^k)(F)`. This polynomial in the
operator variable is irreducible over `F_2`: the order of 2 modulo `3^k`
is `2s`, which is its degree. The nonzero vector `gamma` therefore has
minimal operator polynomial exactly `Phi_(3^k)`, and its orbit span has
dimension `2s`. The relative trace kernel has that same dimension, so they
coincide. The displayed monic separable trace polynomial has precisely `W`
as its roots. Its linear coefficient is 1; Section 3.1 gives the determinant
claims. The same argument shows that **every nonzero element of `W` has
this same full Frobenius span**.

### 4.2 The cubic trace Gram matrix

[D] Let `e_i=gamma^(2^i)` for `0<=i<r`, and let

```text
J = [ 0  I_s ] .
    [ I_s  0 ]
```

[D] Their absolute trace Gram matrix is exactly `J`:

```text
Tr_(E/F2)(e_i*e_j) = 1 if |i-j|=s, and 0 otherwise.          (4.2)
```

[D] Proof. Write `gamma_a=zeta^a+zeta^(-a)`, with
`m=3^(k+1)`. Since `±2^i`, `0<=i<n`, enumerate the units modulo `m`,

```text
Tr(gamma_a) = sum_(u in (Z/m)^*) zeta^(a*u)
           = 1_(m|a) + 1_(3^k|a)          in F_2.
```

[D] The last equality follows by subtracting from the sum over all
residues modulo `m` the sum over multiples of 3, then using the geometric
sum identity. Also `gamma_a*gamma_b=gamma_(a+b)+gamma_(a-b)`. For
`0<|i-j|<2s`, divisibility of `2^i±2^j` by `3^k` occurs exactly when
`|i-j|=s`. In that case `v_3(2^s+1)=k`, so it is not divisible by `m`.
The diagonal trace is zero. This proves (4.2).

### 4.3 The symplectic Moore matrix and its minors

[D] Let `H=(gamma^(2^(i+j)))_(0<=i,j<r)`. Then

```text
H^t J H = J,       H^(-1)=J H J,       det H=1.              (4.3)
```

[D] Proof. To compute the absolute trace Gram matrix of the `e_j`, stack
all `n=3s` Frobenius rows. The first `2s` rows are `H`; the remaining `s`
rows are the sum of its first and second blocks of `s` rows, by the relative
trace relation. If `B=[I_s I_s]`, the stacked matrix is `[H; BH]` and its
Gram matrix is

```text
H^t (I_r+B^t B) H = H^t J H.
```

[D] Equation (4.2) identifies this with `J`. The matrix `H` is symmetric,
so the inverse formula follows. The determinant is already 1 by (4.1)
(or by taking determinants in (4.3) in characteristic two).

**Theorem 4.4 [D].** For `0<=d<=s`,

```text
Delta_(2s-d) = Delta_d^(2^(2s-2d)).                         (4.4)
```

[D] Proof. Jacobi's complementary-minor identity expresses the leading
`(r-d)`-minor of `H` as `det(H)` times the trailing `d`-minor of `H^(-1)`.
By (4.3), the latter is the minor of `H` on indices
`s-d,...,s-1`. Its entries are the entries of the leading `d`-minor raised
to `2^(2(s-d))`. The determinant commutes with Frobenius. This gives (4.4),
including `d=0` with the empty-minor convention.

[D] In particular, at `r=6`, `Delta_5=gamma^16` and
`Delta_4=Delta_2^4`. Thus the entire flag is controlled by
`gamma,Delta_2,Delta_3,1`. At a general level the duality leaves
`Delta_1,...,Delta_s` to evaluate; it does not make all flags trivial.

### 4.4 Prime-conductor analogue

**Theorem 4.5 [D].** Suppose `m` is prime and 2 is primitive modulo `m`,
and put `n=(m-1)/2`. Then the conjugates of `gamma` are a self-dual normal
basis, `Delta_n=1`, and

```text
Delta_(n-d) = Delta_d^(2^(n-2d))       (0<=d<=floor(n/2)).    (4.5)
```

[D] Proof. In this case `Tr(gamma_a)=1` for `a!=0 mod m` and is zero for
`a=0`. The product formula for the `gamma_a` consequently gives trace Gram
matrix `I_n` for the `n` conjugates. For the full symmetric Moore matrix
`H_n`, this says `H_n^t H_n=I_n`, hence `H_n^(-1)=H_n`. Its determinant is
1. Complementary minors give exponent `2^(2(n-d))`, which on `F_(2^n)` is
the same Frobenius as exponent `2^(n-2d)` in the stated range.

[D] This accounts for the reflected halves of all prime-conductor ratio
lists, including their penultimate ratio `2^(n-2)=1/4 mod l`.

## 5. The first three determinants in the cubic tower

[D] In this section `L:E^* -> F_l` is any nonzero homomorphism and
`ord_l(2)=n`. No assertion below divides by `L(gamma)`; the formulas
therefore remain valid under the putative failure `L(gamma)=0`. Every
nonzero proper-subfield element has Kummer logarithm zero.

### 5.1 `Delta_2`

[D] Directly,

```text
Delta_2 = gamma^4*(gamma+1).
```

[D] The cubic relation `gamma*(gamma+1)^2=gamma_(k-1)` gives

```text
L(Delta_2) = (7/2)*L(gamma).                               (5.1)
```

[D] This explains `R_2=0 mod 7` and `R_2=40 mod 73`. It is the already
known cubic relation, not independent evidence for nonvanishing.

[D] For the other tested conductors, where 3 is coprime to `m`, choose
`j` with `2^j=±3/2 mod m`. The identity

```text
gamma_a+gamma_b = gamma_((a+b)/2)*gamma_((a-b)/2)
```

[D] holds even in characteristic zero for the natural root-of-unity
lifts. Hence `L(Delta_2)=(7/2+2^j)*L(gamma)` in these analogues. When 3
divides the cubic conductor, the `gamma_(3/2)` factor instead belongs to the
proper subfield and its Kummer value vanishes. This explains why the
analogue `R_2` values need not be the same rational constant.

### 5.2 `Delta_3`

[D] Suppose `k>=2`; choose `j_k` with `2^(j_k)=±5/2 mod 3^(k+1)`. Then

```text
L(Delta_3) = (19/2+2^(j_k))*L(gamma).                        (5.2)
```

[D] Proof. Factor the Moore determinant into the seven nonzero linear
forms on `gamma,gamma^2,gamma^4`. The three singletons contribute `7L(gamma)`.
The pairs `(0,1)`, `(1,2)`, and `(0,2)` contribute respectively
`(1/2)L(gamma)`, `L(gamma)`, and `2^(j_k)L(gamma)`, by the preceding
cyclotomic product identity. Finally,

```text
gamma+gamma^2+gamma^4 = gamma*(gamma_(k-1)+1).
```

[D] For `k>=2`, the second factor is nonzero and lies in the proper
subfield. The triple contributes `L(gamma)`. Summing gives (5.2). For
`k=1` the triple is zero and `Delta_3=0`, so its logarithm is undefined.

[N] At `m=27`, `5/2=16=2^4 mod 27`. Thus `(19/2+16)=62 mod 73`.
Together with (4.4) and (5.1), this gives

```text
R_1=1, R_2=40, R_3=62, R_4=4*40=14, R_5=16, R_6=0.
```

[D] Although a natural characteristic-zero lift of the triple sum need
not be a unit, its factorization also lifts: with `t=xi+xi^(-1)` and
`t_prev=xi^3+xi^(-3)`,

```text
t + sigma_2(t) + sigma_2^2(t) = t*(t_prev+1).
```

[D] The right second factor belongs to the lower field. It supplies no
independent primitive Kummer coordinate. Unit status and existence of a
characteristic-zero factorization must not be conflated.

## 6. A precise non-liftable relation, and why it still does not prove C

[D] At conductor 27 let `t=xi+xi^(-1)` in the real cyclotomic field, with

```text
P(t)=0,  P(X)=X^9-9X^7+27X^5-30X^3+9X+1,
t_i=sigma_2^i(t),
A_d=product_(0!=a in F_2^d) (sum_(i<d) a_i*t_i).
```

[D] The reduction of `A_d` is `Delta_d`. This is a **specified natural
lift**, not an assertion that no other characteristic-zero element could
have the same residue.

[N] `/tmp/ogdoad_b4_lifts.py`, using the already installed SymPy 1.14.0,
computes exact resultants and remainder polynomials in this degree-nine
field. Its output `/tmp/ogdoad_b4_lifts.json` includes

```text
Norm(t_0+t_1+t_2+t_3) = -109,
Norm(A_1) = -1,
Norm(A_2) = 1,
Norm(A_3) = -27,
Norm(A_4) = 6436341 = 3^10 * 109.
```

[N] It also checks that `A_4-A_2^4` is nonzero but has all even coefficients
in the power basis; its exact remainder is

```text
-1800 X^8 -3552 X^7 +9282 X^6 +18428 X^5 -12736 X^4
-25640 X^3 +4238 X^2 +8918 X +942.
```

[D] Thus the modular identity `Delta_4=Delta_2^4` fails for these natural
characteristic-zero lifts. The four-term linear form is not a unit, and is
not even a unit after inverting 3, since its norm is `-109`. The claim
“linear forms, hence cyclotomic units” is therefore false. The calculation
also shows why B3's coset-product theorem cannot simply be applied to each
factor of a partial flag.

[D, N] Nevertheless, if `w=gamma+gamma^2+gamma^4+gamma^8` at conductor 27,
then `w*gamma_1=gamma^4`, so its Kummer ratio is exactly 4 modulo 73. To
check the identity algebraically, the difference

```text
(X+X^2+X^4+X^8)*(X^3+X) + X^4
    = X^2*(X^9+X^7+X^5+X+1)
```

[D] vanishes at `gamma`. The rightmost polynomial is its degree-nine
minimal polynomial in characteristic two. Thus even this naturally
nonunit lift has a residue with an explicit homogeneous phase evaluation.
This is a fixed-conductor identity, not an evaluation of such forms at all
levels.

[D] Its general version makes the exceptional simplification explicit:
for `k>=2`,

```text
(gamma+gamma^2+gamma^4+gamma^8)*gamma_(k-1)
    = gamma^4 + gamma^2*(gamma_(k-2)+1).
```

[D] Indeed, the degree-nine polynomial in the preceding display is
`g(g(X))+1` for `g(X)=X^3+X`. At `k=2` its value is zero because
`gamma_0=1`; at higher levels the extra lower-field translate remains.

[D] The new multiplicative identity has Kummer equation
`L(Delta_4)=4L(Delta_2)=14L(gamma)` at this fixture, valid without any
nonvanishing premise. It is compatible with all these logarithms being
zero. More generally, (4.4) pairs unknown flag coordinates; it does not
provide an independently nonzero right-hand side. Non-liftability is a
necessary escape from B3's particular lift obstruction, but is not by
itself a nonvanishing argument.

[D] The absolute claim that a residue has “no cyclotomic-unit lift” would
be much stronger and is **not** proved here. At the certified fixture where
`gamma` is primitive, every nonzero residue is some power of `gamma`, and
hence has a cyclotomic-unit lift. The obstruction just established concerns
the specified natural lifts and identities among them, not all possible
lifts of a residue.

## 7. Exact scope of a no-go theorem

### 7.1 What whole-space products forget

**Theorem 7.1 [D].** Let `S` be a finite multiset of nonzero elements of a
finite field of characteristic two, invariant under squaring with its
multiplicities. Then `product S=1`. In particular, its Kummer logarithm is
zero for every odd-prime Kummer quotient.

[D] Proof. Squaring permutes the factors, so the product `P` satisfies
`P^2=P`; as `P!=0`, it equals 1.

[D] For the cubic orbit span, the whole subspace polynomial is already
`T^(Q^2)+T^Q+T`. Thus its nonzero Dickson coefficients are 1 and have zero
Kummer value. Full-span products, absolute Frobenius-orbit products, and
any analogous unweighted Frobenius-stable selection give this same loss of
information.

[D] A partial flag does not satisfy the hypothesis: squaring generally
moves its subspace to a different subspace. There is, however, a distinction
between **invariance** and **equivariance**. Every expression `f(x)` over
`F_2`, including a Moore flag determinant, satisfies `f(x^2)=f(x)^2`.
So “Frobenius-non-equivariant” cannot literally be required of such a
construction. The relevant possibility is a covariant evaluation of a
marked flag whose value is not fixed by Frobenius.

### 7.2 Linear forms collectively contain the full multiplicative information

**Theorem 7.2 [D].** For `W=ker Tr_(F_(Q^3)/F_Q)`,

```text
W^*/W^* = F_(Q^3)^*.
```

[D] Proof. For any `a!=0`, the two-dimensional `F_Q` spaces `W` and
`aW` intersect in dimension at least one inside a three-dimensional space.
Choose `u=a v !=0` in their intersection. Then `u,v` belong to `W^*`, and
`a=u/v`.

[D] Consequently, for every nonzero homomorphism `L:E^* -> F_l`, some
`w` in `W^*` has `L(w)!=0`; otherwise the quotient identity would make `L`
zero on all of `E^*`. Every such `w` is a binary linear form in the
Frobenius conjugates of `gamma`. Thus these linear forms **collectively**
have nonzero Kummer image without assuming `L(gamma)!=0`. A universal theorem evaluating all
of them as `L(w)=c_w L(gamma)` would prove `L(gamma)!=0` by this argument;
it would not be an innocuous no-go result.

[D] More strongly, if all `w` lay in `F_Q^*<gamma>`, the quotient identity
would imply `F_Q^*<gamma>=E^*`, precisely the required full order in the
relative multiplicative quotient. Factoring into linear forms does not
bypass that selected-order problem.

### 7.3 The same additive structure can occur at a trivial Kummer coordinate

**Theorem 7.3 [D].** At `n=81`, `Q=2^27`, `l=2593`, the space
`W=ker Tr_(F_(2^81)/F_(2^27))` contains both nonzero `l`-th powers and
non-`l`-th powers. Every one of these nonzero elements has the same
Frobenius span `W` and minimal additive polynomial `Phi_81(F)`.

[D] Proof. In the cyclic group `G=E^*/F_Q^*`, of order `Q^2+Q+1`, let
`D=W^*/F_Q^*`, of size `Q+1`. If `a` represents a nonidentity coset of
`G`, then `W` and `aW` intersect in dimension exactly one over `F_Q`.
Indeed, equality of these two planes would make `W` stable under `a`,
and hence under `F_Q(a)=E`, an impossibility for a proper nonzero plane.
It follows that every nonidentity element of `G` occurs exactly once as
`d_1/d_2`, with `d_i` in `D`. For each nontrivial complex character `chi`
of `G`, expanding the square gives

```text
|sum_(d in D) chi(d)|^2 = Q.
```

[D] Let `H=G^l`, and take `chi` of order `l`. Character orthogonality and
the preceding bound yield

```text
|D intersection H| >= (Q+1-(l-1)*sqrt(Q))/l.                (7.1)
```

[N] The fixed integer certificate in `ogdoad_b4_lifts.py` verifies that
2593 is prime, `2^81=1 mod 2593`, and `2^27=1455 mod 2593`. Thus its order
is exactly 81. It also checks `(2593-1)^2=6718464 < 2^27=134217728`.
This is an integer order/inequality check, not a selected finite-field row
run.

[D] The right-hand side of (7.1) is therefore positive. Since
`l` does not divide `Q-1`, membership of a coset in `G^l` is equivalent to
membership of any representative in `E^{*l}`. This produces a nonzero
`l`-th power in `W`. Theorem 7.2 supplies a non-`l`-th power in `W`.
The last statement follows from the irreducible-operator argument of 4.1.

[D] This proves the precise limitation: the trace-zero constraint, its
minimal additive polynomial, and its full Frobenius span cannot by
themselves decide whether a marked point is an `l`-th power. This does
**not** provide a counterexample to arm C: the element just counted is not
asserted to be the cyclotomically selected `gamma_4`. Nor does this theorem
cover the additional cyclotomic trace Gram matrix in (4.2), which is more
information than the unmarked span alone.

### 7.4 Artin–Schreier and general linearized operators

[D] On `W`, the algebra generated by Frobenius is the field
`F_2[F]/(Phi_(3^k)(F))`. Every operator `f(F)` with nonzero residue in this
field is consequently an automorphism of `W`. Moreover, the map
`f -> f(F)gamma`, with `deg f<2s`, is a vector-space isomorphism onto `W`.
This follows directly from the minimal-operator-polynomial proof in 4.1.

[D] In particular, `F+1` is invertible on `W`. The Artin–Schreier image
`gamma^2+gamma` has logarithm `(1/2)L(gamma)`, by (5.1), and its unique
preimage within `W` is another specified binary linear form in the orbit.
This particular image has a known homogeneous evaluation. General
linearized forms range over all of `W`, so that one image calculation does
not extend to a no-go theorem for all such forms. All these operators
commute with Frobenius; equivariance alone does not evaluate their Kummer
classes. The relative trace relation gives the element zero, to which no
multiplicative logarithm can be applied.

## 8. What remains

[D] The proved relations are compatible with the simultaneous vanishing
of `L(gamma)` and every explicitly evaluated flag coordinate. Full-span
invariants erase the marking; individual linear forms can have nonzero
Kummer content, but identifying and evaluating a suitable one independently
is still required. The new complementary-minor theorem reduces the number
of undetermined flags, rather than determining them all.

[D] More explicitly, put `c=2^(j_k)` as in (5.2). For `k>=3`, all relevant
minors through size 4 are nonzero, and (3.1) gives the exact first unresolved
coordinate in this approach:

```text
L(Delta_4) = (24+4c)*L(gamma) + L(Delta_3+1).
```

[D] Under a putative arm-C failure this becomes
`L(Delta_4)=L(Delta_3+1)`. The known value of `L(Delta_3)` does not determine
the value of its additive translate. At `k=2`, complementary duality
additionally evaluates this translate as `L(Delta_3+1)=-L(gamma)` modulo 73;
the higher-level duality does not supply that extra equation for `Delta_4`.

[H] An honest continuation would target a specific `Delta_d` or specified
linear form with `d>=4` at a general cubic level and prove a Kummer
nonvanishing statement independent of `L(gamma)`. Merely expressing its
logarithm as another homogeneous multiple of `L(gamma)`, or computing more
finite ratios, would not supply that missing step. The current work proves
neither arm C nor a universal obstruction to all marked additive methods.

## Appendix A — reproducible fixed-fixture script

[N] Save the following block as `ogdoad_b4_moore.py`; it uses only the
Python standard library. The 110-second alarm is a hard runtime cap.

```python
"""Fixed determinant fixtures, not a row census. Stdlib only; 110 s cap."""
import json, math, signal, time
signal.signal(signal.SIGALRM, lambda *_: (_ for _ in ()).throw(TimeoutError('110 s cap')))
signal.alarm(110)
START=time.monotonic()

def factors(n):
    out=[]; p=2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0: n//=p
        p+=1
    if n>1: out.append(n)
    return out

def order2(m):
    v=2%m; d=1
    while v!=1: v=v*2%m; d+=1
    return d

class Field:
    def __init__(self,m):
        ps=factors(m); assert len(ps)==1
        p=ps[0]; step=m//p
        self.mod=sum(1<<(j*step) for j in range(p))
        self.deg=self.mod.bit_length()-1
        assert order2(m)==self.deg
    def mul(self,a,b):
        v=0
        while b:
            if b&1: v^=a
            b>>=1; a<<=1
            if a>>self.deg: a^=self.mod
        return v
    def pow(self,a,e):
        v=1
        while e:
            if e&1: v=self.mul(v,a)
            e>>=1; a=self.mul(a,a)
        return v
    def inv(self,a):
        assert a
        return self.pow(a,(1<<self.deg)-2)
    def det(self,aa):
        a=[row[:] for row in aa]; v=1; d=len(a)
        for j in range(d):
            p=next((i for i in range(j,d) if a[i][j]),None)
            if p is None: return 0
            a[p],a[j]=a[j],a[p]
            v=self.mul(v,a[j][j]); iv=self.inv(a[j][j])
            for i in range(j+1,d):
                c=self.mul(a[i][j],iv)
                for h in range(j+1,d): a[i][h]^=self.mul(c,a[j][h])
        return v

def log_table(f,b,l):
    h=math.isqrt(l)+1; table={}; v=1
    for j in range(h): table.setdefault(v,j); v=f.mul(v,b)
    step=f.pow(b,(-h)%l)
    def log(a):
        v=a
        for i in range(h+1):
            if v in table:
                r=(i*h+table[v])%l
                assert f.pow(b,r)==a
                return r
            v=f.mul(v,step)
        raise AssertionError('not in subgroup')
    return log

def fixture(m):
    f=Field(m); n=f.deg//2; q=1<<n
    assert f.pow(2,m)==1
    for p in factors(m): assert f.pow(2,m//p)!=1
    gamma=2^f.pow(2,m-1)
    assert f.pow(gamma,q)==gamma and gamma
    orbit=[gamma]
    for i in range(2*n): orbit.append(f.mul(orbit[-1],orbit[-1]))
    # P_W(X)=sum c_j X^(2^j); Delta is its linear coefficient.
    coeff=[1]; delta=1; ds=[]
    for d in range(1,n+2):
        a=orbit[d-1]; v=0; t=a
        for c in coeff: v^=f.mul(c,t); t=f.mul(t,t)
        if not v:
            ds.append(0); break
        delta=f.mul(delta,v); ds.append(delta)
        nxt=[0]*(len(coeff)+1)
        for j,c in enumerate(coeff):
            nxt[j]^=f.mul(v,c); nxt[j+1]^=f.mul(c,c)
        coeff=nxt
    rank=len(ds)-1
    # Desnanot--Jacobi for these Hankel Moore minors.
    extended=[1]+ds
    for d in range(1,rank+1):
        assert f.mul(extended[d+1],f.pow(extended[d-1],4)) == \
               f.mul(f.pow(extended[d],4),extended[d]^1)
    if len(factors(m))==1 and factors(m)[0]==m:
        for d in range(1,n//2+1):
            assert ds[n-d-1]==f.pow(ds[d-1],1<<(n-2*d))
    if m in (9,27):
        for d in range(1,rank//2+1):
            assert ds[rank-d-1]==f.pow(ds[d-1],1<<(rank-2*d))
    for d in range(1,min(6,rank+1)+1):
        assert f.det([[orbit[i+j] for j in range(d)] for i in range(d)])==ds[d-1]
    # Independent product check for small spans.
    if rank<=10:
        span=[0]
        for a in orbit[:rank]: span += [x^a for x in span]
        assert len(set(span))==1<<rank
        prod=1
        for x in span[1:]: prod=f.mul(prod,x)
        assert prod==ds[rank-1]
    out={'m':m,'n':n,'rank':rank,'modulus_hex':hex(f.mod),
         'gamma_hex':hex(gamma),'deltas_hex':[hex(x) for x in ds],
         'primary':[]}
    for l in factors(q-1):
        if order2(l)!=n: continue
        e=(q-1)//l; b=f.pow(gamma,e)
        if b==1:
            row={'l':l,'Lgamma':'zero','ratios':None,
                 'delta_nonzero_Kummer':[x!=0 and f.pow(x,e)!=1 for x in ds]}
        else:
            lg=log_table(f,b,l)
            ratios=[None if x==0 else lg(f.pow(x,e)) for x in ds]
            row={'l':l,'Lgamma':'nonzero','ratios':ratios}
            if m not in (9,27):
                a=3*pow(2,-1,m)%m
                j=next(j for j in range(n) if pow(2,j,m) in (a,(-a)%m))
                assert ratios[1]==(7*pow(2,-1,l)+pow(2,j,l))%l
            if m in (9,27):
                assert ratios[1]==7*pow(2,-1,l)%l
                assert ds[rank-1]==1
        out['primary'].append(row)
    return out

if __name__=='__main__':
    result=[fixture(m) for m in (5,9,11,13,19,25,27,29,37,53,59)]
    print(json.dumps({'fixtures':result,'seconds':time.monotonic()-START},indent=2))
```

## Appendix B — natural-lift and difference-set certificate script

[N] Save this beside Appendix A as `ogdoad_b4_lifts.py`. It uses SymPy
1.14.0, which was already installed; no dependency installation was made.
Both scripts terminate under the same 110-second cap.

```python
"""Fixed natural-lift norm and subgroup certificates; no row evaluation."""
import json, signal, time
import sympy as s
from ogdoad_b4_moore import Field, log_table
signal.alarm(110)
start=time.monotonic(); x=s.symbols('x')
P=s.expand((x**3-3*x)**3-3*(x**3-3*x)+1)
ts=[x]
for i in range(1,4): ts.append(s.rem(ts[-1]**2-2,P,x))
# The two natural lifts of the characteristic-two complementary-minor identity.
A=[s.Integer(1)]
for d in range(1,5):
    prod=s.Integer(1)
    for mask in range(1,1<<d):
        t=sum(ts[i] for i in range(d) if mask>>i&1)
        prod=s.rem(prod*t,P,x)
    A.append(prod)
norms=[int(s.resultant(P,a,x)) for a in A[1:]]
f=Field(27); gamma=2^f.pow(2,26); orbit=[gamma]
for _ in range(3): orbit.append(f.mul(orbit[-1],orbit[-1]))
w=orbit[0]^orbit[1]^orbit[2]^orbit[3]
gamma_prev=f.pow(gamma,3)^gamma
assert f.mul(w,gamma_prev)==f.pow(gamma,4)
l=73; e=7; log=log_table(f,f.pow(gamma,e),l)
assert norms[3] % 109 == 0 and abs(norms[1])==1
# Reduce the natural lift difference coefficientwise modulo 2 in the real field.
difference=s.rem(A[4]-A[2]**4,P,x)
assert all(int(c)%2==0 for c in s.Poly(difference,x).all_coeffs())
assert difference!=0
l0=2593
assert all(l0%p for p in range(2,51))
assert pow(2,81,l0)==1 and pow(2,27,l0)!=1
assert (l0-1)**2 < 2**27
out={'sympy':s.__version__,'minimal_polynomial':str(P),
     'four_term_lift':str(sum(ts)),
     'four_term_norm':int(s.resultant(P,sum(ts),x)),
     'natural_product_lift_norms_d1_to_4':norms,
     'A4_minus_A2pow4':str(difference),
     'four_term_kummer_ratio_mod73':log(f.pow(w,e)),
     'four_term_identity':'w * gamma_1 = gamma^4',
     'order_certificate':{'l':l0,'2pow81':pow(2,81,l0),
                         '2pow27':pow(2,27,l0),'Q':2**27,
                         '(l-1)^2':(l0-1)**2},
     'seconds':time.monotonic()-start}
print(json.dumps(out,indent=2))
```

[N] The exact lift/certificate output was:

```json
{
  "sympy": "1.14.0",
  "minimal_polynomial": "x**9 - 9*x**7 + 27*x**5 - 30*x**3 + 9*x + 1",
  "four_term_lift": "x**8 - 8*x**6 + 21*x**4 - 19*x**2 + x + 2",
  "four_term_norm": -109,
  "natural_product_lift_norms_d1_to_4": [
    -1,
    1,
    -27,
    6436341
  ],
  "A4_minus_A2pow4": "-1800*x**8 - 3552*x**7 + 9282*x**6 + 18428*x**5 - 12736*x**4 - 25640*x**3 + 4238*x**2 + 8918*x + 942",
  "four_term_kummer_ratio_mod73": 4,
  "four_term_identity": "w * gamma_1 = gamma^4",
  "order_certificate": {
    "l": 2593,
    "2pow81": 1,
    "2pow27": 1455,
    "Q": 134217728,
    "(l-1)^2": 6718464
  },
  "seconds": 0.04477300000144169
}
```
