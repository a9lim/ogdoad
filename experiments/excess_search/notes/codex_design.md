[gaslamp] → codex · job cx-20261019-224231-b2e8 · watch: tail -f /Users/a9lim/.gaslamp/jobs/cx-20261019-224231-b2e8/events.jsonl
(•̀ᴗ•́) **Build a dependency-aware norm engine with three paths: cached conductor norms, crossed binomials, and synchronized resultants.** The crossed-binomial path handles all six examples efficiently. It also handles many two-component Z rows after converting the sum to a ratio. General multicomponent recursion is exact, but its intermediate expressions can still grow to the original field size; there is no justified universal compression claim here.

I inspected the live paper and certificate scripts, recomputed census coverage, and benchmarked NTL arithmetic at the proposed tower dimensions. The timings below are kernel measurements and Euler-loop estimates, not completed row certifications.

**Corrections to the brief**

- “In any finite field containing the element” is false. For \(x\in\mathbb F_{2^e}\), extending by a degree divisible by \(p\) makes every original element a \(p\)-th power. Extension preserves the test when its degree is prime to \(p\). The stated norm identity is correct.
- “Nothing is known for \(p\ge733\)” is too strong. The repository already has cubic/exceptional family certificates covering later primes; for example, \(2593\) has conductor \(81\). Import those results with their actual verification boundaries.
- The \(359\) certificate already supplies the norm needed for **1433**, because both primes have conductor \(179\). This is a cache lookup plus a small exponentiation, once that certificate is fully trusted.
- Crossing does not make recursive root extraction free. Replacing a radicand by its norm generally loses information needed to construct its next root.
- Increasing numerical order is unnecessary between unrelated rows. Require certified ancestry, and prioritize eligible jobs by marginal mass divided by measured cost. If strict numerical order is retained, an expensive unrelated row can stall the search.

**1. The crossed-binomial operation**

Maintain an explicit, ancestry-consistent coefficient field
\[
K=\mathbb F_{2^B},
\qquad z^R=A\in K,
\qquad [K(z):K]=R,
\]
where \(R\) is odd. First consider the target \(1+z\).

Choose \(t\mid B\), put \(k=\mathbb F_{2^t}\), and require
\[
h\mid Rt,\qquad
f(\ell)\mid t,\qquad
\ell\nmid B/t
\quad\text{for every prime }\ell\mid R.
\]
These ensure the required roots of unity and preserve the relevant primary valuations. A smallest admissible divisor is obtained by taking the lcm of:

- \(h/\gcd(h,R)\);
- all \(f(\ell)\);
- all \(\ell^{v_\ell(B)}\), for \(\ell\mid R\).

Reject the cut if this does not divide \(B\). Also try larger admissible \(t\): a larger output field can be worthwhile if it substantially reduces the characteristic-polynomial degree.

Set
\[
D=B/t,\quad N=2^B-1,\quad
G=\prod_{\ell\mid R}\ell^{v_\ell(N)},\quad
n=\frac{2^B-1}{2^t-1}.
\]
Compute
\[
w=n^{-1}\pmod G,\qquad c=N_{K/k}(A)^w.
\]
Then \(A/c=A^{1-nw}\) has order dividing \(N/G\), which is coprime to \(R\). Therefore an explicit root is
\[
a=(A/c)^{R^{-1}\bmod(N/G)}.
\]
Handle \(N/G=1\) separately with \(a=1\).

Check, exactly,
\[
c^{2^t}=c,\qquad a^R=A/c.
\]

Now construct
\[
H=k[V]/(V^R-c).
\]
Certify this binomial irreducible. Since \(\gcd(D,R)=1\), \(K\cap H=k\), and \(z=aV\) gives a valid embedding of the original binomial extension.

If \(F_a(T)\) is the **characteristic polynomial** of \(a\) over \(k\), of degree \(D\), then
\[
W(V)=N_{KH/H}(1+aV)=V^D F_a(V^{-1}).
\]
Reduce modulo \(V^R-c\), and test
\[
W^{(2^{Rt}-1)/p}=1.
\]

This uses fields of degrees \(B\) and \(Rt\), rather than \(BR\).

A critical implementation detail: if the minimal polynomial of \(a\) has degree \(d<D\), use
\[
F_a=P_a^{D/d}.
\]
Using \(P_a\) alone computes the wrong norm. For ordinary singleton rows, \(A=c a^R\) and the known degree of \(A=\alpha_r\) often prove that \(d=D\). That argument need not hold for a ratio radicand.

For initial implementation, generate a candidate minimal polynomial with power projection, then verify annihilation and its degree/irreducibility exactly. NTL exposes modular composition and minimal-polynomial operations; FLINT supplies polynomial composition and resultant machinery. [NTL documentation](https://libntl.org/doc/GF2EX.cpp.html), [FLINT documentation](https://flintlib.org/doc/fq_poly.html).

**2. Two-component Z rows become binomial problems**

Suppose
\[
\beta=y_1+y_2,\qquad
y_1^{R_1}=A_1,\quad y_2^{R_2}=A_2,
\]
over one synchronized coefficient field \(K\), with coprime \(R_1,R_2\).

Check that \(h\nmid d(y_2)\). Then \(y_2\) is automatically a \(p\)-th power, and
\[
\beta=y_2(1+z),\qquad z=y_1/y_2
\]
has the same \(p\)-power status as \(1+z\). Moreover,
\[
z^{R_1R_2}=A_1^{R_2}/A_2^{R_1}.
\]

Thus apply the preceding operation with the **composite** radical degree \(R=R_1R_2\). Certify the degree and binomial irreducibility; do not merely assume them.

This directly handles the examples:

- **743:** \(K=\mathbb F_{2^{156}}\),
  \[
  z=\chi_7/\chi_{53},\qquad
  z^{371}=\alpha_7^{53}/\alpha_{53}^{7}.
  \]
- **1031:** \(K=\mathbb F_{2^{408}}\),
  \[
  z=\chi_5/\chi_{103},\qquad
  z^{515}=\alpha_5^{103}/\alpha_{103}^{5}.
  \]

A Z row consisting of an odd component plus a finite component is similar: normalize by the finite component, include it in \(K\), and cross the resulting single binomial.

The parent field must preserve shared components. For 743, both \(\alpha_7\) and \(\alpha_{53}\) must use the same \(\chi_3\). Building them independently and then choosing arbitrary embeddings is invalid.

An explicit safe construction for 743 starts over \(\mathbb F_{2^6}\), with \(u=\chi_3\):
\[
P_{\chi_7}(X)=X^7+u+1,
\]
and
\[
P_{\chi_{13}}(X)
 =X^{26}+X^{13}+u^2+u+u^3,
\]
because \(\chi_2=u^3\) and \(\chi_4^2+\chi_4=\chi_2\). Hence
\[
P_{\chi_{53}}(X)=P_{\chi_{13}}(X^{53}+1).
\]
The shared phase is present explicitly in \(u\).

**3. General multicomponent recursion**

Use a DAG of field models, embeddings, component expressions, and norm operations. Never cache a component polynomial without its embedding information when it will be combined with another component.

For independent residual radical degrees \(R_i\), which are pairwise coprime, put
\[
R=\prod_iR_i,\qquad z=\prod_i y_i.
\]
Then
\[
z^R=\prod_i A_i^{R/R_i}.
\]
Choose CRT exponents \(e_i\) satisfying
\[
e_i\equiv1\pmod{R_i},\qquad
e_i\equiv0\pmod{R_j}\quad(j\ne i).
\]
There are explicitly computable \(k_i\in K\) such that
\[
y_i=k_i z^{e_i}.
\]
Consequently the selected sum is one polynomial
\[
\beta=m+\sum_i k_i z^{e_i}.
\]

Cross \(z=aV\) as above. The required norm is now the synchronized expression
\[
W(V)=N_{K/k}\!\left(m+\sum_i k_i a^{e_i}V^{e_i}\right).
\]

Represent \(K=k[T]/P(T)\), with all coefficients expressed in this **same** \(T\)-basis. Compute
\[
W(V)=
\operatorname{Res}_T
\left(P(T),\,m+\sum_i C_i(T)V^{e_i}\right)
\pmod{V^R-c}.
\]

This is the implementable generalization. It preserves every correlation among the coefficients. Separate characteristic polynomials of the \(C_i\) are insufficient.

Apply it recursively through the ancestry:

1. Cross a retained radical to separate it from an unwanted ancestor extension.
2. Express the current target in that common presentation.
3. Eliminate the ancestor with its actual relative norm.
4. Reduce the resulting polynomial immediately.
5. Repeat only while predicted intermediate sizes remain within budget.

Use closed forms whenever possible:
\[
N(by+c)=c^\ell+b^\ell A\quad(y^\ell=A),
\]
and
\[
N(by+c)=c^2+bc+b^2A\quad(y^2+y=A).
\]

There are two important limits.

First, inherited prime-power levels must be removed before defining \(R_i\). If \(K\) already contains \(\chi_{r^j}\), adjoining \(\chi_{r^a}\) has relative degree \(r^{a-j}\), not \(r^a\).

Second, a general resultant over \(H\) can require \(D\) coefficients that are themselves \(H\)-elements: approximately \(DRt=BR\) bits. Thus this recursion **does not guarantee** avoidance of original-size intermediates. Its reachable class is precisely the rows whose chosen elimination plan has affordable coefficient fields, radical fields, and resultant intermediates. Record an explicit cost-limited unresolved result when that fails.

The scalar crossing is especially valuable because its characteristic polynomial has only \(B\) bits of coefficient data, and can be computed before entering \(H\). A general synchronized multicomponent norm lacks that advantage.

**4. Arithmetic strategy and six-row costs**

Do not estimate these tests as generic exponentiation with dense multiplications. After crossing, \(W\) often has degree only \(D\). Left-to-right binary exponentiation uses
\[
L-1\text{ squarings},\qquad
\operatorname{popcount}(e)-1\text{ multiplications by }W,
\]
where \(e=(2^{Rt}-1)/p\). Multiplication by a fixed linear or quadratic polynomial is much cheaper than a dense product.

I benchmarked NTL `GF2EX` over sparse irreducible binary coefficient fields, modulo \(V^R+c\). The radicands and low-degree targets were synthetic; these measurements test arithmetic costs, not the selected rows.

| \(p\) | Original \(E\) | Parent \(B\) | \(t\) | \(R\) | \(D\) | Crossed degree \(Rt\) | Estimated Euler loop |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 733 | 3,660 | 60 | 60 | 61 | 1 | 3,660 | 0.06 s |
| 743 | 57,876 | 156 | 156 | 371 | 1 | 57,876 | 1.5 s |
| 797 | 394,020 | 1,980 | 396 | 199 | 5 | 78,804 | 6.3 s |
| 1031 | 210,120 | 408 | 204 | 515 | 2 | 105,060 | 7.9 s |
| 1433 | 3,504,820 | 19,580 | 178 | 179 | 110 | 31,862 | 4.0 s cold; use cache |
| 4507 | 1,126,500 | 1,500 | 750 | 751 | 2 | 563,250 | 319 s |

These exclude parent construction, subfield conversion, root extraction, characteristic-polynomial construction, and certificate checking.

For 4507, measured squaring was approximately \(0.210\) ms, multiplication by a quadratic \(0.713\) ms, and dense multiplication \(18.2\) ms. That distinction materially changes the implementation choice.

Specific consequences:

- **733:** crossing cannot shrink the field: \(f(61)=60\) already forces \(t=B\).
- **743:** the ratio gives a convenient binomial presentation, but no degree reduction.
- **797:** a degree-five characteristic polynomial removes a factor of five.
- **1031:** the synchronized ratio and a quadratic characteristic polynomial halve the degree.
- **4507:** the quadratic crossing halves the degree. Its ancestor row 751 must be certified first; that row has degree only 1500.
- **1433:** avoid the cold path.

For 1433, the existing \(359\) norm is
```text
theta = 0x28494A54795638CF203B2404FE5133E2AE0E13C2CA4E6
```
in the model with modulus \(X^{179}+X^4+X^2+X+1\). Independent bit-polynomial arithmetic gave
```text
theta^((2^179 - 1)/1433)
    = 0x45bb1bf316726f64204e097b468980d1d69093e70909d
```
which is nonidentity and whose 1433rd power is one.

**Verified here:** that exponentiation and torsion check.  
**Inherited dependency:** identification of `theta` with the selected norm; I did not rerun the full \(359\) resultant certificate. Once that link is accepted or replayed, this establishes the required nonpower for 1433.

For more general targets, benchmark Frobenius-assisted multiexponentiation against the low-degree binary method. Do not assume the former wins.

Also, \(q\)-Frobenius is diagonal in the Kummer basis only when \(R\mid q-1\). For higher prime-power radicals, use the general monomial action
\[
V^q=C V^j,\qquad j=q\bmod R,
\]
which induces a permutation with scalar multipliers on the basis. Reusing the 719 diagonal formula indiscriminately would be wrong.

**5. Exactness checks that should be mandatory**

The certificate verifier should establish:

- **Field validity:** exact irreducibility of coefficient moduli and every claimed extension. Checking \(y^\ell=A\) in a possibly reducible quotient is insufficient.
- **Degree validity:** Frobenius degree checks, or a checked inductive irreducibility argument, for each claimed generated field.
- **Embedding validity:** every shared component has one image; every tower relation holds under the recorded embeddings.
- **Cut validity:** \(t\mid B\), \(h\mid Rt\), and the primary-valuation/disjointness conditions hold.
- **Crossing validity:** subfield membership of \(c\), \(a^R=A/c\), and reconstruction of the original component expressions.
- **Norm validity:** characteristic-polynomial multiplicities are correct; synchronized coefficients remain synchronized.
- **Euler validity:** the exponent division is exact, the target is nonzero, and the resulting phase has \(p\)-th power one.

Handle zero explicitly: zero is a \(p\)-th power, although its Euler power is not one.

For composed sums with overlapping fields, a factor of the expected degree is not a sufficient certificate. Identify the factor by evaluation in the anchored common model, or derive it through a relative construction that already fixes the shared subfield.

For the stored certificates, hashes provide integrity only. The 359 quick mode explicitly does not establish the norm link; the 719 quick mode does not establish the characteristic-polynomial link. Import authoritative results only after the full checks or an equivalent independent verification.

Finally, cache keys must include ancestry and model hashes. If an earlier excess changes, invalidate its descendants. Finding that the proposed rule value is a power does **not** itself compute the replacement excess or its degree.

**6. Reachable mass**

I recomputed structural coverage from the supplied million-row census. The additional path counted here is deliberately simple:

- singleton odd components, including the required finite translate field;
- two-component Z sums reducible to the ratio construction;
- full independent radical degrees, excluding partially inherited levels;
- both \(B\) and \(Rt\) within the stated cap.

These are degree-qualified candidates, not completed tests or guaranteed CPU budgets.

For \(727<p\le10^5\):

| Degree cap | Direct rows | Additional crossed rows | Combined \(\sum1/p\) | Fraction of total mass |
|---:|---:|---:|---:|---:|
| \(10^5\) | 1,392 | 285 | 0.264595 | 47.9% |
| \(10^6\) | 2,823 | 699 | 0.384062 | 69.5% |
| \(10^7\) | 4,436 | 1,370 | 0.471494 | 85.3% |

The total mass through \(10^5\) is \(0.552765\).

Restricting additional crossed jobs to \(D\le16\) gives more conservative initial targets:

- cap \(10^5\): **1,599 rows**, mass **0.244885**;
- cap \(10^6\): **3,209 rows**, mass **0.345287**.

For the more valuable interval \(727<p\le10^4\):

- cap \(10^5\): 597 degree-qualified rows, mass \(0.225013\);
- cap \(10^6\): 898 rows, mass \(0.296518\);
- cap \(10^7\): 1,067 rows, mass \(0.325056\), versus total \(0.330553\).

Thus a realistic engineering target is approximately **0.25–0.38 mass through \(10^5\)** before investing heavily in general multicomponent resultants. The tables do not establish how many CPU-hours that entire campaign takes: field construction and characteristic-polynomial costs must be measured, especially for the larger \(D\) cases.

Use a scheduler score
\[
\frac{\text{new mass unlocked by this job}}
{\text{measured construction + verification + Euler time}},
\]
including descendants and other primes sharing the same conductor. Cache the selected norm by \((h,m)\), not by \(p\).

**7. The random model**

For a uniformly random nonzero field element, the \(p\)-power probability is exactly \(1/p\). The unsupported step is applying that distribution to these recursively selected elements.

In particular:

- theorem- or certificate-settled rows have zero remaining search uncertainty;
- ancestry creates possible dependence;
- uniformity should be hypothesized for the selected norm after accounting for known structural constraints;
- expected count \(\sum1/p\) needs the marginal assumptions;
- converting it to \(1-\exp(-\sum1/p)\) additionally needs an independence approximation.

Sharing a conductor is computationally valuable, but does not itself refute independence under a uniform cyclic-group model: distinct prime coordinates are independent in that model.

Use \(\sum1/p\) as a transparent scheduling weight. Do not present its divergence, or the quoted hit percentages, as evidence that a counterexample must exist.

The benchmark sources and coverage planner are in [/tmp/ogdoad-excess-consult](/tmp/ogdoad-excess-consult). Repository files were unchanged.

[gaslamp] job: cx-20261019-224231-b2e8 · session: 01a15730-6560-7733-abb0-d37b2e8b082b · thread: excess-engine · resume: gaslamp codex --thread excess-engine · tok: 1205k→25k
