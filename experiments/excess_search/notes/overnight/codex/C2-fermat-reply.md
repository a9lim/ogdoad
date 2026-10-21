[gaslamp] → codex · job cx-20261021-023524-5331 · watch: tail -f /Users/a9lim/.gaslamp/jobs/cx-20261021-023524-5331/events.jsonl
(⊙_⊙) **[D] A stronger unconditional bound is proved:**
\[
\boxed{\delta_n\ge \left\lceil\frac{2^{2n+1}}5\right\rceil\quad(n\ge1).}
\]
Using the Fermat-factor congruence sharpens this to
\[
\boxed{\delta_n\ge B_n:=1+2^{n+2}\left\lceil\frac{2^{n-1}}5\right\rceil\quad(n\ge2).}
\]
This improves the supplied general order bound for \(n\ge4\). Full primitivity remains unresolved.

The complete research note, including proofs of the relation formulas and characterwise unit-index criterion, is saved as [C2-fermat.md](/Users/a9lim/Work/ogdoad/experiments/excess_search/notes/overnight/codex/C2-fermat.md).

**[D] 1. The Artin–Schreier relation web has a homogeneous Kummer shadow.**

With unique square roots understood in finite multiplicative groups,
\[
a_j=a_{j-1}^{3/2}u_j^{-1/2},\qquad
c_j=a_{j-1}^{1/2}u_j^{-1/2}.
\]
Consequently
\[
a_j=\prod_{i=0}^j u_i^{-3^{j-i}/2^{j-i+1}},
\qquad
c_j=u_j^{-1/2}\prod_{i<j}u_i^{-3^{j-1-i}/2^{j-i+1}}.
\]
These follow directly from \(c_j^2u_j=a_{j-1}\) and \(a_j=c_ja_{j-1}\).

Fix \(\ell\mid F_n\), put \(s=\Phi_\ell(u_n)\), and evaluate in any common tower field containing the coordinates. Pairwise coprimality of the Fermat numbers gives \(\Phi_\ell(u_j)=0\) for \(j\ne n\). Therefore
\[
\Phi_\ell(a_j)=
\begin{cases}
0,&j<n,\\
-3^{j-n}2^{-(j-n+1)}s,&j\ge n,
\end{cases}
\]
and
\[
\Phi_\ell(c_j)=
\begin{cases}
0,&j<n,\\
-s/2,&j=n,\\
-3^{j-n-1}2^{-(j-n+1)}s,&j>n.
\end{cases}
\]
Also \(\Phi_\ell(c_j+1)=\Phi_\ell(c_j)+\mathbf1_{j=n}s\).

Thus every multiplicative word in these coordinates and their Frobenius conjugates remains a scalar multiple of \(s\). The displayed identities admit \(s=0\). This does **not** show that every additive consequence is powerless: the new lower bound below uses the recurrence without independently evaluating \(s\).

**[D] 2. The CM lift gives an exact selected splitting criterion, with multiple character contributions.**

First, the conductor needs careful indexing:
\[
\operatorname{ord}(c_1)=15,\qquad
\operatorname{ord}(c_n)=\operatorname{ord}(a_n)
=\prod_{j=1}^n\delta_j\quad(n\ge2).
\]
Indeed \(c_n^{F_n}=a_{n-1}\), the lower and upper multiplicative factors are coprime, and \(a_n=c_n^{F_n+1}\); the latter power loses only the initial factor three. Thus the primitive conductor is unknown until the corresponding selected orders are known.

Set \(N=\operatorname{ord}(c_n)\), \(K=\mathbf Q(\zeta_N)^+\), and choose a prime \(P\mid2\) with \(\bar\zeta_N=c_n\). The real cyclotomic unit
\[
\eta=\zeta_N^{1/2}+\zeta_N^{-1/2}
\]
satisfies
\[
\boxed{\bar\eta^4=a_{n-1}u_n^3,\qquad
4\Phi_\ell(\bar\eta)=3\Phi_\ell(u_n).}
\]
For the proof, \(1+\zeta_N^{-1}=\zeta_N^{-1/2}\eta\), so
\(\bar\eta^2=c_nu_n^2\); now use \(c_n^2u_n=a_{n-1}\).
Since \(n\ge1\) implies \(\ell\ge5\), this preserves the vanishing test **even when \(\ell\mid N\)**.

Writing \(P^+=P\cap K\), \(L=K(\mu_\ell)\), and \(Q\mid P^+\), local Kummer theory therefore gives
\[
\boxed{
v_\ell(\delta_n)<v_\ell(F_n)
\iff Q\text{ splits completely in }L(\eta^{1/\ell})/L.
}
\]
The residue field already contains \(\mu_\ell\); at residue characteristic two, splitting is equivalent to the residue unit being an \(\ell\)th power.

There is no half-field CM forcing. For \(n\ge2\), \(N\) contains five and a prime \(t\mid\delta_n\). The congruence \(2^j=-1\bmod5\) requires \(j\equiv2\bmod4\), whereas modulo \(t\) it requires \(j\equiv2^n\bmod2^{n+1}\). Hence conjugation is outside \(\langle2\rangle\). The real residue degree remains \(h=2^{n+1}\).

Assume now \(\ell\nmid |G|\), where \(G=\operatorname{Gal}(K/\mathbf Q)\). With normalized integral character idempotents, the relevant characters are precisely
\[
\Gamma=\{\psi\text{ even}:\overline{\psi(2)}=2\bmod\ell\}.
\]
For conductor \(f\), let
\[
E_\psi(N)=\prod_{t\mid N,\ t\nmid f}(1-\psi(t)^{-1}),\qquad
d_f=[\mathbf Q(\zeta_N):\mathbf Q(\zeta_f)].
\]
Cyclotomic distribution gives, in additive unit notation,
\[
e_\psi\eta_N
=\frac{\psi(2)-1}{d_f}E_\psi(N)e_\psi(1-\zeta_f)
=\frac{E_\psi(N)}{d_f}e_\psi\eta_f.
\]
The denominator \(d_f\) is an \(\ell\)-adic unit but matters when summing contributions.

If \(e_\psi\eta_f=I_\psi b_\psi\), with \(b_\psi\) a basis of the unit eigenline and \(I_\psi\) its circular-unit index coefficient, then the exact criterion is
\[
\boxed{
\frac34\Phi_\ell(u_n)
=\sum_{\psi\in\Gamma}
\overline{d_f^{-1}E_\psi(N)I_\psi}\,
\rho_{P^+}(b_\psi).
}
\]

For \(n\ge2\),
\[
|\Gamma|=\frac{\varphi(N)}{2h}\ge4.
\]
Indeed \(5t\mid N\) and \(t-1\ge2h\). Thus a selected sum can vanish by cancellation; arm C’s single-eigenline disjunction does not carry over.

**[D] Euler annihilation never kills every relevant component.** Choose an odd quartic character modulo five. At one prime \(t\mid\delta_n\), choose a character whose value at two completes the desired primitive \(h\)th root; this character is odd. At every other prime factor use the quadratic character, which is even and takes value one at two. Their product is even, relevant, and nontrivial on every local factor. Its conductor contains every prime dividing \(N\), so \(E_\psi(N)=1\).

This excludes uniform Euler forcing, but leaves unit-index divisibility, selected reduction, and cancellation. When \(\ell\mid|G|\), the character decomposition above is unavailable; the selected Kummer splitting criterion remains valid.

**[D] 3. Proof of the stronger order bound.**

On
\[
\mathcal E:\quad y^2+y=x^3+x^2,
\]
put
\[
P=(c_{n-1},c_n),\qquad d=[\mathbf F_2(P):\mathbf F_2]=2^{n+1},
\]
and define
\[
g=(y+1)/y,\qquad
\iota(x,y)=(x+1,y+x+1),\qquad v=g\circ\iota.
\]
The recurrence puts \(P\) on the curve. Direct substitution shows that \(\iota\) preserves it and \(\iota^2(x,y)=(x,y+1)\).

Let \(Q=2^{2^{n-1}}\). The \(Q\)-power Frobenius sends \(x\) to \(x+1\), and sends \(y\) to either \(y+x\) or \(y+x+1\). Consequently
\[
g(P)=u_n,\qquad v(P)=u_n^{Q}\ \text{or}\ u_n^{-Q}.
\]
Both values lie in \(\langle u_n\rangle\).

Label
\[
A=(0,0),\ B=(0,1),\ C=(1,0),\ D=(1,1).
\]
Horizontal-line intersections and the permutation
\(A\to D\to B\to C\to A\) give
\[
\operatorname{div}(g)=-2[A]+2[B]-[C]+[D],
\]
\[
\operatorname{div}(v)=[A]-[B]-2[C]+2[D].
\]
Hence \(g^av^b\) has pole degree
\[
H(a,b)=|2a-b|+|a+2b|.
\]
The coefficient matrix has determinant five, so these functions are multiplicatively independent.

Consider
\[
\Lambda=\{(a,b)\in\mathbf Z^2:g(P)^av(P)^b=1\}.
\]
Its index is exactly \(\delta_n\). Every nonzero lattice vector gives a nonzero rational function \(g^av^b-1\), defined over \(\mathbf F_2\), vanishing at the degree-\(d\) point \(P\). Therefore
\[
H(a,b)\ge d\qquad(0\ne(a,b)\in\Lambda).
\]
The convex body \(H(a,b)<R\) has area \(2R^2/5\). The two-dimensional Minkowski theorem **[S]** would produce a nonzero lattice vector with \(H<d\) if \(\delta_n<d^2/10\). Thus
\[
\delta_n\ge d^2/10=2^{2n+1}/5.
\]

Every prime dividing \(F_n\), \(n\ge2\), is \(1\bmod2^{n+2}\). Rounding within that progression yields \(B_n\). Moreover, a prime \(\ell\) missing at full valuation divides \(F_n/\delta_n\), giving the improved defect restriction
\[
\boxed{\ell\le\left\lfloor F_n/B_n\right\rfloor.}
\]

**[D] Why this escapes the previous bound:** the two functions are independent as rational functions while their selected values occupy one cyclic group. The argument bounds the degree cost of an exact relation; it does not require independent Kummer phases or assume that the elliptic point has order \(F_{n-1}\).

**[N] Verification:** `ZF-divisor-symbolic` checked curve preservation, \(\iota^2\), the divisor permutation, and determinant five. No searches or finite-field rows were run. The new theorem has a paper proof, not a Lean certificate.

[gaslamp] job: cx-20261021-023524-5331 · session: 01a15d2b-f51b-7ec0-809b-894b10c1aa3b · resume: gaslamp codex --resume 01a15d2b-f51b-7ec0-809b-894b10c1aa3b · tok: 879k→35k
