[gaslamp] → codex · job cx-20261021-023524-5cfb · watch: tail -f /Users/a9lim/.gaslamp/jobs/cx-20261021-023524-5cfb/events.jsonl
(⊙_⊙) [D/N] Completed research note: [B4-moore.md](/Users/a9lim/Work/ogdoad/experiments/excess_search/notes/overnight/codex/B4-moore.md). It contains the complete analogue tables, proofs, executable scripts, and exact outputs.

[D] **The cubic determinant ratios have substantial structure.** Put \(s=3^{k-1}\) and \(r=2s\). Then
\[
\Delta_r=1,\qquad \Delta_d=0\ (d>r),\qquad
\boxed{\Delta_{r-d}=\Delta_d^{\,2^{r-2d}}\quad(0\le d\le s).}
\]
The orbit spans the relative trace-zero space. Its trace Gram matrix is
\(J=\begin{pmatrix}0&I_s\\I_s&0\end{pmatrix}\), and its symmetric Moore matrix satisfies \(H^{-1}=JHJ\). Jacobi’s complementary-minor identity proves the boxed formula.

[N] The requested cubic ratios are:

| \(k\) | \(\ell\) | Ratios through the full rank |
|---:|---:|---|
| 1 | 7 | \(1,0\) |
| 2 | 73 | \(1,40,62,14,16,0\) |

[D] Every entry follows from
\[
L(\Delta_2)=\tfrac72L(\gamma),\qquad
L(\Delta_3)=\left(\tfrac{19}{2}+2^{j_k}\right)L(\gamma),
\quad 2^{j_k}\equiv\pm5/2\pmod{3^{k+1}},
\]
and complementary duality. At \(k=2\), \(j_k=4\). Prime-conductor analogues also satisfy a complementary-minor identity, explaining their reflected ratio lists.

[D/N] **There is a precise failure of characteristic-zero lifting.** At conductor 27, let \(A_d\) multiply the natural characteristic-zero lifts of all nonzero binary linear forms on the first \(d\) conjugates. Then
\[
\operatorname{red}(A_4)=\operatorname{red}(A_2)^4,
\qquad N(A_2)=1,\qquad N(A_4)=3^{10}\cdot109.
\]
Thus the modular identity fails for these specified lifts. In particular, the four-term sum’s natural lift has norm \(-109\), disproving “linear forms, hence cyclotomic units.” This does not exclude other lifts of the same residue.

[D] **The proposed blanket no-go cannot hold.** For the trace-zero plane \(W\subset E=\mathbb F_{Q^3}\),
\[
W^\times/W^\times=E^\times.
\]
Indeed, \(W\cap aW\ne0\) for every \(a\ne0\). Consequently, some binary linear form has nonzero Kummer value for every nontrivial character. Evaluating *all* forms as known multiples of \(L(\gamma)\) would prove arm C.

[D] A narrower obstruction is proved: at degree \(81\), \(\ell=2593\), the same trace-zero space contains both \(\ell\)-th powers and nonpowers, all with the same Frobenius span and minimal additive polynomial. A difference-set count establishes this without evaluating the selected row.

[D] The remaining first unknown flag coordinate is
\[
L(\Delta_4)=(24+4\cdot2^{j_k})L(\gamma)+L(\Delta_3+1).
\]
The known logarithm of \(\Delta_3\) does not evaluate its additive translate.

[H] These results explain the small cubic fixtures but do not close the higher partial-flag route. No proof of arm C follows.

[gaslamp] job: cx-20261021-023524-5cfb · session: 01a15d2b-f51b-7ce3-ba91-4cfa86afb1e4 · resume: gaslamp codex --resume 01a15d2b-f51b-7ce3-ba91-4cfa86afb1e4 · tok: 1264k→35k
