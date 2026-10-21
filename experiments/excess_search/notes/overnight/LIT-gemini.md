[gaslamp] → gemini · job gm-20261021-014254-8abd · watch: tail -f /Users/a9lim/.gaslamp/jobs/gm-20261021-014254-8abd/events.jsonl
### Provenance & Verification Summary
- **Queries run:** Grounded web searches (`search_web`) + direct primary-source fetches (`curl`, GitHub REST API via `gh`, arXiv API, OpenAlex citation-graph API, and MathOverflow API). All grounding redirect URLs were resolved to canonical URLs and primary files were inspected directly.
- **Direct local verification performed:**
  1. Downloaded and parsed all 1,023 computed odd-prime records ($p \le 12281$) from `DjangoPeeters/transfinite-nim-calculator` (`logs/excess_records.txt` and `logs/q_set_records.txt`) and cross-checked every entry against the 0/1/4 rule.
  2. Verified in `SymPy`/`FLINT` over $\mathbb{F}_2$ that the Gauss period $x_k = \zeta_{3^{k+1}} + \zeta_{3^{k+1}}^{-1}$ (satisfying $x_k^3 + x_k = x_{k-1}$, $x_0 = 1$) has **exact full multiplicative order** $2^{3^k}-1$ (index $1$, i.e., is a primitive element of $\mathbb{F}_{2^{3^k}}$) for all $k \in \{1, 2, 3, 4, 5\}$ (degrees $3, 9, 27, 81, 243$).

---

### Question 1: Lenstra Excess $m_p$, the 0/1/4 Rule, and Computations Beyond $p = 709$

* ** verdict:** **No published or preprint proof, disproof, or counterexample** to the 0/1/4 rule or boundedness of $m_p$ exists as of October 2026. However, **897 additional odd primes beyond $p = 709$ (up to $p = 12281$) have been computed** where the Lenstra exponent $e_p$ is tractable, and **every single one obeys the 0/1/4 rule with zero exceptions** ($m_p \in \{0, 1, 4\}$, and $m_p = 4$ occurs only at $p \in \{19, 163, 1459\}$).

* **OEIS A380496 & `a380496.txt` (Aaron N. Siegel, Jan 2025; extended by Django Peeters & Tristan Figueroa-Reid, Oct 2025 – Jul 2026)**
  * **URLs:** https://oeis.org/A380496 and https://oeis.org/A380496/a380496.txt
  * **Relevance:** The contiguous b-file stops at $a(126)$ ($p = 709$, as $p = 719$ has $e_{719} = 1{,}258{,}230{,}380$), but Peeters's linked `a380496.txt` tabulates $n = 1\dots 1417$ ($p \le 11807$, with `?` at uncomputed primes), explicitly noting: *"The only other observed values of $m_p$, besides $0$ or $1$, are $m_{19} = m_{163} = m_{1459} = 4$."*

* **Django Peeters, `transfinite-nim-calculator` (GitHub repository, commits through Sep 6, 2026)**
  * **URLs:**
    * Repo: https://github.com/DjangoPeeters/transfinite-nim-calculator
    * Computed excess cache ($1{,}023$ odd primes up to $p = 12281$): https://raw.githubusercontent.com/DjangoPeeters/transfinite-nim-calculator/main/logs/excess_records.txt
    * Computed $Q$-sets ($1{,}149$ odd primes up to $p = 12289$): https://raw.githubusercontent.com/DjangoPeeters/transfinite-nim-calculator/main/logs/q_set_records.txt
    * Excess search implementation (`important_funcs.cpp`): https://raw.githubusercontent.com/DjangoPeeters/transfinite-nim-calculator/main/src/alpha_calc/important_funcs.cpp
  * **Relevance:** Directly answers both parts of Q1:
    1. **Verification beyond $p = 709$:** Across all $1{,}023$ odd primes in `excess_records.txt` ($126$ primes $\le 709$ and $897$ primes in $727 \le p \le 12281$), I ran a script checking $m_p$ against the exact 0/1/4 rule ($m_p = 0$ if $|Q(f(p))| \ne 1$ or the unique element of $Q(f(p))$ is even; $m_p = 4$ if $f(p) = 2\cdot 3^k$; else $m_p = 1$). **Result: 0 mismatches out of 1,023 primes.** The only primes with $m_p = 4$ are $p = 19$ ($f = 18, Q = \{9\}$), $p = 163$ ($f = 162, Q = \{81\}$), and $p = 1459$ ($f = 486, Q = \{243\}$). (Note: the next prime with $f(p) = 2\cdot 3^k$ and singleton odd $Q$ is $p = 2917$ with $f(2917) = 1458 = 2\cdot 3^6, Q = \{729\}$, which is skipped in `alpha_records.txt` because its exponent exceeds the memory/time cutoff.)
    2. **The 0/1/4 rule is hardcoded as the initial guess in `important_funcs.cpp` (lines 253–258):** Peeters initializes `excess1` via:
       ```cpp
       uint8_t excess1 = 0;
       const uint16_t fp = f(p);
       if (fp != 2 && (fp & 1) == 0 && is_3_pow(fp >> 1)) {
           excess1 = 4;
       } else if (q_set1.size() == 1 && (q_set1[0] & 1) != 0) {
           excess1 = 1;
       }
       ```
       and only increments `excess1++` in a `while (!done)` loop if the candidate fails the order test—meaning the empirical 0/1/4 rule is already known to Peeters/Siegel as the exact initial predictor that always succeeds on the first try.

* **Lucia Rîşnoveanu, *"Some quadratically closed fields of nimbers"* (arXiv:2606.28414v2, June 2026)**
  * **URL:** https://arxiv.org/abs/2606.28414
  * **Relevance:** Recent 2026 work extending Lenstra (1978) on quadratically closed ordinal subfields of $\mathbf{On}_2$ ($\{\varepsilon_\alpha \mid \alpha \le \omega^{\omega^\omega}\}$), but does not address finite excesses $m_p$ below $\omega^{\omega^\omega}$.

---

### Question 2: Wiedemann's Conjecture and Conway's Fermat Tower ($c_n^2 + c_n = c_0\cdots c_{n-1}$)

* **Verdict:** **Wiedemann's conjecture remains open** (both for $x_n$ generating the norm-one torus of order $2^{2^n}+1$ and for the product $x_0 x_1 \cdots x_n$ being primitive in $\mathbb{F}_{2^{2^n}}$). For Conway's tower $c_n^2 + c_n = c_0\cdots c_{n-1}$, the state of the art is **Popovych (2015/2018)** and its arbitrary-characteristic generalization **Cagliero–Herman–Szechtman (2025)**, which prove structural order identities ($O(c_i) = O(a_i)$ for $i \ge 2$) and conditional primitivity criteria, while unconditional full order remains open due to composite Fermat numbers $N_i = 2^{2^i}+1$.

* **Leandro Cagliero, Allen Herman, and Fernando Szechtman, *"Artin-Schreier towers of finite fields"* (arXiv:2405.10159v3, rev. Feb 2025; *Finite Fields Appl.* 103, 2025, 102606)**
  * **URLs:** https://arxiv.org/abs/2405.10159 and https://doi.org/10.1016/j.ffa.2025.102606
  * **Relevance:** Directly studies Conway's tower ($p=2$) and its degree-$p$ Artin-Schreier generalization $c_{i+1}^p - c_{i+1} = (c_{-1}\cdots c_i)^{p-1}$. Unconditionally proves that for all $i \ge 0$ (except $p=2, i=1$), $O(c_i) = O(a_i)$ and $O(c_i)$ equals the product of the relative orders of $c_j \bmod L_{j-1}^\times$, and that the $\mathrm{Gal}(L_i/L_{i-1})$-conjugates of $a_i$ form a normal basis. Explicitly notes in §1 that for $p=2, i \ge 2$, $O(c_i) = N_1\cdots N_i = (2^{2^{i+1}}-1)/3$ iff $c_0 c_i$ is primitive in $L_i$, and states that an explicit relationship between Conway's tower and Wiedemann's tower remains open.

* **Roman Popovych, *"Multiplicative orders of elements in Conway's towers of finite fields"* (arXiv:1509.01958, 2015; published in *Algebra and Discrete Mathematics* 25(1), 2018, 137–146)**
  * **URLs:** https://arxiv.org/abs/1509.01958 and https://admjournal.luguniv.edu.ua/index.php/adm/article/view/172
  * **Relevance:** Proves lower bounds on $O(c_i)$ in Conway's Fermat tower over $\mathbb{F}_2$ and proves that $O(c_i)$ achieves its maximum possible value $\prod_{j=1}^i (2^{2^j}+1)$ (making $c_0 c_i$ primitive in $\mathbb{F}_{2^{2^{i+1}}}$) if and only if for each $j$, the order of $c_j \bmod L_{j-1}^\times$ is the full Fermat number $N_j = 2^{2^j}+1$ (which holds automatically when $N_j$ is prime, i.e., up to $j=4$, and requires a non-power condition at prime factors of $N_j$ for $j \ge 5$).

* **Roman Popovych, *"On the multiplicative order of elements in Wiedemann's towers of finite fields"* (*Carpathian Math. Publ.* 7(2), 2015, 220–225)**
  * **URL:** https://doi.org/10.15330/cmp.7.2.220-225
  * **Relevance:** Improves Voloch's (2010) lower bound on the multiplicative order of elements in Wiedemann's tower $x_m + x_m^{-1} = x_{m-1}$, showing $\mathrm{ord}(x_n)$ grows doubly-exponentially when Fermat factors are controlled, but does not resolve Wiedemann's full-order conjecture.

* **Ulrich Seyfarth and Kedar S. Ranade, *"Cyclic mutually unbiased bases, Fibonacci polynomials and Wiedemann's conjecture"* (*J. Math. Phys.* 53, 2012, 062201) & Ulrich Seyfarth, PhD Thesis (arXiv:1907.02726, 2019)**
  * **URLs:** https://arxiv.org/abs/1104.0202 and https://arxiv.org/abs/1907.02726
  * **Relevance:** Reformulates Wiedemann's conjecture in terms of the Fibonacci index of symmetric matrices over $\mathbb{F}_2$ and cyclic MUBs in dimension $2^{2^k}$, verifying the conjecture computationally through $k \le 10$ ($2048$ qubits, using factored Fermat numbers up to $F_{10}$) and leaving $k \ge 11$ open.

* **Valerio Dose, Pietro Mercuri, Ankan Pal, and Claudio Stirpe, *"High order elements in finite fields arising from recursive towers"* (*Designs, Codes and Cryptography* 90, 2022, 1347–1368)**
  * **URL:** https://doi.org/10.1007/s10623-022-01041-3
  * **Relevance:** Applies the Burkhart et al. (2009) method to recursive towers $x_n^2 + x_n = v(x_{n-1})$ (odd $q$) and $x_n^3 + x_n = v(x_{n-1})$ ($q = 2$, yielding extensions $\mathbb{F}_{2^{2\cdot 3^n}}$), giving exponential lower bounds $\exp(c\sqrt{N})$ rather than full order.

---

### Question 3: Primitivity of $\zeta + \zeta^{-1}$ ($\zeta$ a Primitive $3^{k+1}$-th Root of Unity) in $\mathbb{F}_{2^{3^k}}$ and Vertical Artin Conjecture

* **Verdict:** **No paper in the literature was found that states or proves the conjecture specifically for the vertical 3-adic tower $\zeta_{3^{k+1}} + \zeta_{3^{k+1}}^{-1} \in \mathbb{F}_{2^{3^k}}$, nor is any counterexample known.** (In fact, I verified locally that $\zeta_{3^{k+1}} + \zeta_{3^{k+1}}^{-1}$ **is** a primitive element of $\mathbb{F}_{2^{3^k}}$ for all $1 \le k \le 5$, i.e., degrees $3, 9, 27, 81, 243$; note that this tower is generated recursively by the Chebyshev/Dickson cubic $x_k^3 + x_k = x_{k-1}$ with $x_0 = 1$, which is the exact $f(p) = 2\cdot 3^k$ tower underlying the $m_p = 4$ case in Question 1.) Existing literature on $\zeta + \zeta^{-1}$ in $\mathbb{F}_{2^n}$ focuses on prime conductors $r = 2n+1$ (horizontal variation) or Dickson polynomial dynamics.

* **Florian Breuer, *"Multiplicative orders of Gauss periods and the arithmetic of real quadratic fields"* (arXiv:2006.10344, 2020; *Finite Fields Appl.* 73, 2021, 101848)**
  * **URLs:** https://arxiv.org/abs/2006.10344 and https://doi.org/10.1016/j.ffa.2021.101848
  * **Relevance:** Studies the multiplicative index $\mathrm{ind}(\zeta + \zeta^{-1}) = (q^n - 1)/\mathrm{ord}(\zeta + \zeta^{-1})$ for Gauss periods of type $(n, 2)$ (primarily for prime conductor $p = 2n+1$), noting that $\mathrm{ord}(\zeta + \zeta^{-1}) = q^n - 1$ is "often sharp when $q = 2$ or $3$", and relates prime divisors of $\mathrm{ind}(\zeta + \zeta^{-1})$ dividing $q^2-1$ to the fundamental unit $\varepsilon_p$ and class number $h_p$ of $\mathbb{Q}(\sqrt{p})$.

* **Omran Ahmadi, Igor E. Shparlinski, and José Felipe Voloch, *"Multiplicative Order of Gauss Periods"* (arXiv:0707.4034; *Int. J. Number Theory* 6(4), 2010, 877–882) & Roman Popovych, *"On a multiplicative order of Gauss periods and related questions"* (arXiv:1008.0972, 2010)**
  * **URLs:** https://arxiv.org/abs/0707.4034 and https://arxiv.org/abs/1008.0972
  * **Relevance:** Prove partition-based lower bounds $\exp(c\sqrt{r})$ on $\mathrm{ord}(\zeta + \zeta^{-1})$ in $\mathbb{F}_{q^{(r-1)/2}}$ when $\zeta$ is a primitive $r$-th root of unity, using linear independence of conjugates (normal basis property). Note: for $r = 3^{k+1}$, $\zeta_{3^{k+1}} + \zeta_{3^{k+1}}^{-1}$ has trace $0$ over $\mathbb{F}_2$ for $k \ge 1$ (since $x_1^3 + x_1 + 1 = 0$ has no $x_1^2$ term), so it is **not** a normal element over $\mathbb{F}_2$.

* **Aart Blokhuis, Xiwang Cao, and Wun-Seng Chou, *"On the roots of certain Dickson polynomials"* (*J. Number Theory* 188, 2018, 271–282) & Simone Ugolini, *"Some notes on the multiplicative order of $\alpha + \alpha^{-1}$ in finite fields of characteristic two"* (*Period. Math. Hung.* 79, 2019, 111–117)**
  * **URLs:** https://doi.org/10.1016/j.jnt.2018.01.003 and https://doi.org/10.1007/s10998-019-00296-z
  * **Relevance:** Directly analyze the algebraic and multiplicative structure of $\alpha + \alpha^{-1}$ and roots of iterated Dickson polynomials $D_n(x, 1)$ in characteristic $2$ (for $n=3$, $D_3(x,1) = x^3+x$ is the exact transition map $\zeta_{3^{k+1}} + \zeta_{3^{k+1}}^{-1} \mapsto \zeta_{3^k} + \zeta_{3^k}^{-1}$).

* **Local verification on Q3 (new primary computational datum):**
  * Using `SymPy`/`FLINT` over $\mathbb{F}_2$, I computed the exact multiplicative order of $x_k = \zeta_{3^{k+1}} + \zeta_{3^{k+1}}^{-1} \in \mathbb{F}_{2^{3^k}}^\times$ (root of the $k$-th iterate of $x^3+x$ at $1$) against the prime factorization of $2^{3^k}-1$ for $k = 1, 2, 3, 4, 5$:
    * $k=1$ ($\mathbb{F}_{2^3}$, $|F^\times|=7$): **primitive** (index $1$).
    * $k=2$ ($\mathbb{F}_{2^9}$, $|F^\times|=7 \cdot 73$): **primitive** (index $1$).
    * $k=3$ ($\mathbb{F}_{2^{27}}$, $|F^\times|=7 \cdot 73 \cdot 262657$): **primitive** (index $1$).
    * $k=4$ ($\mathbb{F}_{2^{81}}$, $|F^\times|=7 \cdot 73 \cdot 2593 \cdot 71119 \cdot 262657 \cdot 97685839 \cdot 3712990163251158343$): **primitive** (index $1$).
    * $k=5$ ($\mathbb{F}_{2^{243}}$, $|F^\times|=2^{243}-1$, $11$ prime factors): **primitive** (index $1$).
  * **No counterexample exists for $k \le 5$.** Regarding a "vertical Artin conjecture" for cyclotomic units in $\mathbb{Z}_p$-towers mod $\ell$: while the $p$-adic distribution of cyclotomic units along $\mathbb{Z}_p$-towers is classical in Iwasawa theory (Coleman power series / Sinnott / Washington), no paper was found proving or formulating full multiplicative primitivity of cyclotomic units modulo a fixed prime $\ell$ all the way up a vertical $\mathbb{Z}_p$-tower.

---

### Question 4: Recent (2025–2026) Breakthroughs on Full Multiplicative Order in Towers of Finite Fields

* **Verdict:** **No 2025–2026 paper proves unconditional full multiplicative order (primitivity) for explicit elements across an infinite tower of finite fields.** Doing so for any fixed recursive tower over $\mathbb{F}_q$ remains blocked by the same number-theoretic barrier as Artin's primitive root conjecture (controlling power-freeness at prime divisors of $q^{d_n}-1$ such as Fermat or Mersenne numbers).

* **Leandro Cagliero, Allen Herman, and Fernando Szechtman, *"Artin-Schreier towers of finite fields"* (arXiv:2405.10159v3, Feb 2025; *Finite Fields Appl.* 103, 2025, 102606)**
  * **URL:** https://arxiv.org/abs/2405.10159
  * **Relevance:** The closest 2025–2026 result on exact multiplicative orders in towers: proves the **exact structural reduction** $O(c_i) = O(a_i) = \prod_{j} \mathrm{ord}(c_j \bmod L_{j-1}^\times)$ in the Artin-Schreier / Conway tower for all primes $p$, reducing full order in the tower to relative order $N_j = (p^{p^{j+1}}-1)/(p^{p^j}-1)$ at each step, without overcoming the open problem of proving $\mathrm{ord}(c_j \bmod L_{j-1}^\times) = N_j$ unconditionally for all $j$.

* **Soniya Takshak, Giorgos Kapetanakis, and R. K. Sharma, *"$\mathbb{F}_q$-primitive points on varieties over finite fields"* (*Finite Fields Appl.* 102, 2025, 102582)**
  * **URL:** https://doi.org/10.1016/j.ffa.2025.102582
  * **Relevance:** Uses character-sum / Vinogradov-sieve methods to prove **existence** (not explicit tower formulas) of primitive elements on varieties over finite fields for sufficiently large $q$.

* **Benjamin E. Diamond and Jim Posen, *"Succinct Arguments over Towers of Binary Fields"* (*EUROCRYPT 2025*, LNCS 15604, pp. 97–127) & Noor Athamnah, Noga Ron-Zewi, and Ron D. Rothblum, *"Linear Prover IOPs in Log Star Rounds"* (*TCC 2025*)**
  * **URLs:** https://doi.org/10.1007/978-3-031-91134-7_4 and https://doi.org/10.1007/978-3-032-12287-2_12
  * **Relevance:** Major 2025–2026 activity on Wiedemann/Conway binary tower fields ($\mathcal{T}_\iota$, "Binius"), but focused on additive/basis arithmetic, Cantor additive FFTs, and sumcheck IOPs rather than multiplicative primitivity of the tower generators.
[gaslamp] job: gm-20261021-014254-8abd · session: 7cd4248a-e3e9-457b-8658-bc0938e9ad96 · resume: gaslamp gemini --resume 7cd4248a-e3e9-457b-8658-bc0938e9ad96 · model: gemini-4-argon · tok: 2233k→24k
