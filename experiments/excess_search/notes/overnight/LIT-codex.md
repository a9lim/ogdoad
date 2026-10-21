[gaslamp] → codex · job cx-20261021-014253-c41d · watch: tail -f /Users/a9lim/.gaslamp/jobs/cx-20261021-014253-c41d/events.jsonl
(🔎) **Live search checked 21 October 2026.** Negative findings below mean “nothing located,” not a proof that no such work exists.

**1. Lenstra excess / 0–1–4 rule**

- **No published/preprint proof, disproof, boundedness theorem, or counterexample located** in the searched arXiv, OEIS, GitHub, CGSuite, blog, and MathOverflow material.
- **Computations extend substantially beyond 709.** The [OEIS sparse a-file](https://oeis.org/A380496/a380496.txt) contains 799 known entries among indices \(1,\ldots,1417\), reaching \(p=11827\). The [OEIS comments](https://oeis.org/A380496/internal) explicitly report \(m_{1459}=4\); this fits the rule.
- **Stronger current computational inventory:** Peeters’s [excess records, pinned to commit `9f7d67c`](https://github.com/DjangoPeeters/transfinite-nim-calculator/blob/9f7d67cf205a343266fe1cd37744715945af6ece/logs/excess_records.txt) contain **1,023 odd-prime values**, scattered through \(p=12281\); \(719\) remains the first missing prime. I parsed these records and checked every value against the proposed rule using the accompanying [Q-set records](https://github.com/DjangoPeeters/transfinite-nim-calculator/blob/9f7d67cf205a343266fe1cd37744715945af6ece/logs/q_set_records.txt): **zero discrepancies**. The only recorded 4s are at \(19,163,1459\). This verifies consistency of the published records; I did **not** recompute their finite-field calculations.

**2. Wiedemann and Conway towers**

- **Wiedemann:** no subsequent proof, disproof, or counterexample located. Popovych’s [2015 paper](https://journals.pnu.edu.ua/index.php/cmp/article/download/1401/1734/2952) supplies order restrictions and lower bounds, explicitly retaining the full-order question.
- **Directly relevant new Conway result:** Cagliero–Herman–Szechtman, *Artin-Schreier towers of finite fields*, [2024 preprint](https://arxiv.org/abs/2405.10159), [September 2025 publication](https://doi.org/10.1016/j.ffa.2025.102606). **Assessment:** genuine structural progress, not universal primitivity. Theorem 4.5 proves \(O(c_i)=O(a_i)\), except \(p=2,i=1\); Corollaries 4.7–4.9 give product formulas, conditional maximality, and lower bounds.
- **Important normalization:** in characteristic two, for \(i\ge2\), \(O(c_i)\mid N_1\cdots N_i=(|L_i|-1)/3\); the primitive candidate is \(c_0c_i\). The paper cites Popovych’s computational maximality through \(i=11\), rather than establishing all levels. See [Lemma 3.7 and §4](https://arxiv.org/html/2405.10159v2).

**3. The \(3\)-power Gauss-period tower / “vertical Artin”**

- **No all-\(k\) primitivity theorem, published counterexample, or explicitly named conjecture for this exact tower located.** I also found no matching established “vertical Artin conjecture” for these cyclotomic units.
- **Applicable partial result:** Breuer–Shparlinski, [*Lower bounds for periods of Ducci sequences*](https://arxiv.org/html/1909.04462), published 2020. Corollary 3.3 gives \(P(n)\ge\exp(c(p)\sqrt n)\) for \(n=p^k\); **it does not prove maximality**. Table 5.1 records \(P(9)=63\), \(P(27)=13797\), and \(P(81)=10871635887\), consistent with the proposed maximal formula.
- **Nearby but different conjecture:** Breuer’s [2020 preprint / 2021 paper](https://arxiv.org/html/2006.10344), §4, discusses Gao–Vanstone’s conjecture that \(\zeta+\zeta^{-1}\) is primitive when the conductor is a **safe prime** \(2r+1\), with \(r\) prime. **Assessment:** this is not the composite-conductor \(3^{k+1}\) tower. The paper’s main theorem detects nonprimitivity through quadratic-field arithmetic for certain prime conductors.

**4. Full-order breakthroughs in 2025–2026**

- **No matching breakthrough located** proving full multiplicative order at every level of the prescribed Wiedemann, Conway, or \(3\)-power cyclotomic towers. The directly relevant 2025 advance is the conditional/order-decomposition result above.
- **Adjacent positive result:** Gerardo Vega, [*A characterization and an explicit description of all primitive polynomials of degree two*](https://doi.org/10.1016/j.ffa.2025.102716), January 2026. **Assessment:** characterizes full-order quadratic generators; it does not establish primitivity of the fixed recursive generators in these questions.
- **Adjacent negative result:** Avnish Sharma, [arXiv:2608.07262v3](https://arxiv.org/abs/2608.07262v3), revised **18 October 2026**, proves nonexistence results and counterexamples to other prescribed-form primitive-polynomial conjectures. **Assessment:** relevant caution about recursive primitivity assumptions, but no counterexample to the three specific towers here.

[gaslamp] job: cx-20261021-014253-c41d · session: 01a15cfb-e014-7852-ad39-c3477b18c86e · resume: gaslamp codex --resume 01a15cfb-e014-7852-ad39-c3477b18c86e · tok: 2444k→8.0k
