# Regular and permutation ROBPs with one accept vertex, and hitting set generators

A standard-order ROBP (layers $V_0,\dots,V_n$ of width $w$, two labeled edges from each vertex to the next layer) is **regular** if every vertex of $V_i$, $i\ge 1$, has exactly two incoming edges, and a **permutation** ROBP if moreover for each $i$ and each bit $b$ the edges labeled $b$ from $V_{i-1}$ to $V_i$ form a bijection. Width may be unbounded (a function of $n$ or arbitrary), and one often restricts to programs with a single accept vertex $v_{\mathrm{acc}}\in V_n$.

For a class $\mathcal{F}$ of functions $f:\{0,1\}^n\to\{0,1\}$, an **$\varepsilon$-hitting set generator** (HSG) with seed length $r$ is a map $H:\{0,1\}^r\to\{0,1\}^n$ such that every $f\in\mathcal{F}$ with $\mathbb{E}[f]\ge\varepsilon$ satisfies $f(H(y))=1$ for some seed $y$; it is explicit if computable in space $O(r)$. HSGs suffice to derandomize one-sided error, and the image of any $\varepsilon$-PRG is an $\varepsilon'$-hitting set for every $\varepsilon'\gt\varepsilon$.

## Depends on

- [Pseudorandom generators with logarithmic seed derandomize BPP](../derandomization/pseudorandom-generators-with-logarithmic-seed.md)

## Sources

- Andrej Bogdanov, William M. Hoza, Gautam Prakriya and Edward Pyne, "Hitting Sets for Regular Branching Programs", CCC (2022), ECCC TR21-143.
- Kuan Cheng and William M. Hoza, "Hitting Sets Give Two-Sided Derandomization of Small Space", CCC (2020); Theory of Computing 18(21) (2022), ECCC TR20-016.
- Edward Pyne and Salil Vadhan, "Pseudodistributions That Beat All Pseudorandom Generators", CCC (2021); Theory of Computing 22(3) (2026), ECCC TR21-019.
