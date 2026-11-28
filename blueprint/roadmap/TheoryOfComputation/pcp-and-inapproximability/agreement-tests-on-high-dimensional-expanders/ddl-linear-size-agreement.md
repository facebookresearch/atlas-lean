# Dikstein–Dinur–Lubotzky: linear-size low-acceptance agreement tests

For every $\varepsilon > 0$ there exist $c > 0$, $k$ and a family $\mathcal{F}_n$ of $k$-subsets of $[n]$ with $|\mathcal{F}_n| = O(n)$ and an agreement test on $\mathcal{F}_n$ (a uniformly random pair $s_1, s_2 \in \mathcal{F}_n$ with $|s_1 \cap s_2| = \sqrt{k}$, accepting iff $f_{s_1}, f_{s_2}$ agree on $s_1 \cap s_2$) such that for every alphabet $\Sigma$ and every ensemble $\{f_s\}$,

$$
\operatorname{Agr}(\{f_s\}) > \varepsilon \implies \exists\, G : [n] \to \Sigma,\quad \Pr_{s \in \mathcal{F}_n}\bigl[f_s \overset{0.99}{\approx} G|_s\bigr] \ge \varepsilon^{c},
$$

where $\overset{0.99}{\approx}$ means agreement on at least $99\%$ of the coordinates of $s$.

## Proof sketch

Take $\mathcal{F}_n$ to be the $k$-faces of the symplectic-building quotients that have no connected $m'$-sheeted covers for $1 < m' \le m$, with $m$ at least the cover size $\operatorname{poly}(1/\varepsilon)$ below, and that are swap cocycle expanders. Dikstein and Dinur's cover agreement theorem (Dikstein–Dinur, Theorem 1.3, formally Theorem 3.1; restated as Dikstein–Dinur–Lubotzky, Theorem 1.4 and Theorem 4.10) states: for $k \in \mathbb{N}$ and $\varepsilon > \Omega(1/\log k)$, on a high-dimensional expander of sufficiently large dimension with sufficiently good swap cocycle expansion, every ensemble with $\operatorname{Agr}(\{f_s\}) > \varepsilon$ is explained on at least a $\operatorname{poly}(\varepsilon)$-fraction of $k$-faces by a function $G : Y(0) \to \Sigma$ on some $\ell$-sheeted cover $\rho : Y \to X$ with $\ell = \operatorname{poly}(1/\varepsilon)$. Since $X$ has no small connected covers, $Y$ is a disjoint union of copies of $X$, and restricting $G$ to the copy that explains the most faces gives the bound (Dikstein–Dinur–Lubotzky, Section 1.2 and the proof of Theorem 4.11). Connected covers are the obstruction recorded on the characterization page, and the bounded degree gives linear size.

## Depends on

- [Agreement tests for ensembles of local functions](agreement-test.md)

## Proof depends on

- [Dikstein–Dinur–Lubotzky: bounded-degree complexes without small connected covers](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/ddl-symplectic-no-covers.md)
- [Bafna–Minzer / Dikstein–Dinur characterization of low-soundness direct product testing](bafna-minzer-characterization.md)

## Sources

- Y. Dikstein, I. Dinur, A. Lubotzky, "Low acceptance agreement tests via bounded-degree symplectic HDXs", FOCS (2024), arXiv:2402.01078 (Theorems 1.1-1.4, 4.10 and 4.11; Section 1.2).
- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", arXiv:2308.09582 (2023), ECCC TR23-119 (Theorem 1.3; formal statement Theorem 3.1).
