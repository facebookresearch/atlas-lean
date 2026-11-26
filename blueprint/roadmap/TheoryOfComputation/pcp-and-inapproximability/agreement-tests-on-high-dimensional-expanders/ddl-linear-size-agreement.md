# Dikstein–Dinur–Lubotzky: linear-size low-acceptance agreement tests

For every $\varepsilon > 0$ there exist $k$ and a family $\mathcal{F}_n$ of $k$-subsets of $[n]$ with $|\mathcal{F}_n| = O(n)$ and an agreement test on $\mathcal{F}_n$ (a uniformly random pair $s_1, s_2 \in \mathcal{F}_n$ with $|s_1 \cap s_2| = \sqrt{k}$, accepting iff $f_{s_1}, f_{s_2}$ agree on $s_1 \cap s_2$) such that for every alphabet $\Sigma$ and every ensemble $\{f_s\}$,

$$
\operatorname{Agr}(\{f_s\}) > \varepsilon \implies \exists\, G : [n] \to \Sigma,\quad \Pr_{s \in \mathcal{F}_n}\bigl[f_s \overset{0.99}{\approx} G|_s\bigr] \ge \operatorname{poly}(\varepsilon),
$$

where $\overset{0.99}{\approx}$ means agreement on at least $99\%$ of the coordinates of $s$.

## Proof sketch

Take $\mathcal{F}_n$ to be the top faces of the symplectic-building quotients without small connected covers. Their swap cocycle expansion, combined with the reduction of low-acceptance agreement to cocycle expansion of the swap complex in the absence of small covers, yields the list-decoding statement; the bounded degree gives linear size.

## Depends on

- [Agreement tests for ensembles of local functions](agreement-test.md)

## Proof depends on

- [Dikstein–Dinur–Lubotzky: bounded-degree complexes without small connected covers](../../../Combinatorics/polytopes-simplicial-complexes/coboundary-and-cosystolic-expansion/ddl-symplectic-no-covers.md)
- [Bafna–Minzer / Dikstein–Dinur characterization of low-soundness direct product testing](bafna-minzer-characterization.md)

## Sources

- Y. Dikstein, I. Dinur, A. Lubotzky, "Low acceptance agreement tests via bounded-degree symplectic HDXs", FOCS (2024), arXiv:2402.01078.
- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", arXiv:2308.09582 (2023), ECCC TR23-119.
