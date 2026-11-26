# Minzer–Zheng: near-optimal alphabet-soundness tradeoff for 2-query PCPs

For every $\varepsilon > 0$, for every sufficiently large power of two $q$, and for every $\delta > 0$, it is NP-hard to distinguish whether a given $2$-prover $1$-round projection game with alphabet size $q$ has value at least $1 - \delta$ or value at most $1/q^{1 - \varepsilon}$. Consequently, under quasi-polynomial-time reductions, Boolean quadratic programming is NP-hard to approximate within $(\log n)^{1 - o(1)}$.

## Proof sketch

The construction composes an outer PCP with an inner test based on the Grassmann/bilinear agreement machinery of the $2$-to-$2$ theorem, replacing the abelian-group based soundness reduction of Chan by a list-decoding analysis of subspace tests over $\mathbb{F}_2$ with alphabet $q = 2^t$; the global-hypercontractivity based expansion of pseudorandom sets gives soundness $q^{-1+\varepsilon}$.

## Depends on

- [d-to-d games and 2-to-2 constraints](d-to-d-games.md)

## Proof depends on

- [The 2-to-2 Games Theorem (imperfect completeness)](two-to-two-theorem.md)

## Sources

- D. Minzer, K. Z. Zheng, "Near optimal alphabet-soundness tradeoff PCPs", STOC (2024), arXiv:2404.07441.
