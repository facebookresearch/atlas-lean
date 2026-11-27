# Discounted payoff approximates mean payoff

Let $\mathcal{G}$ be a finite [mean-payoff game](classical-quantitative-objectives.md) with $n$ vertices and weights in $[-W, W]$, and $\mathcal{G}_\lambda$ the
discounted-payoff game with discount factor $\lambda \in (0, 1)$ on the same arena. Then

$$\lVert \mathrm{val} - \mathrm{val}_\lambda \rVert_\infty \le (1 - \lambda) \cdot 2nW.$$

For $n \ge 2$ and $\lambda = 1 - 1/(4n^2(n-1)W)$, whose description has polynomially many bits, this bound and the bound on the denominators of
mean-payoff values let the discounted values determine the mean-payoff values, which reduces solving mean-payoff games to solving
discounted-payoff games.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Proof depends on

- [Energy, mean-payoff and total-payoff games are positionally determined](positional-determinacy-of-mean-payoff-and-energy-games.md)
- [Discounted-payoff values are the unique fixed point of a contraction](discounted-payoff-values-are-the-unique-fixed-point.md)
- [Mean-payoff values are rationals with small denominators](mean-payoff-values-are-rationals-with-small-denominators.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.3, Theorem 5.10 (discounted-payoff approximation) with its proof and the corollary on the choice of $\lambda$ that follows it.
