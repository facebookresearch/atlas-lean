# Pseudo-polynomial value iteration for mean-payoff games

For a finite [mean-payoff game](classical-quantitative-objectives.md) with $n$ vertices, $m$ edges and weights in $[-W, W]$, let $\mathrm{val}_k(u)$ be the value of
the game that stops after $k$ steps and pays the sum of the weights. Then $\lim_k \frac1k \mathrm{val}_k = \mathrm{val}$, and computing
$\mathrm{val}_k$ for $k = 4n^3 W$ by $k$ rounds of the one-step operator determines the mean-payoff values in time $O(n^3 m W)$; deciding
whether $\mathrm{val}(u) \ge c$ for an integer threshold $c$ takes time $O(n^2 m W)$ (Zwick and Paterson). Both bounds are pseudo-polynomial:
polynomial when the weights are written in unary.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Proof depends on

- [Mean-payoff values are rationals with small denominators](mean-payoff-values-are-rationals-with-small-denominators.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.2, "A first value iteration algorithm", Corollary 5.2 and Theorem 5.4 with its proof, and the bibliographic references crediting the algorithm to U. Zwick and M. Paterson, *Theoretical Computer Science* 158 (1996).
