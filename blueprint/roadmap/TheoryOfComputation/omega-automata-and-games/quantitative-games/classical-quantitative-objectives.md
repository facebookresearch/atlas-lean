# Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives

Let the colours be integer weights, $\rho = \rho_0 \rho_1 \rho_2 \cdots \in \mathbb{Z}^\omega$. The classical objectives of
[quantitative games](quantitative-games-and-values.md), which Max maximizes and Min minimizes, are:

- *shortest path*, over $\mathbb{Z} \cup \{\mathrm{Win}\}$: $\mathrm{ShortestPath}(\rho) = \sum_{i<k} \rho_i$ for the first $k$ with $\rho_k = \mathrm{Win}$, and $+\infty$ if
  $\mathrm{Win}$ never occurs;
- *mean payoff*: $\mathrm{MeanPayoff}^+(\rho) = \limsup_k \frac1k \sum_{i<k} \rho_i$ and $\mathrm{MeanPayoff}^-(\rho) = \liminf_k \frac1k \sum_{i<k} \rho_i$;
- *total payoff*: $\mathrm{TotalPayoff}(\rho) = \limsup_n \sum_{i<n} \rho_i$;
- *energy*: $\mathrm{Energy}(\rho) = \inf\{\ell \in \mathbb{N} : \forall k,\ \ell + \sum_{i<k} \rho_i \ge 0\}$, the least initial budget keeping every partial sum
  non-negative ($+\infty$ if there is none) (here the player who wants the budget small is Min, so energy games are stated with the roles swapped);
- *discounted payoff* with discount factor $\lambda \in (0, 1)$: $\mathrm{DiscountedPayoff}_\lambda(\rho) = (1 - \lambda) \sum_{i \ge 0} \lambda^i \rho_i$, which
  exists for bounded weights and satisfies $\mathrm{DiscountedPayoff}_\lambda(\rho) = (1 - \lambda)\rho_0 + \lambda\, \mathrm{DiscountedPayoff}_\lambda(\rho_1 \rho_2 \cdots)$.

A game with weights in $[-W, W]$, for an integer $W \ge 1$, on $n$ vertices and $m$ edges is the input to the algorithms for these objectives; a
*mean-payoff game* (and similarly for the other objectives) is a quantitative game whose condition is the objective applied to
the sequence of edge weights of a play.

## Depends on

- [Quantitative games and their values](quantitative-games-and-values.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 1 (N. Fijalkow, "Introduction"): Section 1.9, "Five classical quantitative objectives" (shortest path, mean payoff, total payoff, energy and discounted payoff); that chapter writes the discounted payoff without the factor $1 - \lambda$.
- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.2 (the dual pair $\mathrm{MeanPayoff}^{\pm}$ and the energy objective) and Section 5.3 (the normalized discounted payoff with the factor $1 - \lambda$ and its recursive form).
