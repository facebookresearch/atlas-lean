# Discounted-payoff values are the unique fixed point of a contraction

For a finite discounted-payoff game (the [discounted objective](classical-quantitative-objectives.md) with factor $\lambda \in (0,1)$), the operator on
$V \to \mathbb{R}$ defined by $\mathcal{O}(\mu)(u) = \max\{\lambda \mu(v) + (1 - \lambda) w : u \xrightarrow{w} v\}$ at vertices of Max and the same with $\min$ at vertices of
Min is a contraction with factor $\lambda$ for the sup norm, so it has a unique fixed point. That fixed point is the vector of
discounted-payoff values; the game is determined, and choosing at each vertex an edge that attains the max (respectively min) in
the fixed-point equation gives positional optimal strategies for both players.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)
- [Quantitative games and their values](quantitative-games-and-values.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.3, Fact 5.3 and Lemma 5.7 (values as unique fixed point) with its proof, using the Banach fixed-point theorem (Theorem 1.5).
