# Parity games reduce to mean-payoff games

Let $\mathcal{G}$ be a [parity game](../parity-games/parity-game.md) with $n$ vertices and priorities $c(e) \in \{1, \dots, d\}$ on the edges (max-parity,
even priorities good for Eve; priorities on edges rather than on positions as in the linked definition, which changes no result here). The [mean-payoff game](classical-quantitative-objectives.md) on the same arena with weights $c'(e) = (-n)^{c(e)}$
satisfies: Eve wins $\mathcal{G}$ from $v$ if and only if the mean-payoff value of $v$ is at least $0$. The weights have $O(d \log n)$
bits; after first relabelling the distinct priorities in increasing order by the least positive integers of the same parities, so that $d \le 2m$
for $m$ edges, solving parity games reduces in polynomial time to solving mean-payoff games with threshold $0$. The point is that on a
simple cycle the weight of the largest priority dominates the sum of all the others.

## Depends on

- [Parity game](../parity-games/parity-game.md)
- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Proof depends on

- [Finite parity games are positionally determined](../parity-games/finite-parity-games-are-positionally-determined.md)
- [Energy, mean-payoff and total-payoff games are positionally determined](positional-determinacy-of-mean-payoff-and-energy-games.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.2, Theorem 5.3 with its proof.
