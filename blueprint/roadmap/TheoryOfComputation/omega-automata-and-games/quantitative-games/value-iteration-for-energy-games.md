# Value iteration for energy games

For a finite energy game (the [energy objective](classical-quantitative-objectives.md), Min wanting a small initial budget) with $n$ vertices, $m$ edges and
weights in $[-W, W]$, the energy values form the least fixed point of the monotone operator on $V \to \mathbb{N} \cup \{\infty\}$ given by
$\mathcal{O}(\mu)(u) = \min\{\max(\mu(v) - w, 0) : u \xrightarrow{w} v\}$ at vertices of Min and $\max\{\cdots\}$ at vertices of Max, and a value iteration
algorithm computes them in time $O(nmW)$, every finite energy value being at most $nW$. By the
[interreduction with mean-payoff games](mean-payoff-games-and-energy-games.md) this decides $\mathrm{val}(u) \ge 0$ for every vertex $u$ of a mean-payoff game in time $O(nmW)$.

## Depends on

- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Proof depends on

- [Mean-payoff games and energy games are interreducible](mean-payoff-games-and-energy-games.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 5 (N. Fijalkow and B. Monmege, "Games with payoffs"): Section 5.2, "A second value iteration algorithm using energy", Lemma 5.4 and Theorem 5.5 with its proof.
