# Stochastic reachability games reduce to simple stochastic games

Every [stochastic reachability game](stochastic-arenas-and-games.md) $\mathcal{G}$ with rational probabilities can be transformed in polynomial time into a
simple stochastic game $\mathcal{G}'$ with $O(n(\log n + k))$ vertices, $k$ being the number of bits of the probabilities, that contains
the vertices of $\mathcal{G}$ and gives each of them the same value. Moreover solving (non-stochastic)
[discounted-payoff games](discounted-payoff-values-are-the-unique-fixed-point.md) reduces in polynomial time to solving stochastic reachability games: after
scaling the weights into $[0, 1]$, each edge $u \xrightarrow{w} v$ is redirected to a new random vertex that moves to $v$ with probability $\lambda$,
to a sink $\mathrm{Win}$ with probability $(1 - \lambda) w$ and to a sink $\mathrm{Lose}$ with probability $(1 - \lambda)(1 - w)$.

## Depends on

- [Stochastic arenas, stochastic reachability games and simple stochastic games](stochastic-arenas-and-games.md)
- [Shortest-path, mean-payoff, total-payoff, energy and discounted-payoff objectives](classical-quantitative-objectives.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 7 (N. Bertrand, P. Bouyer, N. Fijalkow and M. Skomra, "Stochastic games"): Section 7.2, Lemma 7.3 (reduction to normalised games) and Lemma 7.4 (reduction from stochastic games to simple stochastic games), and Section 7.6, Theorem 7.16 (reducing discounted-payoff games to stochastic reachability games) with its proof.
