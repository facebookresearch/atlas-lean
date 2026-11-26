# Stochastic arenas, stochastic reachability games and simple stochastic games

A *stochastic arena* is a graph whose vertices are partitioned into those of Max, those of Min and *random* vertices, together with
a function $\delta$ giving each random vertex a probability distribution on its outgoing edges. Strategies map finite plays to
distributions on edges; a pair of strategies and an initial vertex induce a probability measure on infinite plays. A
*stochastic reachability game* has a sink $\mathrm{Win}$, and the payoff of a pair of strategies from $v$ is the probability of reaching
$\mathrm{Win}$; values and optimal strategies are as in [quantitative games](quantitative-games-and-values.md), and a strategy is *pure* if it
picks edges deterministically. The game is *normalised* if there is a unique almost-surely winning vertex $\mathrm{Win}$ and a unique
vertex $\mathrm{Lose}$ that is not positively winning, both sinks. A *simple stochastic game* (Condon) is a normalised stochastic
reachability game in which every vertex other than $\mathrm{Win}$ and $\mathrm{Lose}$ has two successors and every random vertex moves to
each of them with probability $1/2$.

## Depends on

- [Quantitative games and their values](quantitative-games-and-values.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, arXiv:2305.10546v2, 2025, Chapter 7 (N. Bertrand, P. Bouyer, N. Fijalkow and M. Skomra, "Stochastic games"): Definitions 7.1 and 7.2, the paragraphs on strategies, reachability objectives and values that follow, Definition 7.4 (normalised games) and Definition 7.5 (binary and simple stochastic games).
