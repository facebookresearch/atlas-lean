# Stochastic arenas, stochastic reachability games and simple stochastic games

A *stochastic arena* is a finite graph in which every vertex has an outgoing edge, whose vertices are partitioned into those of Max, those of Min and *random* vertices, together with
a function $\delta$ giving each random vertex a probability distribution on its outgoing edges. A strategy of a player maps each finite play ending at
one of that player's vertices to a distribution on the outgoing edges of that vertex; a pair of strategies and an initial vertex induce a probability measure on infinite plays. A
*stochastic reachability game* has a sink $\mathrm{Win}$, and the payoff of a pair of strategies from $v$ is the probability of reaching
$\mathrm{Win}$; values and optimal strategies are as in [quantitative games](quantitative-games-and-values.md), and a strategy is *pure* if it
picks edges deterministically. A vertex is *almost-surely winning* if Max has a strategy that reaches $\mathrm{Win}$ with probability $1$ against every
strategy of Min, and *positively winning* if Max has one that reaches it with positive probability against every strategy of Min. The game is *normalised* if there is a unique almost-surely winning vertex $\mathrm{Win}$ and a unique
vertex $\mathrm{Lose}$ that is not positively winning, both sinks. A *simple stochastic game* (Condon) is a normalised stochastic
reachability game in which every vertex other than $\mathrm{Win}$ and $\mathrm{Lose}$ has two outgoing edges and every random vertex moves to
each of them with probability $1/2$.

## Depends on

- [Quantitative games and their values](quantitative-games-and-values.md)

## Sources

- N. Fijalkow (ed.), *Games on Graphs: From Logic and Automata to Algorithms*, Cambridge University Press, 2026, doi:10.1017/9781009500678 (numbering of the version arXiv:2305.10546v2, 2025), Chapter 7 (N. Bertrand, P. Bouyer, N. Fijalkow and M. Skomra, "Stochastic games"): Definitions 7.1 and 7.2, the paragraphs on strategies, reachability objectives and values that follow, Definition 7.4 (normalised games) and Definition 7.5 (binary and simple stochastic games).
