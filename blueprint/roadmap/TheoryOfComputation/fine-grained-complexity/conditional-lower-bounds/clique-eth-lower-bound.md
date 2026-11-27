# Under ETH, Clique has no f(k)·n^{o(k)} algorithm

Assuming ETH, there is no algorithm deciding whether an $N$-vertex graph has a clique of size $k$ in time $f(k)\cdot N^{o(k)}$ for any computable function $f$; the same holds for Independent Set, and in particular neither problem is fixed-parameter tractable under ETH.

## Proof sketch

Suppose Clique is solvable in time $f(k)\,N^{k/s(k)}$ with $s$ nondecreasing and unbounded. Given an $n$-vertex instance of 3-Colouring, split its vertices into $k\approx f^{-1}(n)$ groups and build a graph whose vertices are the proper 3-colourings of single groups, two of them adjacent iff they lie in different groups and are compatible on the edges between those groups. It has at most $k\cdot3^{n/k}=2^{o(n)}$ vertices, its $k$-cliques are exactly the proper 3-colourings of the whole graph, and the assumed algorithm runs on it in time $2^{o(n)}$ (computability of $f$ is used to choose $k$ within the time budget). This contradicts the ETH lower bound for 3-Colouring.

## Depends on

- [Parameterized Clique](../../complexity-classes/parameterized-complexity/clique-param.md)
- [Exponential Time Hypothesis and Strong Exponential Time Hypothesis](../fine-grained-hypotheses/exponential-time-hypothesis-and-strong.md)
- [Fixed-parameter tractable problems](../../complexity-classes/parameterized-complexity/fpt.md)

## Proof depends on

- [ETH lower bounds for classical graph problems](../linear-size-reductions-and-graph-lower-bounds/eth-lower-bounds-for-graph-problems.md)

## Sources

- Marek Cygan et al., "Parameterized Algorithms", Springer, 2015, Theorem 14.21 and its proof.
