# Every edge is essential to clique separators

For $2\le k\le n$, every Boolean function on the $\binom n2$ edge variables that is $1$ on all graphs containing a $k$-clique and $0$ on all $(k-1)$-colourable graphs depends on every edge variable. Consequently every monotone circuit (fan-in two) separating $k$-clique graphs from $(k-1)$-colourable graphs has at least $\binom n2-1$ gates.

## Proof sketch

Colour a $k$-set containing the edge $\{u,v\}$ injectively except that $u,v$ share a colour; its complete multipartite graph is $(k-1)$-colourable, and adding $\{u,v\}$ creates a $k$-clique.

## Depends on

- [The clique function CLIQUE(n, s) on adjacency-matrix bits](../monotone-circuit-lower-bound-for-clique/clique-of-size.md)

## Proof depends on

- [A function depending on all inputs needs n - 1 binary gates](../circuit-models-synthesis-and-lower-bounds/circuit-models-and-classes/circuit-models-and-complexity-measures/n-minus-one-binary-gates-for-essential-inputs.md)

## Sources

- Stasys Jukna, "Boolean Function Complexity: Advances and Frontiers", Springer, 2012.
