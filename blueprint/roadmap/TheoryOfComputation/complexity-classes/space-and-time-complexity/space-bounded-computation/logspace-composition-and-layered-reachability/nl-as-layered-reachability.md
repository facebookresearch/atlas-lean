# Every NL language is uniform layered reachability

For every $L\in\mathsf{NL}$ there are a logspace computable family of layered directed graphs $G_x$, with polynomially many vertices arranged in layers $0,\dots,p(|x|)$ and arcs only between consecutive layers, and two distinguished vertices $s_x,t_x$, such that $x\in L$ iff $t_x$ is reachable from $s_x$ in $G_x$; the adjacency of $G_x$ is computable from $x$ by a logspace machine that queries the input in place.

## Proof sketch

Take the configuration graph of the NL machine (configurations encoded compactly in $O(\log n)$ bits), time-stamp configurations with a polynomial clock to make it layered, and add idle arcs at the accepting configuration so that early acceptance reaches the last layer.

## Depends on

- [The complexity class NL](../../../time-and-space-complexity-classes/nl.md)
- [Directed $s$-$t$ connectivity](../../../../completeness-other-classes/directed-s-t-connectivity/stcon-dec.md)

## Proof depends on

- [Configuration graph of a space-bounded machine](../../configuration-graph-of-a-space-bounded-machine.md)
- [Logarithmic-space computable functions compose](logspace-functions-compose.md)

## Sources

- Sanjeev Arora and Boaz Barak, "Computational Complexity - A Modern Approach", Cambridge University Press, 2009.
