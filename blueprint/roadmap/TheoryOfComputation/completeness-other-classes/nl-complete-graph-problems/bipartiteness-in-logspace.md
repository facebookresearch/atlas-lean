# Bipartiteness is in L and non-bipartiteness is logspace-equivalent to undirected connectivity

For undirected graphs $G$ given by adjacency matrices, non-bipartiteness and $\mathrm{USTCON}$ are logspace many-one reducible to each other, and hence $\mathrm{BIPARTITE}=\{G : G$ is $2$-colourable$\}\in\mathsf{L}$.

## Proof sketch

$G$ is non-bipartite iff some vertex $v$ has $(v,0)$ connected to $(v,1)$ in the bipartite double cover $G\times K_2$; taking $n$ disjoint copies of the double cover, one per vertex $v$, and joining a new vertex $s$ to $(v,0)$ and a new vertex $t$ to $(v,1)$ in the $v$-th copy gives a single USTCON instance $(s,t)$. Conversely, USTCON reduces to non-bipartiteness by subdividing every edge (making the graph bipartite) and adding an odd path between $s$ and $t$. Membership in $\mathsf{L}$ follows from Reingold's theorem.

## Depends on

- [Undirected s-t connectivity as a decision problem](../../polynomial-time-problems/undirected-s-t-connectivity/ustcon-dec.md)
- [Deterministic logarithmic space](../../complexity-classes/time-and-space-complexity-classes/log-space.md)
- [Log-space many-one reductions](../../complexity-classes/time-and-space-complexity-classes/log-space-red.md)

## Proof depends on

- [Undirected ST-connectivity is in L (Reingold)](../../polynomial-time-problems/undirected-s-t-connectivity/ustcon-in-l.md)
- [Log-space computable functions](../../complexity-classes/time-and-space-complexity-classes/log-space-computable.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Exercise 5.16.
