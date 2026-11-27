# Connectivity of an undirected graph is in L

$\mathrm{UCONN}$, the language of undirected graphs $G$ in which every two vertices are joined by a path, (the graph with no vertices counts as connected) logspace-reduces to $\mathrm{USTCON}$ and hence lies in $\mathsf{L}$.

## Proof sketch

Graphs with at most one vertex are connected, so let $n\ge 2$. Take disjoint copies $G_1,\dots,G_{n-1}$ of $G$ on vertices $1,\dots,n$ and identify vertex $i+1$ of $G_i$ with vertex $i+1$ of $G_{i+1}$. Since consecutive copies meet only there, vertex $1$ of $G_1$ is connected to vertex $n$ of $G_{n-1}$ iff vertex $i$ is connected to $i+1$ in $G$ for every $i$, i.e. iff $G$ is connected. The construction is logspace, and Reingold's theorem finishes.

## Depends on

- [Undirected s-t connectivity as a decision problem](../../polynomial-time-problems/undirected-s-t-connectivity/ustcon-dec.md)
- [Deterministic logarithmic space](../../complexity-classes/time-and-space-complexity-classes/log-space.md)

## Proof depends on

- [Undirected ST-connectivity is in L (Reingold)](../../polynomial-time-problems/undirected-s-t-connectivity/ustcon-in-l.md)
- [Log-space computable functions](../../complexity-classes/time-and-space-complexity-classes/log-space-computable.md)

## Sources

- Oded Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008, Theorem 5.6.
