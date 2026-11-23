# Random-cluster weight with a boundary wiring

Let $G = (V, E)$ be a finite simple graph, $C$ a simple graph on $V$, and $p, q \in \mathbb{R}$. The weight with boundary wiring $C$ of an assignment $\omega$ of open/closed states to the unordered pairs of vertices is

$$w^C(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)},$$

where $o(\omega)$ and $c(\omega)$ are the numbers of open and closed edges of $G$ and $k_C(\omega)$ is the [number of clusters under the wiring $C$](num-clusters-bc.md), the number of connected components of the graph on $V$ whose edges are the edges of $G$ open in $\omega$ together with the edges of $C$.
