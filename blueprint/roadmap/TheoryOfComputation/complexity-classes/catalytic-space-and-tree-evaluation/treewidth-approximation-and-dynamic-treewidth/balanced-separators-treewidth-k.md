# Balanced separators of size k+1 in graphs of treewidth at most k

Let $G$ be a graph with treewidth at most $k$ (it has a tree decomposition whose bags have size at most $k+1$). Then for every set $W\subseteq V(G)$ there is a set $S\subseteq V(G)$ with $|S|\le k+1$ such that every connected component of $G-S$ contains at most $|W|/2$ vertices of $W$. Such an $S$ (a bag of the decomposition) is a **balanced separator** of $W$. Contrapositively, a set $W$ with no balanced separator of size $k+1$ certifies $\operatorname{tw}(G) > k$; this is the certificate returned by approximation algorithms for treewidth.

## Proof sketch

Orient each edge $tt'$ of the decomposition tree towards the side containing more than $|W|/2$ vertices of $W$ outside the bags' intersection (if any side does). Some node $t$ has no outgoing edge; removing its bag $B_t$ leaves components each contained in the subtree beyond one neighbour of $t$, and each such side carries at most $|W|/2$ vertices of $W$ by the choice of $t$.

## Depends on

- [Tree-decomposition](../../../../GraphTheory/planar-graphs-and-minors/tree-width/tree-decomposition.md)
- [TREEWIDTH as a decision problem](../../../np-completeness/graph-coloring-and-partitioning/treewidth/treewidth-dec.md)

## Sources

- Hans L. Bodlaender, Pål Grønås Drange, Markus S. Dregi, Fedor V. Fomin, Daniel Lokshtanov and Michał Pilipczuk, "A c^k n 5-Approximation Algorithm for Treewidth", SIAM Journal on Computing 45(2) (2016), arXiv:1304.6321.
- Tuukka Korhonen, "A Single-Exponential Time 2-Approximation Algorithm for Treewidth", FOCS (2021), arXiv:2104.07463.
