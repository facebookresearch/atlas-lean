# Bond term: ghost-graph disconnection sum for a bond covariance

Let $G = (V, E)$ be a finite simple graph, $\beta, h \in \mathbb{R}$, $J$ real couplings, $o \in V$ and $e$ a pair of vertices,
and let $G^+$ be the [graph with a ghost vertex](../random-currents-and-the-switching-lemma/with-ghost.md) $\mathfrak g$ joined to every vertex, with coupling $J$ on the edges of $G$ and $h$ on the ghost edges; currents, [sources](../random-currents-and-the-switching-lemma/sources.md) and [weights](../random-currents-and-the-switching-lemma/weight.md) $w(n) = \prod_e (\beta J^+_e)^{n_e}/n_e!$ are taken on $G^+$. The bond term is

$$\sum_{\partial n_1 = S_e,\ \partial n_2 = \emptyset} w(n_1)\, w(n_2)\, \mathbf 1_{o \not\leftrightarrow \mathfrak g \text{ in } n_1 + n_2},$$

with $S_e$ the [ghost source set](hca-bond-source.md) of $e$.
