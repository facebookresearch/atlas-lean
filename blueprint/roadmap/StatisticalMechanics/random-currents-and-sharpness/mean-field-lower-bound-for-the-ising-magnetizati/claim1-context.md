# Outside part of a gated double-current sum

Let $G = (V, E)$ be a finite simple graph, $\beta \in \mathbb{R}$, $J$ real couplings, $S \subseteq V$, $P$ a property of currents and $B, D \subseteq V$;
a current $n$ assigns a multiplicity $n_e \in \mathbb{N}$ to every edge $e \in E$, its [sources](../random-currents-and-the-switching-lemma/sources.md) $\partial n$ are the vertices of odd total incident multiplicity, and its [weight](../random-currents-and-the-switching-lemma/weight.md) is $w(n) = \prod_{e \in E} (\beta J_e)^{n_e}/n_e!$. For two currents $b_1, b_2$ on the edges of $G$ not having both endpoints in $S$, with $\bar b_1, \bar b_2$ their
[extensions by zero](b-full.md), this is

$$\mathbf 1_{\partial \bar b_1 = B}\, w(\bar b_1) \cdot \mathbf 1_{\partial \bar b_2 = D}\, w(\bar b_2) \cdot \mathbf 1_{P(\bar b_1 + \bar b_2)}.$$
