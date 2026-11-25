# Gated double-current sum over edge-indexed currents

Let $G = (V, E)$ be a finite simple graph, $\beta \in \mathbb{R}$, $J$ real couplings, $A, B \subseteq V$ and $P$ a property of currents; a current $n$ assigns a multiplicity $n_e \in \mathbb{N}$ to every edge $e \in E$, its [sources](../random-currents-and-the-switching-lemma/sources.md) $\partial n$ are the vertices of odd total incident multiplicity, and its [weight](../random-currents-and-the-switching-lemma/weight.md) is $w(n) = \prod_{e \in E} (\beta J_e)^{n_e}/n_e!$.
The gated double-current sum is

$$\sum_{\substack{n_1, n_2 \colon E \to \mathbb{N} \\ \partial n_1 = A,\ \partial n_2 = B}} w(n_1)\, w(n_2)\, \mathbf 1_{P(n_1 + n_2)}.$$
