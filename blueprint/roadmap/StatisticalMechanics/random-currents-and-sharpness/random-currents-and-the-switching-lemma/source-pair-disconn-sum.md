# Double-current sum restricted to disconnection

Let $G = (V, E)$ be a finite simple graph, $\beta \in \mathbb{R}$, $J$ real couplings, $A, B \subseteq V$ and $u, v \in V$; a current $n$ assigns a multiplicity $n_e \in \mathbb{N}$ to every edge, its [sources](sources.md) $\partial n$ are the vertices of odd total incident multiplicity, and its [weight](weight.md) is $w(n) = \prod_{e \in E} (\beta J_e)^{n_e}/n_e!$. This is

$$\sum_{\partial n_1 = A,\ \partial n_2 = B} w(n_1)\, w(n_2)\, \mathbf 1_{u \not\leftrightarrow v \text{ in } n_1 + n_2},$$

where $u \leftrightarrow v$ in $n$ means that $u$ and $v$ are joined by a path of edges carrying positive current.
