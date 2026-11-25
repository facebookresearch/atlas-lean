# Random-current cut mass of a vertex set

Let $G = (V, E)$ be a finite simple graph, $\beta \in \mathbb{R}$, $J$ real couplings, $g \in V$ and $S \subseteq V$; a current $n$ assigns a multiplicity $n_e \in \mathbb{N}$ to every edge $e \in E$, its [sources](../random-currents-and-the-switching-lemma/sources.md) $\partial n$ are the vertices of odd total incident multiplicity, and its [weight](../random-currents-and-the-switching-lemma/weight.md) is $w(n) = \prod_{e \in E} (\beta J_e)^{n_e}/n_e!$. The cut mass of $S$ is

$$\frac{1}{Z^2} \sum_{\partial n_1 = \partial n_2 = \emptyset} w(n_1)\, w(n_2)\, \mathbf 1_{\{v : v \not\leftrightarrow g \text{ in } n_1 + n_2\} = S},$$

with $Z = \sum_{\partial n = \emptyset} w(n)$ the sourceless current sum.
