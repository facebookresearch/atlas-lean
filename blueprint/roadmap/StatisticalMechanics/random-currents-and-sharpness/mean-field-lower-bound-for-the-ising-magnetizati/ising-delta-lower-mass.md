# Lower mass of the four-source bound

Let $G = (V, E)$ be a finite simple graph, $\beta \in \mathbb{R}$, $J$ real couplings and $o, x, y, g \in V$; a current $n$ assigns a multiplicity $n_e \in \mathbb{N}$ to every edge $e \in E$, its [sources](../random-currents-and-the-switching-lemma/sources.md) $\partial n$ are the vertices of odd total incident multiplicity, and its [weight](../random-currents-and-the-switching-lemma/weight.md) is $w(n) = \prod_{e \in E} (\beta J_e)^{n_e}/n_e!$. The lower mass is

$$L(o, x, y, g) = \sum_{\substack{S \subseteq V \\ o, x \in S,\ y, g \notin S}} \langle \sigma_o \sigma_x \rangle_{\beta, J|_S} \sum_{\partial n_1 = \partial n_2 = \emptyset} w(n_1)\, w(n_2)\, \mathbf 1_{\{v : v \not\leftrightarrow g \text{ in } n_1 + n_2\} = S},$$

where $\langle \cdot \rangle_{\beta, J|_S}$ is the zero-field Ising expectation on $G$ with the
[coupling restricted to $S$](coupling-in.md) (and $\sigma_o \sigma_x$ means $\sigma_o$ when $x = o$).
