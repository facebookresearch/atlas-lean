# The Ising Hamiltonian as the energy with unit coupling

Let $G = (V, E)$ be a finite simple graph, $h \in \mathbb{R}$ and $s$ a spin configuration, with spins $\sigma_x = +1$ if $s(x)$ is true and $\sigma_x = -1$ otherwise.
The [Ising Hamiltonian](../the-finite-volume-ising-gibbs-measure/hamiltonian.md) equals the Ising
energy with coupling $J = 1$ and field $h$ of the region of all vertices, written as half a sum over
ordered adjacent pairs:

$$-\sum_{\{x, y\} \in E} \sigma_x \sigma_y - h \sum_{x \in V} \sigma_x = -\frac{J}{2} \sum_{x \in V} \sum_{y \in V} [x \sim y]\, \sigma_x \sigma_y - h \sum_{x \in V} \sigma_x, \qquad J = 1.$$
