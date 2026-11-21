# Ising model as a finite canonical ensemble

Let $G = (V, E)$ be a finite simple graph and $h \in \mathbb{R}$. The Ising model on $G$ with field $h$ is the finite canonical
ensemble whose microstates are the spin configurations $s \in \{\text{true}, \text{false}\}^V$, whose
energy is the [Ising Hamiltonian](../the-finite-volume-ising-gibbs-measure/hamiltonian.md) $H(s) = -\sum_{\{x, y\} \in E} \sigma_x \sigma_y - h \sum_{x \in V} \sigma_x$, with no continuous degrees of freedom, and whose reference measure is the
counting measure on configurations.
