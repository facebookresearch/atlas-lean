# Ising Hamiltonian on a finite graph

Let $G = (V, E)$ be a finite simple graph and $h \in \mathbb{R}$. The Ising Hamiltonian with unit coupling and external field $h$
is

$$H(s) = -\sum_{\{x, y\} \in E} \sigma_x \sigma_y - h \sum_{x \in V} \sigma_x$$

for spin configurations $s$, with spins $\sigma_x = +1$ if $s(x)$ is true and $\sigma_x = -1$ otherwise.
