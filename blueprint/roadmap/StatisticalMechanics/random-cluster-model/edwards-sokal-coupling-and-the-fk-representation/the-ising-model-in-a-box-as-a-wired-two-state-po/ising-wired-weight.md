# Ising weight of a coloring with plus boundary

Let $G = (V, E)$ be a finite simple graph and $\partial \subseteq V$ a set of boundary vertices and $\beta \in \mathbb{R}$. The plus-boundary Ising weight of a two-state coloring $\sigma : V \to \{0, 1\}$ is

$$w^+_\beta(\sigma) = \exp\Big(\beta \sum_{\{x,y\} \in E} s(\sigma_x)\, s(\sigma_y)\Big)$$

if $\sigma_x = 0$ for every $x \in \partial$, and $w^+_\beta(\sigma) = 0$ otherwise, where $s(0) = 1$ and $s(1) = -1$.
