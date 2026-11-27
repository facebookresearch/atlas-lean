# Term of the expanded half-edge polynomial for a choice

Let $G = (V, E)$ be a finite simple graph and $\beta \in \mathbb{R}$. For a choice $x = (a, \tau)$ of a Boolean $a_v$ for every vertex $v$ and a pair of Booleans $\tau_e = (\tau_e^0, \tau_e^1)$ for every edge $e$ and a point $z$ of the [variables](lee-yang-var.md) of the half-edge polynomial (an anchor variable $z_v$ for each vertex $v$ and a variable $w_{v,e}$ for each pair of a vertex $v$ and an edge $e$), the term of the expanded
[half-edge polynomial](lee-yang-half-edge-product.md) selected by $x$ is

$$\prod_{v \in V} c_v(z, a_v) \prod_{e \in E} c_e(z, \tau_e),$$

the product of the [vertex terms](lee-yang-anchor-choice-factor.md) and the
[edge terms](lee-yang-edge-choice-factor.md) selected by $x$.
