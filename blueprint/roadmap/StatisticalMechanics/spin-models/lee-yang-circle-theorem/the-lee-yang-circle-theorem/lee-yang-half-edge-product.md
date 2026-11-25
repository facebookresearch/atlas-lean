# Half-edge polynomial of a graph

Let $G = (V, E)$ be a finite simple graph and $\beta \in \mathbb{R}$. The half-edge polynomial of $G$ is the function of the [variables](lee-yang-var.md) of the half-edge polynomial (an anchor variable $z_v$ for each vertex $v$ and a variable $w_{v,e}$ for each pair of a vertex $v$ and an edge $e$)

$$P(z, w) = \prod_{v \in V} (1 + z_v) \prod_{e = \{u, v\} \in E} \bigl(1 + w_{u,e} w_{v,e} + e^{-2\beta}(w_{u,e} + w_{v,e})\bigr).$$
