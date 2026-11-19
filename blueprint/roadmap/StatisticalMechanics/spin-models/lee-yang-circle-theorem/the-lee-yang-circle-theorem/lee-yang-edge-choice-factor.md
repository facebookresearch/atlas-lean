# Term of an edge factor selected by two Boolean choices

Let $G = (V, E)$ be a finite simple graph and $\beta \in \mathbb{R}$, let $z$ be a point of the [variables](lee-yang-var.md) of the half-edge polynomial (an anchor variable $z_v$ for each vertex $v$ and a variable $w_{v,e}$ for each pair of a vertex $v$ and an edge $e$), let $e$ be an edge with $u_e, v_e$ the [chosen endpoints](lee-yang-endpoint0.md) of $e$, and let
$(b_0, b_1)$ be a pair of Booleans, one per endpoint. The term of the edge factor of $e$ selected by
$(b_0, b_1)$ is

$$c_e \cdot (w_{u_e, e} \text{ if } b_0, \text{ else } 1) \cdot (w_{v_e, e} \text{ if } b_1, \text{ else } 1),$$

with $c_e = 1$ if $b_0 = b_1$ and $c_e = e^{-2\beta}$ otherwise.
