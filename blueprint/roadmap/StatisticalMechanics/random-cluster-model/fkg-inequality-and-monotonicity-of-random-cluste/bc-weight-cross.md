# Holley's condition for weights with nested wirings, $q \ge 1$

Let $G = (V, E)$ be a finite simple graph, let $C \le C'$ be simple graphs on $V$ ($C$ a subgraph of $C'$), $0 < p < 1$ and $q \ge 1$. For all assignments $a, b$ of open/closed states to the unordered pairs of vertices (loops and non-edges included),

$$w^C(a)\, w^{C'}(b) \le w^C(a \wedge b)\, w^{C'}(a \vee b),$$

where $w^C(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)}$ is the [weight with boundary wiring $C$](bc-weight.md), $o(\omega)$ and $c(\omega)$ count the open and closed edges of $G$, and $k_C(\omega)$ is the [number of clusters under the wiring $C$](num-clusters-bc.md), the number of connected components of the graph on $V$ whose edges are the edges of $G$ open in $\omega$ together with the edges of $C$. Configurations are ordered coordinatewise (closed $<$ open), and $a \wedge b$, $a \vee b$ denote the coordinatewise minimum and maximum.
