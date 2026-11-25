# Holley's condition for probabilities with nested wirings, $q \ge 1$

Let $G = (V, E)$ be a finite simple graph, let $C \le C'$ be simple graphs on $V$ ($C$ a subgraph of $C'$), $0 < p < 1$ and $q \ge 1$. For all assignments $a, b$ of open/closed states to the unordered pairs of vertices (loops and non-edges included),

$$\phi^C_{G,p,q}(a)\, \phi^{C'}_{G,p,q}(b) \le \phi^C_{G,p,q}(a \wedge b)\, \phi^{C'}_{G,p,q}(a \vee b),$$

where $\phi^C_{G,p,q}(\omega) = p^{o(\omega)}(1 - p)^{c(\omega)} q^{k_C(\omega)} / Z^C_{G}(p, q)$ is the [random-cluster probability with boundary wiring $C$](bc-prob.md); here $o(\omega)$ and $c(\omega)$ count the open and closed edges of $G$, $k_C(\omega)$ is the [number of clusters under the wiring $C$](num-clusters-bc.md), the number of connected components of the graph on $V$ whose edges are the edges of $G$ open in $\omega$ together with the edges of $C$, and $Z^C_G(p, q)$ is the sum of the numerators over all assignments $\omega$ of open/closed states to the unordered pairs of vertices (loops and non-edges included). Configurations are ordered coordinatewise (closed $<$ open), and $a \wedge b$, $a \vee b$ denote the coordinatewise minimum and maximum.
